import RelationalFoundations.HistoricalSupport
import RelationalFoundations.Cardinalization
set_option genInjectivity false

/-!
# A complete constructive family of local producers

This family has four rules: empty output, primitive emission, composition, and
reuse. Every rule's prerequisites, termination decrease and semantic production
are implemented here. For arbitrary typed histories and token readouts, next
demands are generated from the previous produced output, and their realization
is proved to be the complete newest-first token trace.

This is a semantic family for the generic support construction. It is not an
implementation of a type-theoretic universe hierarchy or of an external kernel.
-/

namespace RelationalFoundations.WordSupport
open DemandClosure HistoricalSupport
universe q u v

inductive Request (Token : Type q) where
  | empty
  | emit (token : Token)
  | join (left right : Request Token)
  | reuse (previous : Request Token)

variable {Token : Type q}

def requires : Request Token → List (Request Token)
  | .empty => []
  | .emit _ => []
  | .join left right => [left, right]
  | .reuse previous => [previous]

def rank : Request Token → Nat
  | .empty => 0
  | .emit _ => 0
  | .join left right => rank left + rank right + 1
  | .reuse previous => rank previous + 1

theorem decreases (request child : Request Token) (member : child ∈ requires request) :
    rank child < rank request := by
  cases request with
  | empty => cases member
  | emit _ => cases member
  | join left right =>
      cases member with
      | head => exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
      | tail _ member =>
          cases member with
          | head => exact Nat.lt_succ_of_le (Nat.le_add_left _ _)
          | tail _ member => cases member
  | reuse previous =>
      cases member with
      | head => exact Nat.lt_succ_self _
      | tail _ member => cases member

def system (Token : Type q) : RankedSystem where
  Request := Request Token
  requires := requires
  rank := rank
  decreases := decreases

/-- Independently specified meaning: composition and reuse preserve token order. -/
def meaning : Request Token → List Token
  | .empty => []
  | .emit token => [token]
  | .join left right => meaning left ++ meaning right
  | .reuse previous => meaning previous

def produce : (request : Request Token) → Values (fun _ : Request Token => List Token) (requires request) → List Token
  | .empty, .nil => []
  | .emit token, .nil => [token]
  | .join _ _, .cons left (.cons right .nil) => left ++ right
  | .reuse _, .cons previous .nil => previous

def producer (Token : Type q) : LocalProducer.{q,0} (system Token).requires where
  Value := fun _ => List Token
  produce := produce

def soundness (Token : Type q) : (producer Token).Soundness where
  Valid := fun request value => value = meaning request
  preserves := by
    intro request inputs valid
    cases request with
    | empty => cases inputs; rfl
    | emit _ => cases inputs; rfl
    | join left right =>
        cases inputs with
        | cons first rest =>
            cases rest with
            | cons second rest =>
                cases rest
                exact (congrArg (fun value : List Token => List.append value second) valid.1).trans
                  (congrArg (List.append (meaning left)) valid.2.1)
    | reuse previous =>
        cases inputs with
        | cons first rest =>
            cases rest
            exact valid.1

theorem build_realizes_meaning (request : Request Token) :
    (producer Token).realize ((system Token).build request) = meaning request :=
  (producer Token).realize_valid (soundness Token) _

def fromOutput : List Token → Request Token
  | [] => .empty
  | token :: rest => .join (.emit token) (fromOutput rest)

theorem meaning_fromOutput (output : List Token) : meaning (fromOutput output) = output := by
  induction output with
  | nil => rfl
  | cons token rest ih => exact congrArg (List.cons token) ih

variable {State : Type u} {Step : State → State → Type v}

def previousOutput {source : State} : {target : State} → (history : History Step source target) →
    Context (producer Token) history → List Token
  | _, .root, _ => []
  | _, .extend _ _, context =>
      match context.valuesAt .last with
      | [] => []
      | value :: _ => value.2

/-- The next request incorporates the actual previously produced value. -/
def policy (read : {source target : State} → Step source target → Token) :
    Policy (system Token) (producer Token) Step where
  initial := fun _ => [.empty]
  next := fun history step context =>
    [.join (.emit (read step)) (.reuse (fromOutput (previousOutput history context)))]

def trace (read : {source target : State} → Step source target → Token) {source : State} :
    {target : State} → History Step source target → List Token
  | _, .root => []
  | _, .extend previous step => read step :: trace read previous

/-- The terminal output is derived for every history, not supplied by a bridge. -/
theorem output_eq_trace (read : {source target : State} → Step source target → Token)
    {source target : State} (history : History Step source target) :
    previousOutput history (((policy read).build history).context (producer Token)) = trace read history := by
  induction history with
  | root => rfl
  | extend previous step ih =>
      change (producer Token).realize ((system Token).build
        (.join (.emit (read step)) (.reuse (fromOutput
          (previousOutput previous (((policy read).build previous).context (producer Token))))))) =
        read step :: trace read previous
      rw [build_realizes_meaning]
      change read step :: meaning (fromOutput
        (previousOutput previous (((policy read).build previous).context (producer Token)))) =
        read step :: trace read previous
      rw [meaning_fromOutput, ih]

/-- Each history step constitutes a nonempty resource tree; cardinality is read afterward. -/
theorem support_size_lower_bound (read : {source target : State} → Step source target → Token)
    {source target : State} (history : History Step source target) :
    history.length + 1 ≤ ((policy read).build history).size := by
  induction history with
  | root => exact Nat.le_refl 1
  | extend previous step ih =>
      change (previous.length + 1) + 1 ≤ ((policy read).build previous).size +
        ((system Token).build (.join (.emit (read step)) (.reuse (fromOutput
          (previousOutput previous (((policy read).build previous).context (producer Token))))))).size
      exact Nat.add_le_add ih (Nat.succ_le_of_lt (Tree.size_positive _))

end RelationalFoundations.WordSupport
