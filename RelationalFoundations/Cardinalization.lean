import RelationalFoundations.Turning
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c
namespace History
variable {State : Type u} {Step : State → State → Type v}

def length {a b : State} : History Step a b → Nat
  | .root => 0
  | .extend previous _ => previous.length + 1

theorem length_append {a b c : State} (h : History Step a b) (k : History Step b c) :
    (append h k).length = h.length + k.length := by
  induction k with
  | root => rfl
  | extend k step ih =>
    change (append h k).length + 1 = h.length + (k.length + 1)
    rw [ih, Nat.add_assoc]

/-- Cardinal indexing uses newest-first order; chronology remains a separate relation. -/
def index {a b : State} {h : History Step a b} : Occurrence h → Fin h.length
  | .last => ⟨0, Nat.zero_lt_succ _⟩
  | .earlier old => (index old).succ

def ofIndex {a b : State} (h : History Step a b) : Fin h.length → Occurrence h :=
  match h with
  | .root => fun impossible => Fin.elim0 impossible
  | .extend previous _ => fun i =>
    match i with
    | ⟨0, _⟩ => .last
    | ⟨Nat.succ n, bound⟩ => .earlier (ofIndex previous ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

theorem ofIndex_index {a b : State} {h : History Step a b} (o : Occurrence h) :
    ofIndex h (index o) = o := by
  induction o with
  | last => rfl
  | earlier o ih =>
    change Occurrence.earlier (ofIndex _ (index o)) = .earlier o
    exact congrArg Occurrence.earlier ih

theorem index_ofIndex {a b : State} (h : History Step a b) (i : Fin h.length) :
    index (ofIndex h i) = i := by
  induction h with
  | root => exact Fin.elim0 i
  | extend previous step ih =>
    cases i with
    | mk n bound =>
      cases n with
      | zero => rfl
      | succ n =>
        change (index (ofIndex previous ⟨n, Nat.lt_of_succ_lt_succ bound⟩)).succ =
          (⟨n, Nat.lt_of_succ_lt_succ bound⟩ : Fin previous.length).succ
        exact congrArg Fin.succ (ih _)

def cardinalTransport {a b : State} (h : History Step a b) : ExactTransport (Occurrence h) (Fin h.length) :=
  ⟨index, ofIndex h, ofIndex_index, index_ofIndex h⟩

end History

namespace CircularPresentation
def interiorCardinalization (p : CircularPresentation.{u,v,t,i,c}) :
    ExactTransport p.InternalRole (Fin p.interiorHistory.length) :=
  p.interiorRealization.transport.compose (History.cardinalTransport p.interiorHistory)
end CircularPresentation

namespace OneStepContinuation
variable {p : CircularPresentation.{u,v,t,i,c}}

theorem construction_different (s : OneStepContinuation p) : s.construction ≠ p.interiorConstruction := by
  intro eq
  have lengthEq := congrArg (fun h : RootedConstruction p.Next p.start => h.history.length) eq
  change p.interiorHistory.length + 1 = p.interiorHistory.length at lengthEq
  exact Nat.ne_of_gt (Nat.lt_succ_self _) lengthEq

def verifiedTurning (s : OneStepContinuation p) : AffirmativeTurning s :=
  affirmativeTurning s s.construction_different

def verifiedExit (s : OneStepContinuation p) (regime : ExactRegime p.interiorConstruction) :
    TurningWithExit s regime := turningWithExit s s.construction_different regime

end OneStepContinuation
end RelationalFoundations
