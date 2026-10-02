import RelationalFoundations.HistoryTransport
set_option genInjectivity false

namespace RelationalFoundations
universe u v

inductive Spine {Node : Type u} (Next : Node → Node → Type v) : Node → Type (max u v)
  | boundary (node : Node) : Spine Next node
  | advance {source target : Node} (witness : Next source target)
      (tail : Spine Next target) : Spine Next source

namespace Spine
variable {Node : Type u} {Next : Node → Node → Type v}

@[reducible] def finalNode {node : Node} : Spine Next node → Node
  | .boundary node => node
  | .advance _ tail => tail.finalNode

inductive Position : {node : Node} → Spine Next node → Type (max u v)
  | here {witness : Next source target} {tail : Spine Next target} :
      Position (.advance witness tail)
  | later {witness : Next source target} {tail : Spine Next target} :
      Position tail → Position (.advance witness tail)

theorem Position.later.inj {source target : Node} {witness : Next source target}
    {tail : Spine Next target} {first second : Position tail}
    (eq : Position.later (witness := witness) first = Position.later second) : first = second := by
  cases eq
  rfl

def located {node : Node} {spine : Spine Next node} :
    Position spine → History.LocatedStep Next
  | .here (witness := witness) => ⟨_, _, witness⟩
  | .later position => located position

@[reducible] def toHistory {node : Node} (spine : Spine Next node) :
    History Next node spine.finalNode :=
  match spine with
  | .boundary _ => .root
  | .advance witness tail => History.append (.extend .root witness) tail.toHistory

def realize {node : Node} {spine : Spine Next node} :
    Position spine → History.Occurrence spine.toHistory
  | .here (witness := witness) (tail := tail) =>
      History.embedLeftOccurrence
        (.last : History.Occurrence (.extend .root witness)) tail.toHistory
  | .later (witness := witness) position =>
      History.embedRightOccurrence (.extend .root witness) (realize position)

def decode {node : Node} (spine : Spine Next node) :
    History.Occurrence spine.toHistory → Position spine :=
  match spine with
  | .boundary _ => fun impossible => nomatch impossible
  | .advance witness tail => fun o =>
      match History.splitAppendOccurrence
        (firstHistory := .extend .root witness) (continuation := tail.toHistory) o with
      | .inl _ => .here
      | .inr new => .later (decode tail new)

theorem decode_realize {node : Node} {spine : Spine Next node}
    (p : Position spine) : decode spine (realize p) = p := by
  induction p with
  | here =>
    rename_i source target witness tail
    change (match History.splitAppendOccurrence
      (firstHistory := .extend .root witness) (continuation := tail.toHistory)
      (History.embedLeftOccurrence (.last : History.Occurrence (.extend .root witness)) tail.toHistory) with
      | .inl _ => Position.here
      | .inr new => Position.later (decode tail new)) = Position.here
    rw [History.split_left]
  | later p ih =>
    rename_i source target witness tail
    change (match History.splitAppendOccurrence
      (firstHistory := .extend .root witness) (continuation := tail.toHistory)
      (History.embedRightOccurrence (.extend .root witness) (realize p)) with
      | .inl _ => Position.here
      | .inr new => Position.later (decode tail new)) = Position.later p
    rw [History.split_right]
    exact congrArg Position.later ih

theorem realize_decode {node : Node} (spine : Spine Next node)
    (o : History.Occurrence spine.toHistory) : realize (decode spine o) = o := by
  induction spine with
  | boundary node => cases o
  | advance witness tail ih =>
    have reconstruction := History.join_split (.extend .root witness) tail.toHistory o
    cases eq : History.splitAppendOccurrence
      (firstHistory := .extend .root witness) (continuation := tail.toHistory) o with
    | inl old =>
      rw [eq] at reconstruction
      cases old with
      | last =>
        change realize (match History.splitAppendOccurrence
          (firstHistory := .extend .root witness) (continuation := tail.toHistory) o with
          | .inl _ => Position.here
          | .inr new => Position.later (decode tail new)) = o
        rw [eq]
        exact reconstruction
      | earlier impossible => cases impossible
    | inr new =>
      rw [eq] at reconstruction
      change realize (match History.splitAppendOccurrence
        (firstHistory := .extend .root witness) (continuation := tail.toHistory) o with
        | .inl _ => Position.here
        | .inr new => Position.later (decode tail new)) = o
      rw [eq]
      change History.embedRightOccurrence (.extend .root witness) (realize (decode tail new)) = o
      rw [ih new]
      exact reconstruction

def positionTransport {node : Node} (spine : Spine Next node) :
    ExactTransport (Position spine) (History.Occurrence spine.toHistory) where
  forward := realize
  backward := decode spine
  forwardBackward := decode_realize
  backwardForward := realize_decode spine

theorem located_realize {node : Node} {spine : Spine Next node}
    (p : Position spine) : (realize p).locatedStep = located p := by
  induction p with
  | here => exact History.locatedStep_embedLeft _ _
  | later p ih => exact (History.locatedStep_embedRight _ _).trans ih

inductive Precedes : {node : Node} → {s : Spine Next node} →
    Position s → Position s → Prop
  | here_later (p : Position tail) : Precedes (.here (witness := k)) (.later p)
  | later_later : Precedes p q → Precedes (.later (witness := k) p) (.later q)

inductive Adjacent : {node : Node} → {s : Spine Next node} →
    Position s → Position s → Prop
  | here_next : Adjacent (.here (witness := k) (tail := .advance j tail)) (.later .here)
  | later_next : Adjacent p q → Adjacent (.later (witness := k) p) (.later q)

theorem Precedes.ne {node : Node} {s : Spine Next node} {p q : Position s}
    (h : Precedes p q) : p ≠ q := by
  induction h with
  | here_later => intro eq; cases eq
  | later_later _ ih => intro eq; exact ih (Position.later.inj eq)

theorem Adjacent.toPrecedes {node : Node} {s : Spine Next node} {p q : Position s}
    (h : Adjacent p q) : Precedes p q := by
  induction h with
  | here_next => exact .here_later .here
  | later_next _ ih => exact .later_later ih

theorem position_trichotomy {node : Node} {s : Spine Next node} (first second : Position s) :
    first = second ∨ Precedes first second ∨ Precedes second first := by
  induction first with
  | here => cases second with
    | here => exact .inl rfl
    | later second => exact .inr (.inl (.here_later second))
  | later first ih => cases second with
    | here => exact .inr (.inr (.here_later first))
    | later second =>
      rcases ih second with eq | before | after
      · exact .inl (congrArg Position.later eq)
      · exact .inr (.inl (.later_later before))
      · exact .inr (.inr (.later_later after))

def positionSumTransport {source target : Node} (witness : Next source target) (tail : Spine Next target) :
    ExactTransport (Position (.advance witness tail)) (Unit ⊕ Position tail) where
  forward := fun p => match p with | .here => .inl () | .later old => .inr old
  backward := fun p => match p with | .inl _ => .here | .inr old => .later old
  forwardBackward := fun p => by cases p <;> rfl
  backwardForward := fun p => by cases p with
    | inl u => cases u; rfl
    | inr old => rfl

end Spine
end RelationalFoundations
