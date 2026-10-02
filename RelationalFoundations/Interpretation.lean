import RelationalFoundations.History
set_option genInjectivity false

namespace RelationalFoundations
universe u v a b

set_option linter.checkUnivs false in
structure HistoryInterpretation {Source : Type u} (SourceStep : Source → Source → Type v) where
  ConcreteState : Type a
  ConcreteStep : ConcreteState → ConcreteState → Type b
  stateAt : Source → ConcreteState
  stepAt : {source target : Source} → SourceStep source target → ConcreteStep (stateAt source) (stateAt target)

namespace HistoryInterpretation
variable {Source : Type u} {SourceStep : Source → Source → Type v}
variable (algebra : HistoryInterpretation.{u,v,a,b} SourceStep)

@[reducible] def map {source target : Source} : History SourceStep source target →
    History algebra.ConcreteStep (algebra.stateAt source) (algebra.stateAt target)
  | .root => .root
  | .extend prior step => .extend (map prior) (algebra.stepAt step)

def occurrenceForward {source target : Source} {h : History SourceStep source target} :
    History.Occurrence h → History.Occurrence (algebra.map h)
  | .last => .last
  | .earlier old => .earlier (occurrenceForward old)

def occurrenceBackward {source target : Source} (h : History SourceStep source target) :
    History.Occurrence (algebra.map h) → History.Occurrence h :=
  match h with
  | .root => fun impossible => nomatch impossible
  | .extend prior _ => fun o =>
    match o with
    | .last => .last
    | .earlier old => .earlier (occurrenceBackward prior old)

theorem occurrence_forwardBackward {source target : Source} {h : History SourceStep source target}
    (o : History.Occurrence h) : algebra.occurrenceBackward h (algebra.occurrenceForward o) = o := by
  induction o with
  | last => rfl
  | earlier o ih => exact congrArg History.Occurrence.earlier ih

theorem occurrence_backwardForward {source target : Source} (h : History SourceStep source target)
    (o : History.Occurrence (algebra.map h)) : algebra.occurrenceForward (algebra.occurrenceBackward h o) = o := by
  induction h with
  | root => cases o
  | extend prior step ih =>
    cases o with
    | last => rfl
    | earlier old => exact congrArg History.Occurrence.earlier (ih old)

def occurrenceTransport {source target : Source} (h : History SourceStep source target) :
    ExactTransport (History.Occurrence h) (History.Occurrence (algebra.map h)) :=
  ⟨algebra.occurrenceForward, algebra.occurrenceBackward h,
    algebra.occurrence_forwardBackward, algebra.occurrence_backwardForward h⟩

def located (step : History.LocatedStep SourceStep) : History.LocatedStep algebra.ConcreteStep :=
  ⟨algebra.stateAt step.source, algebra.stateAt step.target, algebra.stepAt step.step⟩

theorem located_exact {source target : Source} {h : History SourceStep source target}
    (o : History.Occurrence h) : (algebra.occurrenceForward o).locatedStep = algebra.located o.locatedStep := by
  induction o with
  | last => rfl
  | earlier o ih => exact ih

end HistoryInterpretation

end RelationalFoundations
