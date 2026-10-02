import StrongPerimetralTurning
import RelationalFoundations

namespace RelationalFoundations.Comparison

universe e i k d p u v

@[reducible] def translateSpine
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} :
    StrongPerimetralTurning.PerimeterSpine K node → Spine (fun a b : StrongPerimetralTurning.LocalNode E I K D P => K a.implicit b.explicit) node
  | .boundary node => .boundary node
  | .advance witness tail => .advance witness (translateSpine tail)

theorem finalNode_exact
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} (s : StrongPerimetralTurning.PerimeterSpine K node) :
    (translateSpine s).finalNode = s.finalNode := by
  induction s with
  | boundary node => rfl
  | advance witness tail ih => exact ih

def positionForward
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} {s : StrongPerimetralTurning.PerimeterSpine K node} :
    StrongPerimetralTurning.NonClosingPosition s → Spine.Position (translateSpine s)
  | .here => .here
  | .later old => .later (positionForward old)

def positionBackward
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} (s : StrongPerimetralTurning.PerimeterSpine K node) :
    Spine.Position (translateSpine s) → StrongPerimetralTurning.NonClosingPosition s :=
  match s with
  | .boundary _ => fun impossible => nomatch impossible
  | .advance _ tail => fun position => match position with
    | .here => .here
    | .later old => .later (positionBackward tail old)

theorem position_forwardBackward
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} {s : StrongPerimetralTurning.PerimeterSpine K node}
    (position : StrongPerimetralTurning.NonClosingPosition s) : positionBackward s (positionForward position) = position := by
  induction position with
  | here => rfl
  | later position ih => exact congrArg StrongPerimetralTurning.NonClosingPosition.later ih

theorem position_backwardForward
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} (s : StrongPerimetralTurning.PerimeterSpine K node)
    (position : Spine.Position (translateSpine s)) : positionForward (positionBackward s position) = position := by
  induction s with
  | boundary node => cases position
  | advance witness tail ih => cases position with
    | here => rfl
    | later old => exact congrArg Spine.Position.later (ih old)

def positionTransport
    {E : Type e} {I : Type i} {K : I → E → Type k} {D : Type d} {P : D → Type p}
    {node : StrongPerimetralTurning.LocalNode E I K D P} (s : StrongPerimetralTurning.PerimeterSpine K node) :
    ExactTransport (StrongPerimetralTurning.NonClosingPosition s) (Spine.Position (translateSpine s)) :=
  ⟨positionForward, positionBackward s, position_forwardBackward, position_backwardForward s⟩

def positiveView (p : StrongPerimetralTurning.CircularPresentation) : CircularPresentation where
  Node := StrongPerimetralTurning.LocalNode p.Explicit p.Implicit p.Compatible p.Difference p.Provenance
  Next := fun a b => p.Compatible a.implicit b.explicit
  start := p.initialNode
  spine := translateSpine p.perimeter
  Terminal := p.Implicit
  Initial := p.Explicit
  terminalInterface := fun node => node.implicit
  initialInterface := fun node => node.explicit
  Close := p.Compatible
  junction := by
    change p.Compatible (translateSpine p.perimeter).finalNode.implicit p.initialNode.explicit
    rw [finalNode_exact]
    exact p.finalJunction

def finalRoleTransport (p : StrongPerimetralTurning.CircularPresentation) :
    ExactTransport (StrongPerimetralTurning.FinalRequirement p) (positiveView p).FinalRole where
  forward := fun _ => .final
  backward := fun _ => .distinguished
  forwardBackward := fun r => by cases r; rfl
  backwardForward := fun r => by cases r; rfl

def historyForward {State : Type u} {Step : State → State → Type v} {a b : State} :
    StrongPerimetralTurning.History Step a b → History Step a b
  | .root => .root
  | .extend prior step => .extend (historyForward prior) step

def historyBackward {State : Type u} {Step : State → State → Type v} {a b : State} :
    History Step a b → StrongPerimetralTurning.History Step a b
  | .root => .root
  | .extend prior step => .extend (historyBackward prior) step

theorem history_forwardBackward {State : Type u} {Step : State → State → Type v}
    {a b : State} (h : StrongPerimetralTurning.History Step a b) : historyBackward (historyForward h) = h := by
  induction h with
  | root => rfl
  | extend prior step ih => exact congrArg (fun k => StrongPerimetralTurning.History.extend k step) ih

theorem history_backwardForward {State : Type u} {Step : State → State → Type v}
    {a b : State} (h : History Step a b) : historyForward (historyBackward h) = h := by
  induction h with
  | root => rfl
  | extend prior step ih => exact congrArg (fun k => History.extend k step) ih

def occurrenceForward {State : Type u} {Step : State → State → Type v}
    {a b : State} {h : StrongPerimetralTurning.History Step a b} :
    StrongPerimetralTurning.History.Occurrence h → History.Occurrence (historyForward h)
  | .last => .last
  | .earlier old => .earlier (occurrenceForward old)

def occurrenceBackward {State : Type u} {Step : State → State → Type v}
    {a b : State} (h : StrongPerimetralTurning.History Step a b) :
    History.Occurrence (historyForward h) → StrongPerimetralTurning.History.Occurrence h :=
  match h with
  | .root => fun impossible => nomatch impossible
  | .extend prior _ => fun o => match o with
    | .last => .last
    | .earlier old => .earlier (occurrenceBackward prior old)

theorem occurrence_forwardBackward {State : Type u} {Step : State → State → Type v}
    {a b : State} {h : StrongPerimetralTurning.History Step a b} (o : StrongPerimetralTurning.History.Occurrence h) :
    occurrenceBackward h (occurrenceForward o) = o := by
  induction o with
  | last => rfl
  | earlier o ih => exact congrArg StrongPerimetralTurning.History.Occurrence.earlier ih

theorem occurrence_backwardForward {State : Type u} {Step : State → State → Type v}
    {a b : State} (h : StrongPerimetralTurning.History Step a b) (o : History.Occurrence (historyForward h)) :
    occurrenceForward (occurrenceBackward h o) = o := by
  induction h with
  | root => cases o
  | extend prior step ih => cases o with
    | last => rfl
    | earlier old => exact congrArg History.Occurrence.earlier (ih old)

def occurrenceTransport {State : Type u} {Step : State → State → Type v}
    {a b : State} (h : StrongPerimetralTurning.History Step a b) :
    ExactTransport (StrongPerimetralTurning.History.Occurrence h) (History.Occurrence (historyForward h)) :=
  ⟨occurrenceForward, occurrenceBackward h, occurrence_forwardBackward, occurrence_backwardForward h⟩

def locatedForward {State : Type u} {Step : State → State → Type v}
    (step : StrongPerimetralTurning.History.LocatedStep Step) : History.LocatedStep Step :=
  ⟨step.source, step.target, step.step⟩

theorem actual_step_exact {State : Type u} {Step : State → State → Type v}
    {a b : State} {h : StrongPerimetralTurning.History Step a b} (o : StrongPerimetralTurning.History.Occurrence h) :
    (occurrenceForward o).locatedStep = locatedForward o.locatedStep := by
  induction o with
  | last => rfl
  | earlier o ih => exact ih

def oldExactTransport {A : Type u} {B : Type v} (t : _root_.ExactTypeTransport A B) : ExactTransport A B :=
  ⟨t.forward, t.backward, t.forwardBackward, t.backwardForward⟩

def canonicalOccurrenceTransport (p : StrongPerimetralTurning.CircularPresentation) :
    ExactTransport (positiveView p).InternalRole
      (History.Occurrence (historyForward (StrongPerimetralTurning.perimeterHistory p))) :=
  ((positionTransport p.perimeter).reverse.compose
    { forward := StrongPerimetralTurning.requirementToOccurrence p
      backward := StrongPerimetralTurning.occurrenceToRequirement p
      forwardBackward := StrongPerimetralTurning.requirementToOccurrence_toRequirement p
      backwardForward := StrongPerimetralTurning.occurrenceToRequirement_toOccurrence p }).compose
        (occurrenceTransport (StrongPerimetralTurning.perimeterHistory p))

def canonicalRealizes (p : StrongPerimetralTurning.CircularPresentation)
    (role : (positiveView p).InternalRole)
    (o : History.Occurrence (historyForward (StrongPerimetralTurning.perimeterHistory p))) : Type _ :=
  StrongPerimetralTurning.RequirementOccurrenceAgreement p
    (StrongPerimetralTurning.perimeterDeployment p)
    (positionBackward p.perimeter role)
    (occurrenceBackward (StrongPerimetralTurning.perimeterHistory p) o)

def canonicalRealization (p : StrongPerimetralTurning.CircularPresentation) :
    ExactRealization (positiveView p).InternalRole
      (History.Occurrence (historyForward (StrongPerimetralTurning.perimeterHistory p)))
      (canonicalRealizes p) where
  transport := canonicalOccurrenceTransport p
  agreement := by
    intro role
    change StrongPerimetralTurning.RequirementOccurrenceAgreement p
      (StrongPerimetralTurning.perimeterDeployment p) (positionBackward p.perimeter role)
      (occurrenceBackward (StrongPerimetralTurning.perimeterHistory p)
        (occurrenceForward (StrongPerimetralTurning.requirementToOccurrence p
          (positionBackward p.perimeter role))))
    rw [occurrence_forwardBackward]
    exact StrongPerimetralTurning.canonicalRequirementAgreement p _

/- AXIOM_AUDIT_BEGIN -/
#print axioms translateSpine
#print axioms finalNode_exact
#print axioms positionTransport
#print axioms positiveView
#print axioms finalRoleTransport
#print axioms history_forwardBackward
#print axioms history_backwardForward
#print axioms occurrenceTransport
#print axioms actual_step_exact
#print axioms canonicalOccurrenceTransport
#print axioms canonicalRealization
/- AXIOM_AUDIT_END -/

end RelationalFoundations.Comparison
