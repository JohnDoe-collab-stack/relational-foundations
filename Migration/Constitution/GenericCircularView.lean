import Constitution.ConstitutedHistory
import RelationalFoundations.CircularSignature
import RelationalFoundations.Generation

set_option genInjectivity false
namespace RelationalFoundations.PerimetralView

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

/-- The generic equipped quantity retains the actual rich primitive node carriers. -/
def circularQuantity (p : StrongPerimetralTurning.CircularPresentation) :=
  CircularSignature.circularQuantity (positiveView p)

def richFormation {p : StrongPerimetralTurning.CircularPresentation}
    (history : StrongPerimetralTurning.RootedGeneratedHistory p) :
    Formation (@StrongPerimetralTurning.GeneratedStep p)
      (StrongPerimetralTurning.initialPositive p) history.endpoint :=
  Formation.fromHistory history.history

theorem richFormation_history_exact {p : StrongPerimetralTurning.CircularPresentation}
    (history : StrongPerimetralTurning.RootedGeneratedHistory p) :
    (richFormation history).toHistory = history.history := Formation.toHistory_fromHistory _

def richRecords {p : StrongPerimetralTurning.CircularPresentation}
    (history : StrongPerimetralTurning.RootedGeneratedHistory p) :
    ExactTransport (Formation.Record (richFormation history)) (History.Occurrence history.history) :=
  (Formation.recordTransport (richFormation history)).compose
    (ExactTransport.ofEquality (congrArg History.Occurrence (richFormation_history_exact history)))

end RelationalFoundations.PerimetralView