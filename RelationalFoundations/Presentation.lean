import RelationalFoundations.Spine
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c

set_option linter.checkUnivs false in
structure SuccessivePresentation where
  Node : Type u
  Next : Node → Node → Type v
  start : Node
  spine : Spine Next start

structure ClosingBoundary (Terminal : Type t) (Initial : Type i)
    (Close : Terminal → Initial → Type c) where
  terminal : Terminal
  initial : Initial

inductive BoundaryFinalRole {Terminal : Type t} {Initial : Type i}
    {Close : Terminal → Initial → Type c}
    (boundary : ClosingBoundary Terminal Initial Close) : Type
  | final

namespace BoundaryFinalRole
variable {Terminal : Type t} {Initial : Type i} {Close : Terminal → Initial → Type c}
variable {boundary : ClosingBoundary Terminal Initial Close}

theorem contracts (role : BoundaryFinalRole boundary) : role = .final := by
  cases role
  rfl

def unitTransport (boundary : ClosingBoundary Terminal Initial Close) :
    ExactTransport (BoundaryFinalRole boundary) Unit where
  forward := fun _ => ()
  backward := fun _ => .final
  forwardBackward := fun r => (contracts r).symm
  backwardForward := fun u => by cases u; rfl

end BoundaryFinalRole

set_option linter.checkUnivs false in
structure CircularPresentation extends SuccessivePresentation.{u,v} where
  Terminal : Type t
  Initial : Type i
  terminalInterface : Node → Terminal
  initialInterface : Node → Initial
  Close : Terminal → Initial → Type c
  junction : Close (terminalInterface spine.finalNode) (initialInterface start)

namespace CircularPresentation

def boundary (p : CircularPresentation.{u,v,t,i,c}) :
    ClosingBoundary p.Terminal p.Initial p.Close :=
  ⟨p.terminalInterface p.spine.finalNode, p.initialInterface p.start⟩

abbrev InternalRole (p : CircularPresentation.{u,v,t,i,c}) := Spine.Position p.spine
abbrev FinalRole (p : CircularPresentation.{u,v,t,i,c}) := BoundaryFinalRole p.boundary
abbrev FullRole (p : CircularPresentation.{u,v,t,i,c}) := p.InternalRole ⊕ p.FinalRole
abbrev interiorHistory (p : CircularPresentation.{u,v,t,i,c}) := p.spine.toHistory
abbrev InteriorOccurrence (p : CircularPresentation.{u,v,t,i,c}) := History.Occurrence p.interiorHistory

def classify (p : CircularPresentation.{u,v,t,i,c}) (o : p.InteriorOccurrence) : p.FullRole :=
  .inl (Spine.decode p.spine o)

theorem classify_not_final (p : CircularPresentation.{u,v,t,i,c}) (o : p.InteriorOccurrence) :
    p.classify o ≠ .inr BoundaryFinalRole.final := by
  intro eq
  cases eq

theorem fullRole_cases (p : CircularPresentation.{u,v,t,i,c}) (r : p.FullRole) :
    (∃ internal, r = .inl internal) ∨ r = .inr BoundaryFinalRole.final := by
  cases r with
  | inl internal => exact .inl ⟨internal, rfl⟩
  | inr f => exact .inr (congrArg Sum.inr (BoundaryFinalRole.contracts f))

end CircularPresentation
end RelationalFoundations
