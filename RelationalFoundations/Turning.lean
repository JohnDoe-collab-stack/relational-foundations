import RelationalFoundations.BoundaryInterpretation
import RelationalFoundations.Regime
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c g

namespace CircularPresentation
def interiorConstruction (p : CircularPresentation.{u,v,t,i,c}) : RootedConstruction p.Next p.start :=
  ⟨p.spine.finalNode, p.interiorHistory⟩
end CircularPresentation

namespace OneStepContinuation
variable {p : CircularPresentation.{u,v,t,i,c}} (s : OneStepContinuation p)

def construction : RootedConstruction p.Next p.start := ⟨s.target, s.history⟩

def strictExtension (different : s.construction ≠ p.interiorConstruction) :
    StrictExtension p.interiorConstruction s.construction where
  continuation := ⟨_, .root, s.witness⟩
  recompose := rfl
  different := different

end OneStepContinuation

structure AffirmativeTurning {p : CircularPresentation.{u,v,t,i,c}}
    (s : OneStepContinuation p) where
  interior : p.InteriorDelimitation
  extension : StrictExtension p.interiorConstruction s.construction
  interpretation : BoundaryInterpretation s
  residual : s.label (s.fresh ()) = .inr BoundaryFinalRole.final

def affirmativeTurning {p : CircularPresentation.{u,v,t,i,c}} (s : OneStepContinuation p)
    (different : s.construction ≠ p.interiorConstruction) : AffirmativeTurning s :=
  ⟨p.delimitInterior, s.strictExtension different, .ofContinuation s, s.fresh_is_residual ()⟩

structure TurningWithExit {p : CircularPresentation.{u,v,t,i,c}} (s : OneStepContinuation p)
    (regime : ExactRegime.{max u v,g} p.interiorConstruction) where
  turning : AffirmativeTurning s
  exits : regime.Admission s.construction → False

def turningWithExit {p : CircularPresentation.{u,v,t,i,c}} (s : OneStepContinuation p)
    (different : s.construction ≠ p.interiorConstruction)
    (regime : ExactRegime p.interiorConstruction) : TurningWithExit s regime :=
  ⟨affirmativeTurning s different, regime.rejects different⟩

end RelationalFoundations
