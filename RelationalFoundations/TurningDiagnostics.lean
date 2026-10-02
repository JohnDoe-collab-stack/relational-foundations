import RelationalFoundations.FaithfulTurning
import RelationalFoundations.Diagnostics
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c g a b

def ExactRegime.diagnosticClassification {Carrier : Type u} {canonical : Carrier}
    (regime : ExactRegime.{u,g} canonical) : Diagnostics.ExactRegimeClassification canonical regime.Admission :=
  ⟨fun admission => regime.classify _ admission, fun equality => regime.complete _ equality⟩

def InterpretedContinuation (p : CircularPresentation.{u,v,t,i,c})
    (candidate : RootedConstruction p.Next p.start) :=
  Σ continuation : OneStepContinuation p,
    PLift (candidate = continuation.construction) × BoundaryInterpretation continuation

def TurningWithExit.diagnostic {p : CircularPresentation.{u,v,t,i,c}} {continuation : OneStepContinuation p}
    {regime : ExactRegime.{max u v,g} p.interiorConstruction}
    (turning : TurningWithExit continuation regime) :
    Diagnostics.RegimeExit (InterpretedContinuation p) regime.Admission :=
  ⟨continuation.construction, ⟨continuation, ⟨rfl⟩, turning.turning.interpretation⟩, turning.exits⟩

def TurningWithExit.uniformDiagnostic {p : CircularPresentation.{u,v,t,i,c}}
    {continuation : OneStepContinuation p} {regime : ExactRegime.{max u v,g} p.interiorConstruction}
    (turning : TurningWithExit continuation regime) (Implementation : Type a)
    (Faithful : Implementation → RootedConstruction p.Next p.start → Type b)
    (interpret : (implementation : Implementation) → InterpretedContinuation p continuation.construction →
      Faithful implementation continuation.construction) :
    Diagnostics.UniformRegimeExit Implementation Faithful regime.Admission :=
  ⟨continuation.construction, fun implementation => interpret implementation turning.diagnostic.faithful, turning.exits⟩

theorem TurningWithExit.uniform_candidate_exact {p : CircularPresentation.{u,v,t,i,c}}
    {continuation : OneStepContinuation p} {regime : ExactRegime.{max u v,g} p.interiorConstruction}
    (turning : TurningWithExit continuation regime) (Implementation : Type a)
    (Faithful : Implementation → RootedConstruction p.Next p.start → Type b)
    (interpret : (implementation : Implementation) → InterpretedContinuation p continuation.construction →
      Faithful implementation continuation.construction) (implementation : Implementation) :
    ((turning.uniformDiagnostic Implementation Faithful interpret).atImplementation implementation).candidate =
      turning.diagnostic.candidate := rfl
end RelationalFoundations
