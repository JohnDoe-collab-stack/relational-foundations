import RelationalFoundations.Continuation
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c

/-- Every field is tied to the same positive continuation by an exact agreement. -/
structure BoundaryInterpretation {p : CircularPresentation.{u,v,t,i,c}}
    (s : OneStepContinuation p) where
  occurrence : s.Occurrence
  occurrenceExact : occurrence = s.fresh ()
  realization : s.FinalRealizes .final occurrence
  actualStep : History.LocatedStep p.Next
  actualStepExact : actualStep = occurrence.locatedStep
  formation : Formation p.Next p.start s.target
  formationExact : formation = s.formation
  junction : p.Close p.boundary.terminal p.boundary.initial
  junctionExact : junction = p.junction

namespace BoundaryInterpretation
variable {p : CircularPresentation.{u,v,t,i,c}} {s : OneStepContinuation p}

def ofContinuation (s : OneStepContinuation p) : BoundaryInterpretation s where
  occurrence := s.fresh ()
  occurrenceExact := rfl
  realization := s.freshRealization
  actualStep := (s.fresh ()).locatedStep
  actualStepExact := rfl
  formation := s.formation
  formationExact := rfl
  junction := p.junction
  junctionExact := rfl

theorem formation_history_exact (b : BoundaryInterpretation s) :
    b.formation.toHistory = s.history := by
  rw [b.formationExact]
  exact s.formation_history_exact

theorem actual_source_exact (b : BoundaryInterpretation s) :
    b.actualStep.source = p.spine.finalNode := by
  rw [b.actualStepExact, b.occurrenceExact]
  rfl

theorem actual_target_exact (b : BoundaryInterpretation s) :
    b.actualStep.target = s.target := by
  rw [b.actualStepExact, b.occurrenceExact]
  rfl

theorem provenance_preserved (old : Formation.Record (Formation.deployed p.spine)) :
    (Formation.Record.preserved (witness := s.witness) old).located = old.located := rfl

end BoundaryInterpretation
end RelationalFoundations
