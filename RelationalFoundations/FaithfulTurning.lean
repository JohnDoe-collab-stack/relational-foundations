import RelationalFoundations.FaithfulContinuation
import RelationalFoundations.Cardinalization
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c g

namespace FaithfulContinuation
variable {p : CircularPresentation.{u,v,t,i,c}} {target : p.Node}
variable {positive : History.Positive p.Next p.spine.finalNode target}

theorem positive_occurrence_exact (context : FaithfulContinuation p positive) :
    positive.lastOccurrence = context.exactlyOne.canonicalOccurrence :=
  context.exactlyOne.occurrence_unique positive.lastOccurrence

structure CoupledTurning (context : FaithfulContinuation p positive)
    (regime : ExactRegime.{max u v,g} p.interiorConstruction) where
  turning : TurningWithExit context.generatedStep regime
  originalHistoryExact : History.append p.interiorHistory positive.toHistory = context.generatedStep.history
  originalFormationExact : context.interpretation.formation.toHistory =
    History.append p.interiorHistory positive.toHistory
  originalOccurrenceExact : positive.lastOccurrence = context.exactlyOne.canonicalOccurrence

def coupledTurning (context : FaithfulContinuation p positive)
    (regime : ExactRegime p.interiorConstruction) : context.CoupledTurning regime :=
  ⟨context.generatedStep.verifiedExit regime, context.history_exact,
    context.interpreted_history_exact, context.positive_occurrence_exact⟩

end FaithfulContinuation
end RelationalFoundations
