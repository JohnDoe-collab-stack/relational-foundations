import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalFoundationBridge

/-!
# Causal constitutive execution, without accounting or diagnostic projections

This module owns the semantic carrier threaded by the repaired architecture.
Its states retain the constituted history, the operational SAT state, the
assignment produced by execution, and the material decision provenance.  A
stage contains the actual opening relation, its total action on a continuation,
the separate acceptance-preservation witness, and the exact next state.

There are deliberately no work counters, widths, address spaces, programs, or
representation projections here.  Instrumented executions may be erased into
this carrier in a later module; roles are indexed only by this carrier.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open StrongPerimetralTurning
/--
One causal stage.  The relational transformation and its execution output are
data.  Preservation is recorded separately and is not used to identify the two
opening occurrences or to declare the left one impossible.
-/
structure CausalConstitutiveStageExecution
    (source : CausalConstitutiveState) where
  selected : Var
  fresh :
    StructuralDecisionsAvoid selected source.operationalState.context.decisions
  relation :
    GeneratedStructuralFlipAtRelation selected
      (causalOpeningLeft source selected fresh)
      (causalOpeningRight source selected fresh)
  sourceContinuation :
    GeneratedStructuralBranchContinuation
      (causalOpeningLeft source selected fresh)
  sourceAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningLeft source selected fresh)
      sourceContinuation
  outputContinuation :
    GeneratedStructuralBranchContinuation
      (causalOpeningRight source selected fresh)
  outputExact :
    outputContinuation = relation.mapContinuation sourceContinuation
  outputAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source selected fresh)
      outputContinuation
  next : CausalConstitutiveState
  constitutiveGeneration :
    GeneratedStep
      source.constitutedHistory.endpoint
      next.constitutedHistory.endpoint
  nextAssignmentExact : next.assignment = outputContinuation.1
  nextSearchSeedExact : next.searchSeed = selected
  nextDecisionsExact :
    next.decisions =
      { var := selected, value := true } :: source.decisions
  nextProvenanceExact :
    next.provenance = selected :: source.provenance

/-- Preservation is recovered from the relation that actually produced output. -/
theorem CausalConstitutiveStageExecution.outputAccepted_from_relation
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source stage.selected stage.fresh)
      stage.outputContinuation := by
  rw [stage.outputExact]
  exact stage.relation.mapContinuation_accept
    stage.sourceContinuation stage.sourceAccepted

/--
The authoritative causal history.  Its dependent tail starts at the exact
state produced by its head; an unrelated state cannot be substituted.
-/
inductive CausalConstitutiveExecutionHistory :
    (count : Nat) → CausalConstitutiveState → Type 2 where
  | nil (state : CausalConstitutiveState) :
      CausalConstitutiveExecutionHistory 0 state
  | step {count : Nat} {state : CausalConstitutiveState}
      (head : CausalConstitutiveStageExecution state)
      (tail : CausalConstitutiveExecutionHistory count head.next) :
      CausalConstitutiveExecutionHistory (count + 1) state

/-- The number of stages is an aval readout of the dependent history. -/
def CausalConstitutiveExecutionHistory.stageCount :
    {count : Nat} → {state : CausalConstitutiveState} →
      CausalConstitutiveExecutionHistory count state → Nat
  | _, _, .nil _ => 0
  | _, _, .step _ tail => tail.stageCount + 1

theorem CausalConstitutiveExecutionHistory.stageCount_exact
    {count : Nat} {state : CausalConstitutiveState}
    (history : CausalConstitutiveExecutionHistory count state) :
    history.stageCount = count := by
  induction history with
  | nil => rfl
  | step _ tail inductionHypothesis =>
      unfold stageCount
      exact congrArg (fun value => value + 1) inductionHypothesis

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveStageExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveStageExecution.outputAccepted_from_relation
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecutionHistory.stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecutionHistory.stageCount_exact
/- AXIOM_AUDIT_END -/
