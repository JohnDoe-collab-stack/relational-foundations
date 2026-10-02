import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecution

/-!
# Exact realization of the causal execution by the public instrumented run

This exact realization erases counters and diagnostic material from the
already executed public feedback history.  It never invokes a stage builder or
reruns discovery.  Every causal stage is projected from the corresponding
instrumented stage, and the dependent tail starts at the projected state that
the same stage actually produced.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open StrongPerimetralTurning

/-- Erase instrumentation while retaining the constituted and operational data. -/
def causalStateOfThreadedState
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    CausalConstitutiveState :=
  { constitutedHistory := (constructStage depth).history
    rootFormula :=
      distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex
    operationalState := (constructStage (depth + 1)).operationalRoot
    assignment := assignment.assignment
    searchSeed := state.searchSeed
    decisions := state.decisions
    provenance := state.provenance
    provenanceExact := state.provenanceExact }

/-- The generated step stored by the threaded source reaches the projected next history. -/
def threadedGenerationToProjectedNext
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    GeneratedStep
      (causalStateOfThreadedState state).constitutedHistory.endpoint
      (constructStage (depth + 1)).history.endpoint := by
  change GeneratedStep
    (constructStage depth).history.endpoint
    (constructStage (depth + 1)).history.endpoint
  rw [← state.generation.targetExact]
  exact state.generation.generated

/-- One projected causal stage, built exclusively from one executed stage. -/
def causalStageOfThreadedStage
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    CausalConstitutiveStageExecution (causalStateOfThreadedState state) :=
  { selected := stage.discovery.var
    fresh := stage.discovery.fresh
    relation := stage.discovery.relation
    sourceContinuation := stage.sourceContinuation
    sourceAccepted := stage.sourceAccepted
    outputContinuation := stage.application.output
    outputExact := by
      rw [stage.application.outputExact, executedDiscoverySchedule_code]
      rfl
    outputAccepted := stage.outputAccepted
    next := causalStateOfThreadedState run.nextRun.next
    constitutiveGeneration := threadedGenerationToProjectedNext state
    nextAssignmentExact := stage.nextAssignmentExact
    nextSearchSeedExact := by
      change run.nextRun.next.searchSeed = stage.discovery.var
      rw [run.nextRun.searchSeedFromProducedState,
        executedProducedSearchSeed_eq_scheduleEntry]
      exact congrArg (fun schedule => schedule.entry.var) stage.scheduleExact
    nextDecisionsExact := by
      change run.nextRun.next.decisions =
        { var := stage.discovery.var, value := true } :: state.decisions
      rw [run.nextRun.decisionsFromExecution]
      have selectedExact :
          stage.discovery.var = stageSelectedVar (depth + 1) := by
        exact Eq.trans
          (congrArg (fun schedule => schedule.entry.var) stage.scheduleExact).symm
          (sequentialStage_selected_exact stage)
      rw [selectedExact]
    nextProvenanceExact := by
      change run.nextRun.next.provenance =
        stage.discovery.var :: state.provenance
      rw [run.nextRun.provenanceFromExecution]
      have selectedExact :
          stage.discovery.var = stageSelectedVar (depth + 1) := by
        exact Eq.trans
          (congrArg (fun schedule => schedule.entry.var) stage.scheduleExact).symm
          (sequentialStage_selected_exact stage)
      rw [selectedExact] }

/-- Structural erasure of the authoritative instrumented history. -/
def causalHistoryOfInstrumentedHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (history : ConstitutiveExecutionHistory (count := count) state) →
      CausalConstitutiveExecutionHistory count
        (causalStateOfThreadedState state)
  | _, _, _, _, .nil state =>
      CausalConstitutiveExecutionHistory.nil (causalStateOfThreadedState state)
  | _, _, _, _, .step _ headRun tailRun =>
      CausalConstitutiveExecutionHistory.step
        (causalStageOfThreadedStage headRun)
        (causalHistoryOfInstrumentedHistory tailRun)

/--
Witness that a causal run is the projection of one particular instrumented
history.  The constructor stores no alternative execution.
-/
structure InstrumentedExecutionRealization
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (instrumented : ConstitutiveExecutionHistory (count := count) state) where
  causalRun : CausalConstitutiveExecutionHistory count
    (causalStateOfThreadedState state)
  causalRunExact : causalRun = causalHistoryOfInstrumentedHistory instrumented

/-- Canonical realization by erasure, with no computation rerun. -/
def realizeInstrumentedExecution
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (instrumented : ConstitutiveExecutionHistory (count := count) state) :
    InstrumentedExecutionRealization instrumented :=
  { causalRun := causalHistoryOfInstrumentedHistory instrumented
    causalRunExact := rfl }

/-- Realization of the exact feedback history stored by the public run. -/
def publicInstrumentedExecutionRealization (input : Nat) :=
  realizeInstrumentedExecution
    (executeConstitutiveResolution input).constitutiveFeedbackHistory

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalStateOfThreadedState
#print axioms ConstitutiveSearch.EndogenousDecomposition.threadedGenerationToProjectedNext
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalStageOfThreadedStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalHistoryOfInstrumentedHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeInstrumentedExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicInstrumentedExecutionRealization
/- AXIOM_AUDIT_END -/
