import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedLocalSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GenericConcreteRefinement
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.IntegratedProjection
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredDiscoveryBounds
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredGeneration
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAssignmentBounds
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFullStep
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveRoleCycle
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback

set_option linter.unusedVariables false

/-!
# Integrated concrete `endogenous operational decomposition` resolution run

This module packages the construction proved by the isolated integration
layer.  Its scope is deliberately exact: it establishes a nonempty unbounded
family of constituted, discovered, validated, locally executed histories and a
same-input operational non-factorization result.  It does not introduce a
global completion marker and does not identify this concrete family with every
possible decision problem.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open ConstitutiveGeneration
open SAT

/-- Canonical nonempty history length assigned to an external input. -/
def resolutionLength (input : Nat) : Nat := input + 1

/-- Unary external encoding used by the complexity statement. -/
def encodeConstitutiveInput : Nat → List Unit
  | 0 => []
  | input + 1 => () :: encodeConstitutiveInput input

theorem encodeConstitutiveInput_length (input : Nat) :
    (encodeConstitutiveInput input).length = input := by
  induction input with
  | zero => rfl
  | succ input inductionHypothesis =>
      change (encodeConstitutiveInput input).length + 1 = input + 1
      rw [inductionHypothesis]

def resolutionProduction (input : Nat) : ConstitutiveProductionRun input (resolutionLength input) :=
  let initialized := initializeConstitutiveHistory input
  produceMeasuredConstitutiveHistory input (resolutionLength input) initialized.history.endpoint
    (congrArg RootedGeneratedHistory.endpoint initialized.historyExact)

/-- Entire constitutive history produced before operational traversal. -/
def resolutionGeneratedHistory (input : Nat) :
    CanonicalGeneratedHistory input (resolutionLength input) :=
  (resolutionProduction input).history

theorem resolutionGeneratedHistory_eq_reference (input : Nat) :
    resolutionGeneratedHistory input =
      produceCanonicalGeneratedHistory input (resolutionLength input) :=
  (resolutionProduction input).historyExact

/-- The actual causally threaded history for one external input. -/
def resolutionHistory (input : Nat) :
    SequentialHistory
      input
      (initialSequentialAssignment input)
      (resolutionLength input) :=
  (executeConstitutiveExecutionHistory
    (resolutionLength input)
    (initialThreadedConstitutiveState input)
    (initialThreadedConstitutiveState_fresh input)).toSequentialHistory

theorem ConstitutiveExecutionHistory.toSequentialHistory_generatedHistory
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.generatedHistory = run.toGeneratedHistory := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      change CanonicalGeneratedHistory.step head.generation
          tailRun.toSequentialHistory.generatedHistory = _
      rw [inductionHypothesis]
      rfl

theorem decideSequentialTerminal_of_executedBits
    {depth count : Nat} {assignment : SequentialAssignment depth}
    (history : SequentialHistory depth assignment count)
    (bitsExact : history.executedBits = List.replicate count true) :
    (runTerminalReadout history.executedBits).decision =
      alternatingExecutionDecision count := by
  rw [runTerminalReadout_decision, bitsExact,
    transportedBitParity_true_replicate]

theorem ThreadedConstitutiveStageRun.reader_bound
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) (query : Var) :
    (stage.next.reader query).work.total ≤
      (assignment.reader query).work.total + (query + 2) := by
  exact stage.reader_bound query

theorem ConstitutiveExecutionHistory.reader_bound
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) (query : Var) :
    (run.toSequentialHistory.final.reader query).work.total ≤
      (assignment.reader query).work.total + count * (query + 2) := by
  induction run with
  | nil => rw [Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      change (tailRun.toSequentialHistory.final.reader query).work.total ≤ _
      calc
        _ ≤ (head.next.reader query).work.total + count * (query + 2) :=
          inductionHypothesis
        _ ≤ ((assignment.reader query).work.total + (query + 2)) +
              count * (query + 2) :=
          Nat.add_le_add_right (headRun.reader_bound query) _
        _ = _ := by rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (query + 2)]

theorem ConstitutiveExecutionHistory.variables_bounded
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    ∀ query, query ∈ run.toSequentialHistory.executedVariables →
      query ≤ stageSelectedVar (depth + count) := by
  induction run with
  | nil => intro query member; cases member
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      intro query member
      change query ∈ head.schedule.entry.var ::
        tailRun.toSequentialHistory.executedVariables at member
      cases member with
      | head =>
          rw [sequentialStage_selected_exact]
          exact stageSelectedVar_mono
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
      | tail _ prior =>
          have bounded := inductionHypothesis query prior
          have indices : depth + 1 + count = depth + (count + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 count]
          rw [indices] at bounded
          exact bounded

theorem ConstitutiveExecutionHistory.variables_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.executedVariables.length = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      change tailRun.toSequentialHistory.executedVariables.length + 1 = _
      rw [inductionHypothesis]

theorem ConstitutiveExecutionHistory.realizationWork_bound
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toDiscoveryTraversal.realizationWork.total ≤
      count * stageRealizationWork (depth + count) := by
  induction run with
  | nil => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      change (headRun.discoveryRun.generated.realizationWork.add
        tailRun.toDiscoveryTraversal.realizationWork).total ≤ _
      rw [ComparisonWork.total_add]
      have headExact : headRun.discoveryRun.generated.realizationWork.total =
          stageRealizationWork (depth + 1) := by
        rw [headRun.discoveryRun.generatedExact,
          measuredGeneratedExtraction_realizationWork_eq,
          generatedRealizationWork_exact]
      rw [headExact]
      have headBound := stageRealizationWork_mono
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
      have tailBound := inductionHypothesis
      have depthEq : depth + 1 + count = depth + (count + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 count]
      rw [depthEq] at tailBound
      rw [Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add headBound tailBound)
        (Nat.le_of_eq (Nat.add_comm _ _))

theorem ConstitutiveExecutionHistory.terminalQueries_bound
    {depth count : Nat}
    {state : ThreadedConstitutiveState depth (initialSequentialAssignment depth)}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    let history := run.toSequentialHistory
    let largest := stageSelectedVar (depth + count)
    (readAssignmentQueries history.final.reader history.executedVariables).work.total ≤
      ((largest + 1 + count * (largest + 2)) + 1) * count + 1 := by
  dsimp only
  have perQuery : ∀ query, query ∈ run.toSequentialHistory.executedVariables →
      (run.toSequentialHistory.final.reader query).work.total ≤
        stageSelectedVar (depth + count) + 1 +
          count * (stageSelectedVar (depth + count) + 2) := by
    intro query member
    have queryBound := run.variables_bounded query member
    have reading := run.reader_bound query
    exact Nat.le_trans reading (Nat.add_le_add
      (Nat.le_trans (readAlternatingAssignment_bound query)
        (Nat.add_le_add_right queryBound 1))
      (Nat.mul_le_mul_left count (Nat.add_le_add_right queryBound 2)))
  have bound := readAssignmentQueries_bound run.toSequentialHistory.final.reader
    run.toSequentialHistory.executedVariables _ perQuery
  rw [run.variables_length] at bound
  exact bound

theorem ConstitutiveExecutionHistory.terminalBit_bound
    {depth count : Nat}
    {state : ThreadedConstitutiveState depth (initialSequentialAssignment depth)}
    (run : ConstitutiveExecutionHistory (count := count + 1) state) :
    let history := run.toSequentialHistory
    let largest := stageSelectedVar (depth + (count + 1))
    (terminalFromSequentialHistory history).bitRead.work.total ≤
      largest + 1 + (count + 1) * (largest + 2) := by
  dsimp only
  let history := run.toSequentialHistory
  let terminal := terminalFromSequentialHistory history
  change (history.final.reader terminal.observedVar).work.total ≤ _
  rw [terminal.observedVarExact]
  have indexExact : lastStageDepth depth count + 1 = depth + (count + 1) := by
    unfold lastStageDepth
    rw [advancedDepth_eq_add, Nat.add_assoc]
  rw [indexExact]
  exact Nat.le_trans (run.reader_bound _)
    (Nat.add_le_add_right (readAlternatingAssignment_bound _) _)

theorem ConstitutiveExecutionHistory.terminalReadWork_bound
    {depth count : Nat}
    {state : ThreadedConstitutiveState depth (initialSequentialAssignment depth)}
    (run : ConstitutiveExecutionHistory (count := count + 1) state) :
    let history := run.toSequentialHistory
    let largest := stageSelectedVar (depth + (count + 1))
    let readBound := largest + 1 + (count + 1) * (largest + 2)
    (terminalFromSequentialHistory history).measuredReadWork ≤
      (((count + 1) + 1) + ((readBound + 1) * (count + 1) + 1)) +
        readBound + (count + 1) := by
  dsimp only
  let history := run.toSequentialHistory
  let terminal := terminalFromSequentialHistory history
  have folded : terminal.readoutRun.bitVisits = count + 1 := by
    rw [terminal.readoutRunExact, terminal.observedBitsExact,
      runTerminalReadout_visits, run.executedBits_length]
  unfold SequentialTerminalArtifact.measuredReadWork
  rw [folded]
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.le_of_eq (SequentialHistory.lastVariableRun_visits history)
    · exact run.terminalQueries_bound
  · exact run.terminalBit_bound

/--
Public result of the integrated concrete procedure.  Its only argument is the
external input; discovery, schedules, validation, returned code, applications,
terminal data, decision, and statistics are stored as produced descendants.
-/
structure ConstitutiveResolutionRun (input : Nat) where
  initialization : ConstitutiveInitializationRun input
  initializationExact : initialization = initializeConstitutiveHistory input
  threadedInitialState :
    ThreadedConstitutiveState input (initialSequentialAssignment input)
  threadedInitialStateExact :
    threadedInitialState = initialThreadedConstitutiveState input
  threadedInitialStateFromInitialization :
    threadedInitialState =
      initialThreadedConstitutiveStateFromInitialization initialization
  threadedInitialGenerationExact :
    threadedInitialState.generation = generateCanonicalStage input
  constitutiveFeedbackHistory :
    ConstitutiveExecutionHistory
      (count := resolutionLength input) threadedInitialState
  production : ConstitutiveProductionRun input (resolutionLength input)
  productionExact : production =
    constitutiveFeedbackHistory.toProductionRun
      threadedInitialGenerationExact
  generatedHistory :
    CanonicalGeneratedHistory input (resolutionLength input)
  generatedHistoryExact :
    generatedHistory = resolutionGeneratedHistory input
  generatedHistoryFromProduction : generatedHistory = production.history
  history :
    SequentialHistory
      input
      (initialSequentialAssignment input)
      (resolutionLength input)
  historyExact : history = resolutionHistory input
  historyConsumesGeneration : generatedHistory =
    constitutiveFeedbackHistory.toGeneratedHistory
  discoveryTraversal :
    GeneratedHistoryTraversalResult
      input
      (initialSequentialAssignment input)
      (resolutionLength input)
  discoveryTraversalExact :
    discoveryTraversal = constitutiveFeedbackHistory.toDiscoveryTraversal
  discoveryTraversalExecutionExact :
    discoveryTraversal.execution? = some history
  discoveryTraversalRunsExact :
    discoveryTraversal.discoveryRuns = resolutionLength input
  successfulDiscoveriesExact :
    discoveryTraversal.successfulDiscoveries = resolutionLength input
  discoveryFailureAbsent : discoveryTraversal.failureDepth? = none
  acceptedHistory : AcceptedSequentialHistory history
  fullHistoryExecution : FullHistoryExecution history
  roleHistory : ConstitutiveRoleHistory history
  historyFromCausalExecution :
    history = constitutiveFeedbackHistory.toSequentialHistory
  feedbackRoleHistory :
    ThreadedConstitutiveRoleHistory constitutiveFeedbackHistory
  feedbackStats : ConstitutiveFeedbackStats
  feedbackStatsExact : feedbackStats = constitutiveFeedbackHistory.feedbackStats
  genericRefinement : GenericRefinedHistory history
  terminal : SequentialTerminalArtifact history
  terminalExact : terminal = terminalFromSequentialHistory history
  decision : Bool
  decisionExact : decision = decideSequentialTerminal terminal
  stats : SequentialHistoryStats
  statsExact : stats = history.stats
  measuredComparisonWork : ComparisonWork
  measuredComparisonWorkExact : measuredComparisonWork = history.measuredComparisonWork
  measuredConstructionWork : ComparisonWork
  measuredConstructionWorkExact : measuredConstructionWork = history.measuredConstructionWork
  measuredValidationWork : ComparisonWork
  measuredValidationWorkExact : measuredValidationWork = history.measuredValidationWork
  measuredExecutionWork : ComparisonWork
  measuredExecutionWorkExact : measuredExecutionWork = history.measuredExecutionWork
  measuredRealizationWork : ComparisonWork
  measuredRealizationWorkExact : measuredRealizationWork = discoveryTraversal.realizationWork
  structuralProfileCost : Nat
  structuralProfileCostExact : structuralProfileCost = history.totalStructuralProfileCost
  phaseAccounting : ResolutionPhaseAccounting
  phaseAccountingExact : phaseAccounting = history.phaseAccounting
  phaseAccountingTotalExact : phaseAccounting.total = structuralProfileCost
  projectionExperiment : IntegratedProjectionExperiment history.firstStage
  projectionExperimentExact :
    projectionExperiment = runIntegratedProjectionExperiment history.firstStage

/-- Execute the whole concrete procedure from the input alone. -/
def executeConstitutiveResolution
    (input : Nat) : ConstitutiveResolutionRun input :=
  let initialization := initializeConstitutiveHistory input
  let threadedInitialState :=
    initialThreadedConstitutiveStateFromInitialization initialization
  let feedbackHistory := executeConstitutiveExecutionHistory
    (resolutionLength input) threadedInitialState
    (initialThreadedConstitutiveStateFromInitialization_fresh initialization)
  have initialGenerationExact : threadedInitialState.generation =
      generateCanonicalStage input :=
    initialThreadedConstitutiveStateFromInitialization_generation_exact initialization
  let history := feedbackHistory.toSequentialHistory
  have historyCanonical : history = resolutionHistory input := by
    rfl
  let production := feedbackHistory.toProductionRun initialGenerationExact
  let generatedHistory := production.history
  let traversal := feedbackHistory.toDiscoveryTraversal
  have traversed := feedbackHistory.toDiscoveryTraversal_exact
  let terminal := terminalFromSequentialHistory history
  { history := history
    initialization := initialization
    initializationExact := rfl
    threadedInitialState := threadedInitialState
    threadedInitialStateExact := rfl
    threadedInitialStateFromInitialization := rfl
    threadedInitialGenerationExact := initialGenerationExact
    constitutiveFeedbackHistory := feedbackHistory
    production := production
    productionExact := rfl
    generatedHistory := generatedHistory
    generatedHistoryExact := Eq.trans production.historyExact
      (resolutionGeneratedHistory_eq_reference input).symm
    generatedHistoryFromProduction := rfl
    historyExact := historyCanonical
    historyConsumesGeneration := rfl
    discoveryTraversal := traversal
    discoveryTraversalExact := rfl
    discoveryTraversalExecutionExact := traversed.1
    discoveryTraversalRunsExact := traversed.2.1
    successfulDiscoveriesExact := traversed.2.2.1
    discoveryFailureAbsent := traversed.2.2.2
    acceptedHistory := feedbackHistory.toAcceptedHistory
    fullHistoryExecution := executeFullHistory history
    roleHistory := buildConstitutiveRoleHistory history
    historyFromCausalExecution := rfl
    feedbackRoleHistory := buildThreadedConstitutiveRoleHistory feedbackHistory
    feedbackStats := feedbackHistory.feedbackStats
    feedbackStatsExact := rfl
    terminal := terminal
    genericRefinement := executedHistory_genericRefinement history
    terminalExact := rfl
    decision := decideSequentialTerminal terminal
    decisionExact := rfl
    stats := history.stats
    statsExact := rfl
    measuredComparisonWork := history.measuredComparisonWork
    measuredComparisonWorkExact := rfl
    measuredConstructionWork := history.measuredConstructionWork
    measuredConstructionWorkExact := rfl
    measuredValidationWork := history.measuredValidationWork
    measuredValidationWorkExact := rfl
    measuredExecutionWork := history.measuredExecutionWork
    measuredExecutionWorkExact := rfl
    measuredRealizationWork := traversal.realizationWork
    measuredRealizationWorkExact := rfl
    structuralProfileCost := history.totalStructuralProfileCost
    structuralProfileCostExact := rfl
    phaseAccounting := history.phaseAccounting
    phaseAccountingExact := rfl
    phaseAccountingTotalExact := history.phaseAccounting_exact
    projectionExperiment := runIntegratedProjectionExperiment history.firstStage
    projectionExperimentExact := rfl }

/-- The number of actual producer calls is the nonconstant requested length. -/
theorem executeConstitutiveResolution_generatedSteps (input : Nat) :
    (executeConstitutiveResolution input).stats.generatedSteps = input + 1 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.1

/-- One discovered schedule atom is produced per generated stage. -/
theorem executeConstitutiveResolution_scheduleAtoms (input : Nat) :
    (executeConstitutiveResolution input).stats.scheduleAtoms = input + 1 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.2.2.2.1

/-- Validation performs one primitive query per generated stage. -/
theorem executeConstitutiveResolution_validationQueries (input : Nat) :
    (executeConstitutiveResolution input).stats.validationPrimitiveQueries =
      input + 1 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.2.2.2.2.1

/-- Local execution performs one primitive query per generated stage. -/
theorem executeConstitutiveResolution_executionQueries (input : Nat) :
    (executeConstitutiveResolution input).stats.executionPrimitiveQueries =
      input + 1 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.2.2.2.2.2.1

/-- Every code returned by the local runs is actually applied once. -/
theorem executeConstitutiveResolution_appliedAtoms (input : Nat) :
    (executeConstitutiveResolution input).stats.appliedCodeAtoms = input + 1 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.2.2.2.2.2.2.2

/-- No global composition candidate is inspected anywhere in the history. -/
theorem executeConstitutiveResolution_noGlobalComposition (input : Nat) :
    (executeConstitutiveResolution input).stats.compositionCandidates = 0 := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  exact (run.constitutiveFeedbackHistory.coreStats_exact
    run.threadedInitialGenerationExact).2.2.2.2.2.2.2.1

/--
All structural cardinalities are consequences of the objects already produced
by the run.  No numeric witness is accepted by the public procedure.
-/
theorem executeConstitutiveResolution_correspondences (input : Nat) :
    let run := executeConstitutiveResolution input
    run.generatedHistory.stepCount = input + 1 ∧
      run.stats.generatedSteps = input + 1 ∧
      run.discoveryTraversal.successfulDiscoveries = input + 1 ∧
      run.stats.scheduleAtoms = input + 1 ∧
      run.stats.appliedCodeAtoms = input + 1 ∧
      run.stats.validationPrimitiveQueries = input + 1 ∧
      run.stats.executionPrimitiveQueries = input + 1 ∧
      run.stats.compositionCandidates = 0 := by
  let run := executeConstitutiveResolution input
  exact
    ⟨by rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference];
        exact producedHistory_stepCount input (resolutionLength input),
      executeConstitutiveResolution_generatedSteps input,
      run.successfulDiscoveriesExact,
      executeConstitutiveResolution_scheduleAtoms input,
      executeConstitutiveResolution_appliedAtoms input,
      executeConstitutiveResolution_validationQueries input,
      executeConstitutiveResolution_executionQueries input,
      executeConstitutiveResolution_noGlobalComposition input⟩

/-- The final decision reads the terminal produced from the threaded history. -/
theorem executeConstitutiveResolution_decision_from_terminal (input : Nat) :
    (executeConstitutiveResolution input).decision =
      decideSequentialTerminal
        (executeConstitutiveResolution input).terminal :=
  (executeConstitutiveResolution input).decisionExact

/-- The decision is the alternating signal of actually applied trace atoms. -/
theorem executeConstitutiveResolution_decision (input : Nat) :
    (executeConstitutiveResolution input).decision =
      alternatingExecutionDecision (input + 1) := by
  let run := executeConstitutiveResolution input
  calc
    run.decision = (runTerminalReadout run.history.executedBits).decision := by
      rw [run.decisionExact, run.terminalExact]
      unfold decideSequentialTerminal
      rw [
        (terminalFromSequentialHistory run.history).decisionBitExact,
        (terminalFromSequentialHistory run.history).readoutRunExact,
        (terminalFromSequentialHistory run.history).observedBitsExact]
      rfl
    _ = alternatingExecutionDecision (resolutionLength input) :=
      decideSequentialTerminal_of_executedBits run.history (by
        rw [run.historyFromCausalExecution]
        exact run.constitutiveFeedbackHistory.executedBits_exact)
    _ = alternatingExecutionDecision (input + 1) := rfl

/-- The family contains a concrete YES instance. -/
theorem executeConstitutiveResolution_zero_yes :
    (executeConstitutiveResolution 0).decision = true := by
  rw [executeConstitutiveResolution_decision]
  rfl

/-- The family contains a concrete NO instance. -/
theorem executeConstitutiveResolution_one_no :
    (executeConstitutiveResolution 1).decision = false := by
  rw [executeConstitutiveResolution_decision]
  rfl

/-- Successive external inputs execute strictly more constituted stages. -/
theorem resolution_generatedSteps_strict (input : Nat) :
    (executeConstitutiveResolution input).stats.generatedSteps <
      (executeConstitutiveResolution (input + 1)).stats.generatedSteps := by
  rw [
    executeConstitutiveResolution_generatedSteps,
    executeConstitutiveResolution_generatedSteps
  ]
  exact Nat.lt_succ_self (input + 1)

/-- Exact discovery-effort law for the counter emitted by the authoritative
feedback recursion, after its produced provenance has filtered prior variables. -/
theorem executeConstitutiveResolution_attempts_exact (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts =
      threadedAttemptTotal (2 * input + 10) (input + 1) := by
  let run := executeConstitutiveResolution input
  rw [run.statsExact, run.historyFromCausalExecution]
  have invariant : ThreadedProvenanceInvariant run.threadedInitialState := by
    rw [run.threadedInitialStateExact]
    exact initialThreadedProvenanceInvariant input
  have exactTotal := run.constitutiveFeedbackHistory.discoveryAttempts_eq_threadedTotal
    invariant
  have initialAttempts := threadedDiscovery_attempts_add_provenance_exact
    run.threadedInitialState invariant
  have provenanceEmpty : run.threadedInitialState.provenance.length = 0 := by
    rw [run.threadedInitialStateExact]
    rfl
  rw [provenanceEmpty] at initialAttempts
  rw [Nat.add_zero] at initialAttempts
  rw [exactTotal, initialAttempts]
  rfl

/-- Successive external inputs strictly increase the discovery attempts
actually emitted by the authoritative causally threaded execution. -/
theorem executeConstitutiveResolution_attempts_strict (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts := by
  rw [executeConstitutiveResolution_attempts_exact,
    executeConstitutiveResolution_attempts_exact]
  exact threadedAttemptTotal_integrated_strict input

theorem natFunction_strict_of_successor (function : Nat → Nat)
    (successor : ∀ input, function input < function (input + 1))
    {first second : Nat} (before : first < second) : function first < function second := by
  induction second with
  | zero => exact False.elim (Nat.not_lt_zero first before)
  | succ second ih =>
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with
    | inl earlier => exact Nat.lt_trans (ih earlier) (successor second)
    | inr same => cases same; exact successor first

def resolutionStageSurfacePolynomial : CostPolynomial :=
  CostPolynomial.mul
    (CostPolynomial.add
      CostPolynomial.input
      (CostPolynomial.constant 1))
    (CostPolynomial.substitute
      sequentialStageSurfacePolynomial
      (CostPolynomial.add
        CostPolynomial.input
        (CostPolynomial.add
          CostPolynomial.input
          (CostPolynomial.constant 1))))

/-- Stage work plus all terminal parity reads and its final list observation. -/
def resolutionSurfacePolynomial : CostPolynomial :=
  CostPolynomial.add
    (CostPolynomial.add
      resolutionStageSurfacePolynomial
      (CostPolynomial.add
        CostPolynomial.input
        (CostPolynomial.constant 1)))
    (CostPolynomial.constant 1)

/--
Named causal obligations for one concrete stage.  This record makes the
phase-to-phase equalities inspectable without deriving any operational object
from the constitutive generation witness alone.
-/
structure ConstitutiveCausalStageEvidence (depth : Nat) : Type 2 where
  run : SequentialStageRun depth (initialSequentialAssignment depth)
  runExact : run =
    executeSequentialStage depth (initialSequentialAssignment depth)
  discoveryComesFromExecutedSearch :
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? =
      some run.discovery
  relationComesFromDiscovery :
    run.schedule.entry.relation = run.discovery.relation
  validationConsumesProducedSchedule :
    run.validated.run = runDiscoveryScheduleValidation run.schedule
  executionConsumesValidatedSchedule :
    run.execution.run = run.schedule.entry.executionRun
  returnedCodeComesFromDiscoveredRelation :
    run.execution.code = run.schedule.entry.code
  continuationComesFromReturnedCode :
    run.application.output =
      (run.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)
          run.schedule.entry.var)).map
        run.sourceContinuation
  sourceIsAccepted :
    GeneratedStructuralBranchAccept
      run.schedule.entry.source run.sourceContinuation
  outputIsAccepted :
    GeneratedStructuralBranchAccept
      run.schedule.entry.target run.application.output

def constitutiveCausalStageEvidence
    (depth : Nat) : ConstitutiveCausalStageEvidence depth :=
  let run := executeSequentialStage depth (initialSequentialAssignment depth)
  { run := run
    runExact := rfl
    discoveryComesFromExecutedSearch := run.discoveryExact
    relationComesFromDiscovery := concreteRelation_comes_from_discovery run
    validationConsumesProducedSchedule := run.validated.runExact
    executionConsumesValidatedSchedule := run.execution.runExact
    returnedCodeComesFromDiscoveredRelation :=
      executedDiscoverySchedule_code run.execution
    continuationComesFromReturnedCode := run.application.outputExact
    sourceIsAccepted := run.sourceAccepted
    outputIsAccepted := run.outputAccepted }

/--
The exact aggregate required by §6.  The fields do not reconstruct a second
execution: they expose, in one typed package, the equalities and recursive
witnesses already carried by the unique public run.
-/
structure Section6OperationalSuccessionEvidence {input : Nat}
    (run : ConstitutiveResolutionRun input) : Type 2 where
  sourceIsInitial :
    run.generatedHistory = run.constitutiveFeedbackHistory.toGeneratedHistory
  discoveryTraversalReturnsHistory :
    run.discoveryTraversal.execution? = some run.history
  successionIsTyped : FullHistoryExecution run.history
  discoveryProvenanceIsRetained : GenericRefinedHistory run.history
  returnedCodesComeFromDiscoveredPath :
    run.history.localPath.map LocalPrimitiveAtom.compile = run.history.returnedCodes
  terminalComesFromExecution :
    run.terminal = terminalFromSequentialHistory run.history
  targetIsHistoryEndpoint :
    run.terminal.assignment = run.history.final.assignment
  executedAtomsAreGeneratedSteps :
    run.stats.appliedCodeAtoms = run.generatedHistory.stepCount
  compositionCandidatesAreZero :
    run.stats.compositionCandidates = 0
  terminalContinuationIsOperationalFold :
    run.terminal.assignment =
      foldOperationalSteps run.history.returnedCodes
        (initialSequentialAssignment input).assignment

def section6OperationalSuccessionEvidence {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    Section6OperationalSuccessionEvidence run :=
  { sourceIsInitial := run.historyConsumesGeneration
    discoveryTraversalReturnsHistory := run.discoveryTraversalExecutionExact
    successionIsTyped := run.fullHistoryExecution
    discoveryProvenanceIsRetained := run.genericRefinement
    returnedCodesComeFromDiscoveredPath := localPath_compiles_to_returnedCodes run.history
    terminalComesFromExecution := run.terminalExact
    targetIsHistoryEndpoint := run.terminal.assignmentExact
    executedAtomsAreGeneratedSteps := by
      calc
        run.stats.appliedCodeAtoms = input + 1 := by
          rw [run.statsExact, run.historyFromCausalExecution]
          exact (run.constitutiveFeedbackHistory.coreStats_exact
            run.threadedInitialGenerationExact).2.2.2.2.2.2.2.2
        _ = run.generatedHistory.stepCount := by
          rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference]
          exact (producedHistory_stepCount input (resolutionLength input)).symm
    compositionCandidatesAreZero := by
      rw [run.statsExact, run.historyFromCausalExecution]
      exact (run.constitutiveFeedbackHistory.coreStats_exact
        run.threadedInitialGenerationExact).2.2.2.2.2.2.2.1
    terminalContinuationIsOperationalFold :=
      Eq.trans run.terminal.assignmentExact
        (terminalAssignment_is_operational_fold run.history) }

/--
Exact evidence exposed for every input.  Each field names a construction or a
theorem already tied to the executed run; no conditional operational premise
is left open.
-/
structure EndogenousOperationalDecompositionEvidence (input : Nat) : Type 3 where
  stageConstitution : ConstitutiveStageEvidence input
  oldOccurrencesPersist :
    ∀ occurrence : History.Occurrence (constitutedHistory input).history,
      (successorOccurrenceSplit examplePresentation input).forward
          (.inl occurrence) =
        History.Occurrence.earlier occurrence
  freshOccurrenceRemainsDistinct :
    ∀ occurrence : History.Occurrence (constitutedHistory input).history,
      History.Occurrence.earlier occurrence ≠
        (History.Occurrence.last :
          History.Occurrence (constitutedHistory (input + 1)).history)
  provenancePersists :
    PreservesProvenance
      (constructStage input).history.endpoint
      (constructStage (input + 1)).history.endpoint
  occurrenceOrderPreserved :
    ∀ {first second : History.Occurrence (constitutedHistory input).history},
      History.OccurrencePrecedes first second →
        History.OccurrencePrecedes
          ((successorOccurrenceSplit examplePresentation input).forward (.inl first))
          ((successorOccurrenceSplit examplePresentation input).forward (.inl second))
  residualDifferencePreserved :
    FreshBoundaryDifference (constructStage input).history.endpoint
  realization : RealizedConstitutiveStage input
  realizationExact : realization = realizeConstitutedStage input
  interfaceRealizationExact :
    concreteConstitutiveOperationalInterface.realize
        (constitutedEndpoint input) =
      constitutedSearchIndex input
  causalStage : ConstitutiveCausalStageEvidence input
  run : ConstitutiveResolutionRun input
  runExact : run = executeConstitutiveResolution input
  generatedHistoryExact : run.stats.generatedSteps = input + 1
  generationCallsExact : run.stats.generateCalls = input + 1
  provenanceUnitsExact : run.stats.provenanceUnits = input + 1
  generationCertificatesExact :
    run.stats.generationCertificates = input + 1
  generatedObjectHasExactLength : run.generatedHistory.stepCount = input + 1
  operationalHistoryConsumesGeneratedObject :
    run.generatedHistory = run.constitutiveFeedbackHistory.toGeneratedHistory
  failureAwareTraversalConsumesDiscovery :
    run.discoveryTraversal.execution? = some run.history
  discoveryRunsExact : run.discoveryTraversal.discoveryRuns = input + 1
  successfulDiscoveriesExact :
    run.discoveryTraversal.successfulDiscoveries = input + 1
  noDiscoveryFailure : run.discoveryTraversal.failureDepth? = none
  section6Succession : Section6OperationalSuccessionEvidence run
  constitutiveFeedbackIsThreaded :
    ConstitutiveExecutionHistory
      (count := resolutionLength input) run.threadedInitialState
  publicHistoryComesFromCausalExecution :
    run.history = run.constitutiveFeedbackHistory.toSequentialHistory
  feedbackRolesFollowThreadedHistory :
    ThreadedConstitutiveRoleHistory run.constitutiveFeedbackHistory
  feedbackAccountingIsProduced :
    run.feedbackStats = run.constitutiveFeedbackHistory.feedbackStats
  nextDiscoveryDependsOnConstitution :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := input))
        (nextDiscoveryOutcome (depth := input))
  feedbackFailureProducesNothing :
    feedbackFailureArtifacts input = ⟨0, false, false⟩
  acceptedExecutionHistory : AcceptedSequentialHistory run.history
  compiledPathIsReturnedCode :
    run.history.localPath.map LocalPrimitiveAtom.compile = run.history.returnedCodes
  producedPathLength : run.history.localPath.length = input + 1
  returnedCodeSize : compiledLocalSize run.history.returnedCodes = input + 1
  terminalAssignmentIsExecutedFold :
    run.history.final.assignment = foldOperationalSteps run.history.returnedCodes
      (initialSequentialAssignment input).assignment
  scheduleProductionExact : run.stats.scheduleAtoms = input + 1
  validationExact : run.stats.validationPrimitiveQueries = input + 1
  localExecutionExact : run.stats.executionPrimitiveQueries = input + 1
  applicationExact : run.stats.appliedCodeAtoms = input + 1
  relationQueriesAreAttempts :
    run.stats.relationQueries = run.stats.discoveryAttempts
  noGlobalComposition : run.stats.compositionCandidates = 0
  structuralProfileCostProduced : run.structuralProfileCost = run.history.totalStructuralProfileCost
  phaseAccountingProduced : run.phaseAccounting = run.history.phaseAccounting
  phaseAccountingSumExact :
    run.phaseAccounting.total = run.structuralProfileCost
  terminalReadoutInstrumented :
    run.terminal.readoutRun.bitVisits = run.terminal.observedBits.length
  terminalProducedByHistory :
    run.terminal = terminalFromSequentialHistory run.history
  transportedBitsProducedByExecution :
    run.terminal.observedBits = run.history.executedBits
  terminalReadoutPreserved :
    run.terminal.executedVariables.map run.terminal.assignment = run.terminal.observedBits
  decisionReadsTerminalOnly :
    run.decision = decideSequentialTerminal run.terminal
  decisionReadsTransportedBits :
    run.decision = transportedBitParity run.terminal.observedBits
  projectionSplitComesFromConstitution :
    projectionSplitVar input =
      growingDiscoverySplitVar (constitutedSearchIndex input)
  projectionRootComesFromConstitution :
    projectionRootFormula input =
      symmetricBlockFamily
        (growingDiscoverySplitVar (constitutedSearchIndex input))
        (growingDiscoveryAnchorVar (constitutedSearchIndex input))
        []
  sameInputConstitutionsDistinct :
    (integratedMarkedTarget run.history.firstStage 2 (by decide)).context.decisions ≠
      (integratedMarkedTarget run.history.firstStage 4 (by decide)).context.decisions
  sameInputProjectionEqual :
    integratedInputProjection run.history.firstStage .compatible =
      integratedInputProjection run.history.firstStage .incompatible
  operationalProjectionNonFactorization :
    ¬ ValueFactorsThrough
        (integratedInputProjection run.history.firstStage)
        (fun organization => (integratedOrganizationObservation run.history.firstStage organization).terminalBit)
  projectionUsesSection31Primitives :
    Section31PrimitiveRaccord run.history.firstStage
  projectionPositiveCodeAtoms :
    run.projectionExperiment.positiveRun.codeAtoms = 1
  projectionNegativeCodeAtoms :
    run.projectionExperiment.negativeRun.codeAtoms = 0
  projectionRunsIntegrated :
    run.projectionExperiment = runIntegratedProjectionExperiment run.history.firstStage

/- Closed construction of the exact evidence package for every input. -/
set_option maxHeartbeats 1000000 in
def endogenousOperationalDecompositionEvidence
    (input : Nat) : EndogenousOperationalDecompositionEvidence input :=
  let run := executeConstitutiveResolution input
  { stageConstitution := constitutiveStageEvidence input
    oldOccurrencesPersist := constitutedOldOccurrence_persists input
    freshOccurrenceRemainsDistinct := constitutedOldOccurrence_ne_fresh input
    occurrenceOrderPreserved := constitutedOccurrence_order_preserved input
    provenancePersists :=
      (constitutiveStageEvidence input).provenancePersists
    residualDifferencePreserved :=
      (constitutiveStageEvidence input).residualDifferenceRemainsFresh
    realization := realizeConstitutedStage input
    realizationExact := rfl
    interfaceRealizationExact :=
      concreteInterface_realize_constitutedEndpoint input
    causalStage := constitutiveCausalStageEvidence input
    run := run
    runExact := rfl
    generatedHistoryExact :=
      executeConstitutiveResolution_generatedSteps input
    generationCallsExact :=
      by
        rw [run.statsExact, run.historyFromCausalExecution]
        exact (run.constitutiveFeedbackHistory.coreStats_exact
          run.threadedInitialGenerationExact).1
    provenanceUnitsExact :=
      by
        rw [run.statsExact, run.historyFromCausalExecution]
        exact (run.constitutiveFeedbackHistory.coreStats_exact
          run.threadedInitialGenerationExact).2.2.1
    generationCertificatesExact :=
      by
        rw [run.statsExact, run.historyFromCausalExecution]
        exact (run.constitutiveFeedbackHistory.coreStats_exact
          run.threadedInitialGenerationExact).2.2.2.1
    generatedObjectHasExactLength := by
      rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference]
      exact producedHistory_stepCount input (resolutionLength input)
    operationalHistoryConsumesGeneratedObject :=
      run.historyConsumesGeneration
    failureAwareTraversalConsumesDiscovery :=
      run.discoveryTraversalExecutionExact
    discoveryRunsExact := run.discoveryTraversalRunsExact
    successfulDiscoveriesExact := run.successfulDiscoveriesExact
    noDiscoveryFailure := run.discoveryFailureAbsent
    section6Succession := section6OperationalSuccessionEvidence run
    constitutiveFeedbackIsThreaded := run.constitutiveFeedbackHistory
    publicHistoryComesFromCausalExecution := run.historyFromCausalExecution
    feedbackRolesFollowThreadedHistory := run.feedbackRoleHistory
    feedbackAccountingIsProduced := run.feedbackStatsExact
    nextDiscoveryDependsOnConstitution := nextDiscovery_not_factors input
    feedbackFailureProducesNothing := feedbackFailureArtifacts_exact input
    acceptedExecutionHistory := run.acceptedHistory
    compiledPathIsReturnedCode := localPath_compiles_to_returnedCodes run.history
    producedPathLength := localPath_length run.history
    returnedCodeSize := returnedCodes_size run.history
    terminalAssignmentIsExecutedFold := terminalAssignment_is_operational_fold run.history
    scheduleProductionExact :=
      executeConstitutiveResolution_scheduleAtoms input
    validationExact :=
      executeConstitutiveResolution_validationQueries input
    localExecutionExact :=
      executeConstitutiveResolution_executionQueries input
    applicationExact :=
      executeConstitutiveResolution_appliedAtoms input
    relationQueriesAreAttempts :=
      by
        rw [run.statsExact, run.historyFromCausalExecution]
        exact run.constitutiveFeedbackHistory.relationQueries_eq_attempts
    noGlobalComposition :=
      executeConstitutiveResolution_noGlobalComposition input
    structuralProfileCostProduced := run.structuralProfileCostExact
    phaseAccountingProduced := run.phaseAccountingExact
    phaseAccountingSumExact := run.phaseAccountingTotalExact
    terminalReadoutInstrumented := by
      rw [run.terminal.readoutRunExact]
      exact runTerminalReadout_visits _
    terminalProducedByHistory := run.terminalExact
    transportedBitsProducedByExecution :=
      run.terminal.observedBitsExact
    terminalReadoutPreserved := by
      rw [run.terminal.executedVariablesExact, run.terminal.assignmentExact,
        run.terminal.observedBitsExact]
      exact run.history.readout_preserved
    decisionReadsTerminalOnly := run.decisionExact
    decisionReadsTransportedBits := by
      calc
        run.decision = run.terminal.decisionBit := run.decisionExact
        _ = run.terminal.readoutRun.decision :=
          run.terminal.decisionBitExact
        _ = (runTerminalReadout run.terminal.observedBits).decision :=
          congrArg
            (fun readout : TerminalReadoutRun => readout.decision)
            run.terminal.readoutRunExact
        _ = transportedBitParity run.terminal.observedBits :=
          runTerminalReadout_decision _
    projectionSplitComesFromConstitution :=
      projectionSplitVar_from_constitution input
    projectionRootComesFromConstitution :=
      projectionRootFormula_from_constitution input
    sameInputConstitutionsDistinct :=
      integrated_marked_constitutions_distinct run.history.firstStage
    sameInputProjectionEqual := congrArg (fun formula => (input, formula))
      (integrated_marked_projection_equal run.history.firstStage)
    operationalProjectionNonFactorization :=
      integrated_projection_not_factors run.history.firstStage
    projectionUsesSection31Primitives := run.projectionExperiment.section31Raccord
    projectionPositiveCodeAtoms := run.projectionExperiment.positiveCodeAtoms
    projectionNegativeCodeAtoms := run.projectionExperiment.negativeCodeAtoms
    projectionRunsIntegrated := run.projectionExperimentExact }

/-- Execution retains the precise generated steps supplied to its traversal. -/
theorem ConstitutiveResolutionRun.generatorsExact {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.history.generatedHistory = run.generatedHistory := by
  rw [run.historyFromCausalExecution,
    run.constitutiveFeedbackHistory.toSequentialHistory_generatedHistory,
    ← run.historyConsumesGeneration]

/-- The generic traversal returns the actual local discoveries of the public run.
HEq accounts only for the proved equality of the two history indices. -/
theorem ConstitutiveResolutionRun.genericTraversalExact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    HEq (concreteConstitutiveOperationalInterface.discoverHistory run.generatedHistory.asGeneric)
      (some run.history.genericDiscovered) := by
  rw [← run.generatorsExact]
  exact heq_of_eq (executedHistory_genericTraversal run.history)

/-- Only the four instrumented search/construction subprograms, not total run cost. -/
def ConstitutiveResolutionRun.measuredSearchWork {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  (run.measuredComparisonWork.add run.measuredConstructionWork).total +
    (run.measuredValidationWork.add run.measuredExecutionWork).total

def resolutionMeasuredSearchPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .add (.mul count (stageDiscoveryPolynomial last))
    (.mul count (.add (stageRelationPolynomial last) (stageRelationPolynomial last)))

theorem ConstitutiveResolutionRun.measuredSearchWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.measuredSearchWork ≤ resolutionMeasuredSearchPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.measuredSearchWork
  rw [run.measuredComparisonWorkExact, run.measuredConstructionWorkExact,
    run.measuredValidationWorkExact, run.measuredExecutionWorkExact]
  exact Nat.add_le_add (historyDiscovery_measured_bound run.history)
    (historyValidationExecution_measured_bound run.history)

/-- Polynomial bound on actual measured subprogram work, relative to the
executable unary input encoding. Initialization and driver costs are excluded. -/
theorem constitutiveMeasuredSearch_inputPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).measuredSearchWork) := by
  refine ⟨resolutionMeasuredSearchPolynomial, ?_⟩
  intro input
  dsimp only
  rw [encodeConstitutiveInput_length]
  exact (executeConstitutiveResolution input).measuredSearchWork_bound

def resolutionTerminalReadPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  let largest : CostPolynomial := .add (.mul (.constant 2) (.add last (.constant 3))) (.constant 2)
  let reading : CostPolynomial := .add (.add largest (.constant 1))
    (.mul count (.add largest (.constant 2)))
  .add (.add (.add (.add count (.constant 1))
    (.add (.mul (.add reading (.constant 1)) count) (.constant 1))) reading) count

theorem ConstitutiveResolutionRun.terminalReadWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.terminal.measuredReadWork ≤ resolutionTerminalReadPolynomial.eval input := by
  rw [run.terminalExact, run.historyFromCausalExecution]
  have bounded := run.constitutiveFeedbackHistory.terminalReadWork_bound
  dsimp only at bounded
  have labelExact : stageSelectedVar (input + (input + 1)) =
      2 * ((input + (input + 1)) + 3) + 2 := by
    change constitutedSearchIndex (input + (input + 1)) + 2 = _
    rw [constitutedSearchIndex_exact]
  rw [labelExact] at bounded
  exact bounded

def resolutionRealizationPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .mul count (.add (.mul (.constant 2)
    (.add (.mul (.constant 2) (.add last (.constant 3))) (.constant 1))) (.constant 16))

theorem ConstitutiveResolutionRun.realizationWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.measuredRealizationWork.total ≤ resolutionRealizationPolynomial.eval input := by
  rw [run.measuredRealizationWorkExact, run.discoveryTraversalExact]
  exact run.constitutiveFeedbackHistory.realizationWork_bound

/-- Count producer invocations once. Appended steps and provenance indicators
describe their outputs; they are deliberately not added as duplicate calls. -/
def ConstitutiveResolutionRun.productionCalls {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  run.initialization.generateCalls + run.production.generateCalls

theorem ConstitutiveResolutionRun.productionCalls_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) : run.productionCalls = input + (input + 1) := by
  unfold ConstitutiveResolutionRun.productionCalls
  have generationCanonical : run.threadedInitialState.generation =
      generateCanonicalStage input := by
    exact run.threadedInitialGenerationExact
  have productionExact : run.production.generateCalls = resolutionLength input := by
    calc
      run.production.generateCalls =
          run.constitutiveFeedbackHistory.productionStats.generateCalls :=
        congrArg ConstitutiveProductionRun.generateCalls run.productionExact
      _ = resolutionLength input :=
        (run.constitutiveFeedbackHistory.productionStats_exact generationCanonical).1
  rw [run.initializationExact, (initializeConstitutiveHistory_counts input).1,
    productionExact]
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.terminalReadWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.realizationWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.productionCalls
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.productionCalls_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.resolutionProduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.measuredSearchWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.measuredSearchWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveMeasuredSearch_inputPolynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.generatorsExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.genericTraversalExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.resolutionGeneratedHistory_eq_reference
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution
#print axioms ConstitutiveSearch.EndogenousDecomposition.encodeConstitutiveInput_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_decision_from_terminal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_decision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_zero_yes
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_one_no
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_noGlobalComposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_correspondences
#print axioms ConstitutiveSearch.EndogenousDecomposition.resolution_generatedSteps_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_attempts_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_attempts_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveCausalStageEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.section6OperationalSuccessionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.endogenousOperationalDecompositionEvidence
/- AXIOM_AUDIT_END -/
