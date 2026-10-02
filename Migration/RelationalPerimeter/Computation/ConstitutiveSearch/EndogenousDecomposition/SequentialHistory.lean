import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialResolution

/-!
# Recursively executed constitutive history

The trace below is indexed by its current threaded assignment.  Its constructor
forces the tail to consume `head.next`; consequently an independently rebuilt
state cannot be inserted between two stages.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- Endpoint depth obtained by advancing one stage per recursive step. -/
def advancedDepth : Nat → Nat → Nat
  | startDepth, 0 => startDepth
  | startDepth, count + 1 => advancedDepth (startDepth + 1) count

theorem advancedDepth_eq_add (startDepth count : Nat) :
    advancedDepth startDepth count = startDepth + count := by
  induction count generalizing startDepth with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [advancedDepth, inductionHypothesis]
      calc
        startDepth + 1 + count = startDepth + (1 + count) :=
          Nat.add_assoc startDepth 1 count
        _ = startDepth + (count + 1) :=
          congrArg (fun value => startDepth + value) (Nat.add_comm 1 count)

/-- A trace whose next stage is indexed by the preceding produced assignment. -/
inductive SequentialHistory :
    (startDepth : Nat) →
      SequentialAssignment startDepth →
      Nat → Type where
  | nil
      (startDepth : Nat)
      (input : SequentialAssignment startDepth) :
      SequentialHistory startDepth input 0
  | step
      {startDepth count : Nat}
      {input : SequentialAssignment startDepth}
      (head : SequentialStageRun startDepth input)
      (tail : SequentialHistory (startDepth + 1) head.next count) :
      SequentialHistory startDepth input (count + 1)

/-- Canonical recursive execution; no later input is supplied by the caller. -/
def executeSequentialHistory :
    (startDepth count : Nat) →
      (input : SequentialAssignment startDepth) →
        SequentialHistory startDepth input count
  | startDepth, 0, input => .nil startDepth input
  | startDepth, count + 1, input =>
      let head := executeSequentialStage startDepth input
      .step
        head
        (executeSequentialHistory
          (startDepth + 1)
          count
          head.next)

/-- The final assignment is recovered by following the typed tail. -/
def SequentialHistory.final :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count →
          SequentialAssignment (advancedDepth startDepth count)
  | _, _, _, .nil _ input => input
  | _, _, _, .step _head tail => tail.final

/-- Discovered variables whose returned transport atoms were actually applied. -/
def SequentialHistory.executedVariables :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count → List Var
  | _, _, _, .nil _ _ => []
  | _, _, _, .step head tail =>
      head.schedule.entry.var :: tail.executedVariables

/-- Exactly one discovered variable is retained for every executed stage. -/
theorem executedHistory_variables_length
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
      startDepth count input).executedVariables.length = count := by
  induction count generalizing startDepth input with
  | zero =>
      rw [executeSequentialHistory, SequentialHistory.executedVariables]
      rfl
  | succ count inductionHypothesis =>
      rw [executeSequentialHistory, SequentialHistory.executedVariables]
      change
        (executeSequentialHistory
          (startDepth + 1)
          count
          (executeSequentialStage startDepth input).next).executedVariables.length + 1 =
            count + 1
      rw [inductionHypothesis]

/-- Later stages preserve every query below the next discovered variable. -/
theorem executedHistory_preserves_below
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth)
    (query : Var)
    (below : query < stageSelectedVar (startDepth + 1)) :
    (executeSequentialHistory startDepth count input).final.assignment query =
      input.assignment query := by
  induction count generalizing startDepth input with
  | zero =>
      rw [executeSequentialHistory, SequentialHistory.final]
  | succ count inductionHypothesis =>
      let head := executeSequentialStage startDepth input
      have currentBeforeNext :
          stageSelectedVar (startDepth + 1) <
            stageSelectedVar ((startDepth + 1) + 1) := by
        rw [stageSelectedVar_succ (startDepth + 1)]
        exact
          Nat.lt_trans
            (Nat.lt_succ_self _)
            (Nat.lt_succ_self (_ + 1))
      have belowNext :
          query < stageSelectedVar ((startDepth + 1) + 1) :=
        Nat.lt_trans below currentBeforeNext
      rw [executeSequentialHistory, SequentialHistory.final]
      calc
        (executeSequentialHistory
            (startDepth + 1)
            count
            head.next).final.assignment query =
            head.next.assignment query :=
          inductionHypothesis
            (startDepth + 1)
            head.next
            belowNext
        _ = input.assignment query :=
          executeSequentialStage_preserves_other
            startDepth
            input
            query
            (Nat.ne_of_lt below)

/-- Values read immediately from the continuations produced by executed atoms. -/
theorem SequentialHistory.preserves_below
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) (query : Var)
    (below : query < stageSelectedVar (depth + 1)) :
    history.final.assignment query = input.assignment query := by
  induction history with
  | nil => rfl
  | @step depth count input head tail ih =>
    have belowNext : query < stageSelectedVar (depth + 1 + 1) := by
      exact Nat.lt_trans below (stageSelectedVar_strict (Nat.lt_succ_self (depth + 1)))
    change tail.final.assignment query = _
    rw [ih belowNext, sequentialStage_next_from_input,
      sequentialStage_selected_exact]
    exact Assignment.flipAt_other _ _ _ (Nat.ne_of_lt below)

def SequentialHistory.executedBits :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count → List Bool
  | _, _, _, .nil _ _ => []
  | _, _, _, .step head tail =>
      head.application.output.1 head.schedule.entry.var :: tail.executedBits

/-- Every retained bit is read as `true` from the corresponding applied output. -/
theorem SequentialHistory.readout_preserved
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    history.executedVariables.map history.final.assignment = history.executedBits := by
  induction history with
  | nil => rfl
  | @step depth count input head tail ih =>
    change tail.final.assignment head.schedule.entry.var ::
      tail.executedVariables.map tail.final.assignment =
      head.application.output.1 head.schedule.entry.var :: tail.executedBits
    rw [ih]
    have below : head.schedule.entry.var < stageSelectedVar (depth + 1 + 1) := by
      rw [sequentialStage_selected_exact]
      exact stageSelectedVar_strict (Nat.lt_succ_self (depth + 1))
    rw [tail.preserves_below _ below, head.nextAssignmentExact]

theorem executedHistory_bits_exact
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).executedBits =
      List.replicate count true := by
  induction count generalizing startDepth input with
  | zero =>
      rw [
        executeSequentialHistory,
        SequentialHistory.executedBits
      ]
      rfl
  | succ count inductionHypothesis =>
      let head := executeSequentialStage startDepth input
      have selected :
          head.schedule.entry.var = stageSelectedVar (startDepth + 1) := by
        change
          (canonicalStageDiscovery (startDepth + 1)).var =
            stageSelectedVar (startDepth + 1)
        exact canonicalStageDiscovery_var (startDepth + 1)
      have headBit :
          head.application.output.1 head.schedule.entry.var = true := by
        rw [selected]
        exact executeSequentialStage_output_selected startDepth input
      rw [
        executeSequentialHistory,
        SequentialHistory.executedBits
      ]
      change
        head.application.output.1 head.schedule.entry.var ::
            (executeSequentialHistory
              (startDepth + 1)
              count
              head.next).executedBits =
          List.replicate (count + 1) true
      rw [headBit, inductionHypothesis, List.replicate_succ]

theorem executedHistory_bits_length
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).executedBits.length =
      count := by
  induction count generalizing startDepth input with
  | zero =>
      rw [executeSequentialHistory, SequentialHistory.executedBits]
      rfl
  | succ count inductionHypothesis =>
      rw [executeSequentialHistory, SequentialHistory.executedBits]
      change
        (executeSequentialHistory
          (startDepth + 1)
          count
          (executeSequentialStage startDepth input).next).executedBits.length + 1 =
            count + 1
      rw [inductionHypothesis]

/-- Full accounting obtained by folding stored per-stage run statistics. -/
structure SequentialHistoryStats where
  generateCalls : Nat
  generatedSteps : Nat
  provenanceUnits : Nat
  generationCertificates : Nat
  extractionClauseVisits : Nat
  extractionLiteralVisits : Nat
  extractedCandidates : Nat
  testedCandidates : Nat
  discoveryAttempts : Nat
  candidateConstructions : Nat
  variableComparisonUnits : Nat
  formulaComparisonLiteralVisits : Nat
  historyComparisonDecisionVisits : Nat
  relationQueries : Nat
  scheduleAtoms : Nat
  validatedAtoms : Nat
  validationPrimitiveQueries : Nat
  executionPrimitiveQueries : Nat
  compositionCandidates : Nat
  appliedCodeAtoms : Nat
  continuationApplications : Nat
  deriving DecidableEq, Repr

/-- Empty accounting record. -/
def SequentialHistoryStats.zero : SequentialHistoryStats :=
  { generateCalls := 0
    generatedSteps := 0
    provenanceUnits := 0
    generationCertificates := 0
    extractionClauseVisits := 0
    extractionLiteralVisits := 0
    extractedCandidates := 0
    testedCandidates := 0
    discoveryAttempts := 0
    candidateConstructions := 0
    variableComparisonUnits := 0
    formulaComparisonLiteralVisits := 0
    historyComparisonDecisionVisits := 0
    relationQueries := 0
    scheduleAtoms := 0
    validatedAtoms := 0
    validationPrimitiveQueries := 0
    executionPrimitiveQueries := 0
    compositionCandidates := 0
    appliedCodeAtoms := 0
    continuationApplications := 0 }

/-- Add one actually executed stage to an accumulated trace record. -/
def SequentialHistoryStats.addStage
    (tail : SequentialHistoryStats)
    (head : SequentialStageStats) : SequentialHistoryStats :=
  { generateCalls := tail.generateCalls + head.generateCalls
    generatedSteps := tail.generatedSteps + head.generatedSteps
    provenanceUnits := tail.provenanceUnits + head.provenanceUnits
    generationCertificates :=
      tail.generationCertificates + head.generationCertificates
    extractionClauseVisits :=
      tail.extractionClauseVisits + head.extractionClauseVisits
    extractionLiteralVisits :=
      tail.extractionLiteralVisits + head.extractionLiteralVisits
    extractedCandidates :=
      tail.extractedCandidates + head.extractedCandidates
    testedCandidates := tail.testedCandidates + head.testedCandidates
    discoveryAttempts := tail.discoveryAttempts + head.discoveryAttempts
    candidateConstructions :=
      tail.candidateConstructions + head.candidateConstructions
    variableComparisonUnits :=
      tail.variableComparisonUnits + head.variableComparisonUnits
    formulaComparisonLiteralVisits :=
      tail.formulaComparisonLiteralVisits +
        head.formulaComparisonLiteralVisits
    historyComparisonDecisionVisits :=
      tail.historyComparisonDecisionVisits +
        head.historyComparisonDecisionVisits
    relationQueries := tail.relationQueries + head.relationQueries
    scheduleAtoms := tail.scheduleAtoms + head.scheduleAtoms
    validatedAtoms := tail.validatedAtoms + head.validatedAtoms
    validationPrimitiveQueries :=
      tail.validationPrimitiveQueries + head.validationPrimitiveQueries
    executionPrimitiveQueries :=
      tail.executionPrimitiveQueries + head.executionPrimitiveQueries
    compositionCandidates :=
      tail.compositionCandidates + head.compositionCandidates
    appliedCodeAtoms := tail.appliedCodeAtoms + head.appliedCodeAtoms
    continuationApplications :=
      tail.continuationApplications + head.continuationApplications }

/-- Fold costs from the concrete stored stages. -/
def SequentialHistory.stats :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count →
          SequentialHistoryStats
  | _, _, _, .nil _ _ => SequentialHistoryStats.zero
  | _, _, _, .step head tail => tail.stats.addStage head.stats

/--
Measured freshness, formula/history transformation and comparison work folded
from the stored discovery runs. Endpoint construction and later phases are
not included in this partial counter.
-/
def SequentialHistory.measuredComparisonWork :
    {depth count : Nat} → {input : SequentialAssignment depth} →
      SequentialHistory depth input count → ComparisonWork
  | _, _, _, .nil _ _ => .zero
  | _, _, _, .step head tail =>
    head.discoveryRun.outcome.comparisonWork.add tail.measuredComparisonWork

def SequentialHistory.structuralProfileCost :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count → Nat
  | _, _, _, .nil _ _ => 0
  | _, _, _, .step head tail =>
      tail.structuralProfileCost + head.stats.total

/-- Work of the actual residual and endpoint construction inside discovery. -/
def SequentialHistory.measuredConstructionWork :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
        SequentialHistory startDepth input count → ComparisonWork
  | _, _, _, .nil _ _ => .zero
  | _, _, _, .step head tail =>
      head.discoveryRun.outcome.constructionWork.add tail.measuredConstructionWork

/-- Fold the work of the validators actually retained in the executed stages. -/
def SequentialHistory.measuredValidationWork :
    {depth count : Nat} → {input : SequentialAssignment depth} →
      SequentialHistory depth input count → ComparisonWork
  | _, _, _, .nil _ _ => .zero
  | _, _, _, .step head tail =>
    head.measuredValidation.search.work.add tail.measuredValidationWork

def SequentialHistory.measuredExecutionWork :
    {depth count : Nat} → {input : SequentialAssignment depth} →
      SequentialHistory depth input count → ComparisonWork
  | _, _, _, .nil _ _ => .zero
  | _, _, _, .step head tail =>
    head.measuredExecution.search.work.add tail.measuredExecutionWork

/-- Terminal fold with a visit counter emitted by the same recursion. -/
structure TerminalReadoutRun where
  decision : Bool
  bitVisits : Nat
  deriving DecidableEq, Repr

def runTerminalReadout : List Bool → TerminalReadoutRun
  | [] => { decision := false, bitVisits := 0 }
  | false :: rest =>
      let tail := runTerminalReadout rest
      { decision := tail.decision
        bitVisits := tail.bitVisits + 1 }
  | true :: rest =>
      let tail := runTerminalReadout rest
      { decision := !tail.decision
        bitVisits := tail.bitVisits + 1 }

/--
Legacy structural profile, plus terminal list visits. Measured comparison
work is exposed separately; this value is not complete executed cost.
-/
def SequentialHistory.totalStructuralProfileCost
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (history : SequentialHistory startDepth input count) : Nat :=
  history.structuralProfileCost +
    (runTerminalReadout history.executedBits).bitVisits + 1

/-- Disjoint top-level accounting: stage recursion, terminal fold, final observation. -/
structure ResolutionPhaseAccounting where
  stageWork : Nat
  terminalBitVisits : Nat
  finalObservation : Nat
  deriving DecidableEq, Repr

def ResolutionPhaseAccounting.total
    (accounting : ResolutionPhaseAccounting) : Nat :=
  accounting.stageWork + accounting.terminalBitVisits + accounting.finalObservation

def SequentialHistory.phaseAccounting
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (history : SequentialHistory startDepth input count) :
    ResolutionPhaseAccounting :=
  { stageWork := history.structuralProfileCost
    terminalBitVisits := (runTerminalReadout history.executedBits).bitVisits
    finalObservation := 1 }

/-- Arithmetic equality of the profile partition; not a no-double-count proof. -/
theorem SequentialHistory.phaseAccounting_exact
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (history : SequentialHistory startDepth input count) :
    history.phaseAccounting.total = history.totalStructuralProfileCost :=
  rfl

/-- Canonical legacy surface; its aggregate components are not disjoint events. -/
def SequentialHistoryStats.total (stats : SequentialHistoryStats) : Nat :=
  stats.generateCalls +
    stats.generatedSteps +
    stats.provenanceUnits +
    stats.generationCertificates +
    stats.extractionClauseVisits +
    stats.extractionLiteralVisits +
    stats.extractedCandidates +
    stats.testedCandidates +
    stats.discoveryAttempts +
    stats.candidateConstructions +
    stats.variableComparisonUnits +
    stats.formulaComparisonLiteralVisits +
    stats.historyComparisonDecisionVisits +
    stats.relationQueries +
    stats.scheduleAtoms +
    stats.validatedAtoms +
    stats.validationPrimitiveQueries +
    stats.executionPrimitiveQueries +
    stats.compositionCandidates +
    stats.appliedCodeAtoms +
    stats.continuationApplications

theorem executedHistory_generatedSteps
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.generatedSteps =
      count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.generatedSteps + 1 =
          count + 1
      rw [inductionHypothesis]

theorem executedHistory_generateCalls
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.generateCalls =
      count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.generateCalls +
            (executeSequentialStage startDepth input).stats.generateCalls =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_generationStats startDepth input).1
      ]

theorem executedHistory_provenanceUnits
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.provenanceUnits =
      count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.provenanceUnits +
            (executeSequentialStage startDepth input).stats.provenanceUnits =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_generationStats startDepth input).2.2.1
      ]

theorem executedHistory_generationCertificates
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
        startDepth count input).stats.generationCertificates = count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.generationCertificates +
            (executeSequentialStage startDepth input).stats.generationCertificates =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_generationStats startDepth input).2.2.2
      ]

theorem executedHistory_scheduleAtoms
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.scheduleAtoms =
      count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.scheduleAtoms +
            (executeSequentialStage startDepth input).stats.scheduleAtoms =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_localStats startDepth input).1
      ]

theorem executedHistory_validationQueries
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
      startDepth count input).stats.validationPrimitiveQueries = count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.validationPrimitiveQueries +
            (executeSequentialStage startDepth input).stats.validationPrimitiveQueries =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_localStats startDepth input).2.1
      ]

theorem executedHistory_executionQueries
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
      startDepth count input).stats.executionPrimitiveQueries = count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.executionPrimitiveQueries +
            (executeSequentialStage startDepth input).stats.executionPrimitiveQueries =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_localStats startDepth input).2.2.1
      ]

theorem executedHistory_compositionCandidates
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
      startDepth count input).stats.compositionCandidates = 0 := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.compositionCandidates +
            (executeSequentialStage startDepth input).stats.compositionCandidates = 0
      rw [
        inductionHypothesis,
        (executeSequentialStage_localStats startDepth input).2.2.2.1
      ]

theorem executedHistory_appliedAtoms
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.appliedCodeAtoms =
      count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.appliedCodeAtoms +
            (executeSequentialStage startDepth input).stats.appliedCodeAtoms =
          count + 1
      rw [
        inductionHypothesis,
        (executeSequentialStage_localStats startDepth input).2.2.2.2
      ]

theorem executedHistory_continuationApplications
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory
      startDepth count input).stats.continuationApplications = count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            (executeSequentialStage startDepth input).next).stats.continuationApplications +
            (executeSequentialStage startDepth input).stats.continuationApplications =
          count + 1
      rw [inductionHypothesis,
        executeSequentialStage_continuationApplications startDepth input]

/-- The trace-level tested list accounting equals the charged attempt count. -/
theorem executedHistory_testedCandidates
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.testedCandidates =
      (executeSequentialHistory startDepth count input).stats.discoveryAttempts := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
              (startDepth + 1)
              count
              (executeSequentialStage startDepth input).next).stats.testedCandidates +
            (executeSequentialStage startDepth input).stats.testedCandidates =
          (executeSequentialHistory
              (startDepth + 1)
              count
              (executeSequentialStage startDepth input).next).stats.discoveryAttempts +
            (executeSequentialStage startDepth input).stats.discoveryAttempts
      rw [
        inductionHypothesis,
        executeSequentialStage_testedCandidates
      ]

/-- Every local relation query is emitted by one charged discovery attempt. -/
theorem executedHistory_relationQueries
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.relationQueries =
      (executeSequentialHistory startDepth count input).stats.discoveryAttempts := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
              (startDepth + 1)
              count
              (executeSequentialStage startDepth input).next).stats.relationQueries +
            (executeSequentialStage startDepth input).stats.relationQueries =
          (executeSequentialHistory
              (startDepth + 1)
              count
              (executeSequentialStage startDepth input).next).stats.discoveryAttempts +
            (executeSequentialStage startDepth input).stats.discoveryAttempts
      rw [
        inductionHypothesis,
        (executeSequentialStage_detailedDiscoveryStats startDepth input).2.2.2.2,
        executeSequentialStage_attempts
      ]

theorem executedHistory_extractedCandidates_eq_literalVisits
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.extractedCandidates =
      (executeSequentialHistory startDepth count input).stats.extractionLiteralVisits := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
              (startDepth + 1) count
              (executeSequentialStage startDepth input).next).stats.extractedCandidates +
            (executeSequentialStage startDepth input).stats.extractedCandidates =
          (executeSequentialHistory
              (startDepth + 1) count
              (executeSequentialStage startDepth input).next).stats.extractionLiteralVisits +
            (executeSequentialStage startDepth input).stats.extractionLiteralVisits
      rw [inductionHypothesis, executeSequentialStage_extractedCandidates,
        (executeSequentialStage_extractionStats startDepth input).2]

theorem executedHistory_validatedAtoms
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).stats.validatedAtoms = count := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (executeSequentialHistory
              (startDepth + 1) count
              (executeSequentialStage startDepth input).next).stats.validatedAtoms +
            (executeSequentialStage startDepth input).stats.validatedAtoms =
          count + 1
      rw [inductionHypothesis, executeSequentialStage_validatedAtoms]

/--
Attempt count of the executed stage sequence, with its actual increasing depths.
-/
def historyAttemptCount (depth : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => historyAttemptCount (depth + 1) count + (2 * depth + 10)

theorem executedHistory_attemptCount
    (depth count : Nat) (input : SequentialAssignment depth) :
    (executeSequentialHistory depth count input).stats.discoveryAttempts =
      historyAttemptCount depth count := by
  induction count generalizing depth input with
  | zero => rfl
  | succ count ih =>
    change (executeSequentialHistory (depth + 1) count
      (executeSequentialStage depth input).next).stats.discoveryAttempts +
      (executeSequentialStage depth input).stats.discoveryAttempts = _
    rw [ih, executeSequentialStage_attempts]
    rfl

theorem historyAttemptCount_depth_mono {first second : Nat}
    (ordered : first ≤ second) (count : Nat) :
    historyAttemptCount first count ≤ historyAttemptCount second count := by
  induction count generalizing first second with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
    exact Nat.add_le_add (ih (Nat.add_le_add_right ordered 1))
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ordered) 10)

theorem historyAttemptCount_integrated_strict (input : Nat) :
    historyAttemptCount input (input + 1) <
      historyAttemptCount (input + 1) (input + 2) := by
  change historyAttemptCount input (input + 1) <
    historyAttemptCount (input + 1 + 1) (input + 1) + (2 * (input + 1) + 10)
  have lower := historyAttemptCount_depth_mono
    (Nat.le_add_right input 2) (input + 1)
  have positive : 0 < 2 * (input + 1) + 10 := Nat.zero_lt_succ _
  exact Nat.lt_of_le_of_lt lower (Nat.lt_add_of_pos_right positive)

theorem historyAttemptCount_le (depth count : Nat) :
    historyAttemptCount depth count ≤ count * (2 * (depth + count) + 10) := by
  induction count generalizing depth with
  | zero =>
      rw [historyAttemptCount, Nat.zero_mul]
      exact Nat.le_refl 0
  | succ count inductionHypothesis =>
      change
        historyAttemptCount (depth + 1) count + (2 * depth + 10) ≤
          (count + 1) * (2 * (depth + (count + 1)) + 10)
      have endpoint : depth + 1 + count = depth + (count + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 count]
      have tail := inductionHypothesis (depth + 1)
      rw [endpoint] at tail
      have head : 2 * depth + 10 ≤ 2 * (depth + (count + 1)) + 10 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left 2 (Nat.le_add_right depth (count + 1))) 10
      exact Nat.le_trans (Nat.add_le_add tail head)
        (Nat.le_of_eq
          (Nat.succ_mul count (2 * (depth + (count + 1)) + 10)).symm)

theorem executedHistory_attempts_le
    (depth count : Nat) (input : SequentialAssignment depth) :
    (executeSequentialHistory depth count input).stats.discoveryAttempts ≤
      count * (2 * (depth + count) + 10) := by
  rw [executedHistory_attemptCount]
  exact historyAttemptCount_le depth count

theorem executedHistory_relationQueries_le
    (depth count : Nat) (input : SequentialAssignment depth) :
    (executeSequentialHistory depth count input).stats.relationQueries ≤
      count * (2 * (depth + count) + 10) := by
  rw [executedHistory_relationQueries]
  exact executedHistory_attempts_le depth count input

theorem executedHistory_cost_le
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (executeSequentialHistory startDepth count input).structuralProfileCost ≤
      count * sequentialStageSurfacePolynomial.eval (startDepth + count) := by
  induction count generalizing startDepth input with
  | zero =>
      rw [executeSequentialHistory]
      rw [SequentialHistory.structuralProfileCost, Nat.zero_mul]
      exact Nat.le_refl 0
  | succ count inductionHypothesis =>
      let head := executeSequentialStage startDepth input
      have tailBound :=
        inductionHypothesis
          (startDepth + 1)
          head.next
      have endpointExact :
          startDepth + 1 + count = startDepth + (count + 1) := by
        calc
          startDepth + 1 + count = startDepth + (1 + count) :=
            Nat.add_assoc startDepth 1 count
          _ = startDepth + (count + 1) :=
            congrArg
              (fun value => startDepth + value)
              (Nat.add_comm 1 count)
      rw [endpointExact] at tailBound
      have headBound :
          sequentialStageSurfacePolynomial.eval startDepth ≤
            sequentialStageSurfacePolynomial.eval
              (startDepth + (count + 1)) :=
        sequentialStageSurfacePolynomial.eval_mono
          (Nat.le_add_right startDepth (count + 1))
      change
        (executeSequentialHistory
            (startDepth + 1)
            count
            head.next).structuralProfileCost +
              head.stats.total ≤
          (count + 1) *
            sequentialStageSurfacePolynomial.eval
              (startDepth + (count + 1))
      rw [executeSequentialStage_total]
      exact
        Nat.le_trans
          (Nat.add_le_add tailBound headBound)
          (Nat.le_of_eq
            (Nat.succ_mul
              count
              (sequentialStageSurfacePolynomial.eval
                (startDepth + (count + 1)))).symm)

/-- Last stage depth of a nonempty trace with `count + 1` steps. -/
def lastStageDepth (startDepth count : Nat) : Nat :=
  advancedDepth startDepth count

/-- Alternating decision signal computed from completed execution work. -/
def alternatingExecutionDecision : Nat → Bool
  | 0 => false
  | count + 1 => !(alternatingExecutionDecision count)

/-- Parity read from concrete Boolean values retained by the final assignment. -/
def transportedBitParity : List Bool → Bool
  | [] => false
  | false :: rest => transportedBitParity rest
  | true :: rest => !(transportedBitParity rest)

theorem runTerminalReadout_decision (bits : List Bool) :
    (runTerminalReadout bits).decision = transportedBitParity bits := by
  induction bits with
  | nil => rfl
  | cons bit rest inductionHypothesis =>
      cases bit <;>
        rw [runTerminalReadout, transportedBitParity, inductionHypothesis]

theorem runTerminalReadout_visits (bits : List Bool) :
    (runTerminalReadout bits).bitVisits = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest inductionHypothesis =>
      cases bit <;>
        change (runTerminalReadout rest).bitVisits + 1 = rest.length + 1 <;>
        rw [inductionHypothesis]

theorem transportedBitParity_true_replicate (count : Nat) :
    transportedBitParity (List.replicate count true) =
      alternatingExecutionDecision count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ]
      change
        (!(transportedBitParity (List.replicate count true))) =
          (!(alternatingExecutionDecision count))
      rw [inductionHypothesis]

structure LastExecutedVariableRun where
  result : Option Var
  visits : Nat

/-- Recover the observed variable from stored discoveries, with traversal visits. -/
def SequentialHistory.lastVariableRun : {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → LastExecutedVariableRun
  | _, _, _, .nil _ _ => ⟨none, 1⟩
  | _, _, _, .step head tail =>
    let prior := tail.lastVariableRun
    ⟨match prior.result with
      | none => some head.schedule.entry.var
      | some selected => some selected,
      prior.visits + 1⟩

/-- Reference only; the executable accessor above never uses this index formula. -/
def expectedLastVariable : Nat → Nat → Option Var
  | _, 0 => none
  | depth, count + 1 =>
    match expectedLastVariable (depth + 1) count with
    | none => some (stageSelectedVar (depth + 1))
    | some selected => some selected

theorem SequentialHistory.lastVariableRun_exact {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    history.lastVariableRun.result = expectedLastVariable depth count := by
  induction history with
  | nil => rfl
  | step head tail ih =>
    change (match tail.lastVariableRun.result with
      | none => some head.schedule.entry.var
      | some selected => some selected) = _
    rw [ih, sequentialStage_selected_exact head]
    rfl

theorem expectedLastVariable_nonempty (depth count : Nat) :
    expectedLastVariable depth (count + 1) = some (stageSelectedVar (lastStageDepth depth count + 1)) := by
  induction count generalizing depth with
  | zero => rfl
  | succ count ih =>
    change (match expectedLastVariable (depth + 1) (count + 1) with
      | none => some (stageSelectedVar (depth + 1))
      | some selected => some selected) = _
    rw [ih]
    rfl

theorem SequentialHistory.lastVariableRun_visits {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) : history.lastVariableRun.visits = count + 1 := by
  induction history with
  | nil => rfl
  | step head tail ih => exact congrArg (fun n => n + 1) ih

def LastExecutedVariableRun.get (run : LastExecutedVariableRun) (success : run.result ≠ none) : Var :=
  match found : run.result with
  | none => False.elim (success found)
  | some selected => selected

theorem LastExecutedVariableRun.get_exact (run : LastExecutedVariableRun) (success : run.result ≠ none) :
    run.result = some (run.get success) := by
  unfold LastExecutedVariableRun.get
  split
  · rename_i failed; exact False.elim (success failed)
  · rename_i selected found; exact found

/-- Terminal data are constructed only from the final threaded assignment. -/
structure SequentialTerminalArtifact
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (history : SequentialHistory startDepth input (count + 1)) where
  assignment : Assignment
  observedVar : Var
  variableReadout : LastExecutedVariableRun
  variableReadoutExact : variableReadout = history.lastVariableRun
  observedVarFromReadout : variableReadout.result = some observedVar
  bitRead : MeasuredValue (assignment observedVar)
  bit : Bool
  executedAtoms : Nat
  executedVariables : List Var
  assignmentReadout : MeasuredAssignmentReadout (assignment := assignment) executedVariables
  observedBits : List Bool
  readoutRun : TerminalReadoutRun
  decisionBit : Bool
  assignmentExact : assignment = history.final.assignment
  observedVarExact :
    observedVar = stageSelectedVar (lastStageDepth startDepth count + 1)
  bitExact : bit = assignment observedVar
  bitFromRead : bit = bitRead.value
  executedAtomsExact : executedAtoms = history.stats.appliedCodeAtoms
  executedVariablesExact : executedVariables = history.executedVariables
  assignmentReadoutExact : HEq assignmentReadout
    (readAssignmentQueries history.final.reader history.executedVariables)
  observedBitsFromReadout : observedBits = assignmentReadout.bits
  observedBitsExact : observedBits = history.executedBits
  readoutRunExact : readoutRun = runTerminalReadout observedBits
  decisionBitExact : decisionBit = readoutRun.decision

/-- Build the terminal by reading the final assignment of a completed trace. -/
def terminalFromSequentialHistory
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (history : SequentialHistory startDepth input (count + 1)) :
    SequentialTerminalArtifact history :=
  let queried := readAssignmentQueries history.final.reader history.executedVariables
  let readout := runTerminalReadout queried.bits
  let variableReadout := history.lastVariableRun
  have variableExact : variableReadout.result =
      some (stageSelectedVar (lastStageDepth startDepth count + 1)) :=
    Eq.trans history.lastVariableRun_exact (expectedLastVariable_nonempty startDepth count)
  have variableFound : variableReadout.result ≠ none := by
    rw [variableExact]; intro impossible; cases impossible
  let observedVar := variableReadout.get variableFound
  have observedExact : observedVar = stageSelectedVar (lastStageDepth startDepth count + 1) :=
    Option.some.inj (Eq.trans (variableReadout.get_exact variableFound).symm variableExact)
  let bitRead := history.final.reader observedVar
  { assignment := history.final.assignment
    observedVar := observedVar
    variableReadout := variableReadout
    variableReadoutExact := rfl
    observedVarFromReadout := variableReadout.get_exact variableFound
    bitRead := bitRead
    bit := bitRead.value
    executedAtoms := history.stats.appliedCodeAtoms
    executedVariables := history.executedVariables
    assignmentReadout := queried
    observedBits := queried.bits
    readoutRun := readout
    decisionBit := readout.decision
    assignmentExact := rfl
    observedVarExact := observedExact
    bitExact := bitRead.valueExact
    bitFromRead := rfl
    executedAtomsExact := rfl
    executedVariablesExact := rfl
    assignmentReadoutExact := HEq.rfl
    observedBitsFromReadout := rfl
    observedBitsExact := Eq.trans queried.bitsExact history.readout_preserved
    readoutRunExact := rfl
    decisionBitExact := rfl }

/-- Decision consumes the terminal artifact and no earlier input or state. -/
def decideSequentialTerminal
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    {history : SequentialHistory startDepth input (count + 1)}
    (terminal : SequentialTerminalArtifact history) : Bool :=
  terminal.decisionBit

/-- The final selected assignment bit of every nonempty execution is produced true. -/
theorem executedHistory_selectedBit_true
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    (terminalFromSequentialHistory
      (executeSequentialHistory startDepth (count + 1) input)).bit =
      true := by
  rw [(terminalFromSequentialHistory
    (executeSequentialHistory startDepth (count + 1) input)).bitExact]
  rw [(terminalFromSequentialHistory
    (executeSequentialHistory startDepth (count + 1) input)).observedVarExact]
  change (executeSequentialHistory startDepth (count + 1) input).final.assignment
    (stageSelectedVar (lastStageDepth startDepth count + 1)) = true
  induction count generalizing startDepth input with
  | zero =>
      rw [executeSequentialHistory]
      change
        (executeSequentialStage startDepth input).next.assignment
            (stageSelectedVar (startDepth + 1)) = true
      rw [executeSequentialStage_threads_output]
      exact executeSequentialStage_output_selected startDepth input
  | succ count inductionHypothesis =>
      rw [executeSequentialHistory]
      change
        (executeSequentialHistory
          (startDepth + 1) (count + 1)
          (executeSequentialStage startDepth input).next).final.assignment
          (stageSelectedVar (lastStageDepth (startDepth + 1) count + 1)) = true
      exact
        inductionHypothesis
          (startDepth + 1)
          (executeSequentialStage startDepth input).next

/-- Decision is computed from executed trace work retained in the terminal. -/
theorem executedHistory_decision_exact
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    decideSequentialTerminal
        (terminalFromSequentialHistory
          (executeSequentialHistory startDepth (count + 1) input)) =
      alternatingExecutionDecision (count + 1) := by
  change (runTerminalReadout
    (readAssignmentQueries
      (executeSequentialHistory startDepth (count + 1) input).final.reader
      (executeSequentialHistory startDepth (count + 1) input).executedVariables).bits).decision = _
  rw [(readAssignmentQueries
    (executeSequentialHistory startDepth (count + 1) input).final.reader
    (executeSequentialHistory startDepth (count + 1) input).executedVariables).bitsExact]
  change
    (runTerminalReadout
        ((executeSequentialHistory startDepth (count + 1) input).executedVariables.map
          (executeSequentialHistory startDepth (count + 1) input).final.assignment)).decision =
      alternatingExecutionDecision (count + 1)
  rw [
    SequentialHistory.readout_preserved,
    runTerminalReadout_decision,
    executedHistory_bits_exact,
    transportedBitParity_true_replicate
  ]

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.lastVariableRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.lastVariableRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.lastVariableRun_visits
#print axioms ConstitutiveSearch.EndogenousDecomposition.expectedLastVariable_nonempty
#print axioms ConstitutiveSearch.EndogenousDecomposition.LastExecutedVariableRun.get
#print axioms ConstitutiveSearch.EndogenousDecomposition.LastExecutedVariableRun.get_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.terminalFromSequentialHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.measuredValidationWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.measuredExecutionWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.measuredConstructionWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.measuredComparisonWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.preserves_below
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.readout_preserved
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_attemptCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyAttemptCount_depth_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyAttemptCount_integrated_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.final
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.executedVariables
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.executedBits
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.structuralProfileCost
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.totalStructuralProfileCost
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.phaseAccounting
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.phaseAccounting_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_variables_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_preserves_below
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_bits_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_bits_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_generatedSteps
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_generateCalls
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_provenanceUnits
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_generationCertificates
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_validationQueries
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_executionQueries
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_compositionCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_appliedAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_testedCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_relationQueries
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_extractedCandidates_eq_literalVisits
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_validatedAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyAttemptCount_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_attempts_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_relationQueries_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_cost_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.terminalFromSequentialHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.transportedBitParity
#print axioms ConstitutiveSearch.EndogenousDecomposition.runTerminalReadout
#print axioms ConstitutiveSearch.EndogenousDecomposition.runTerminalReadout_decision
#print axioms ConstitutiveSearch.EndogenousDecomposition.runTerminalReadout_visits
#print axioms ConstitutiveSearch.EndogenousDecomposition.decideSequentialTerminal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_selectedBit_true
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_decision_exact
/- AXIOM_AUDIT_END -/
