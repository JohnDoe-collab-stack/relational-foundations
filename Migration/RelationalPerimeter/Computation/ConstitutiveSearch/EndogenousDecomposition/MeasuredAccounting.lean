import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolution

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Exclusive owners of the instrumented operations. Output-size indicators
and the legacy structural profile are not additional execution phases. -/
inductive MeasuredPhase where
  | production
  | generationMaterialization
  | realization
  | extraction
  | extractedCandidates
  | discovery
  | candidateTests
  | relationQueries
  | schedule
  | validationSearch
  | validatedAtoms
  | validationQueries
  | executionSearch
  | executionQueries
  | codeApplication
  | decisionAccumulation
  | decisionProvenance
  | historyFiltering
  | terminal
  | projection
  deriving DecidableEq, Repr

def measuredPhases : List MeasuredPhase :=
  [.production, .realization, .extraction, .discovery, .validationSearch,
    .executionSearch, .terminal, .generationMaterialization, .schedule,
    .validationQueries, .executionQueries, .codeApplication,
    .extractedCandidates, .candidateTests, .relationQueries, .validatedAtoms,
    .decisionAccumulation, .decisionProvenance, .historyFiltering,
    .projection]

def phaseOccurrences (phase : MeasuredPhase) : List MeasuredPhase → Nat
  | [] => 0
  | head :: tail => (if phase = head then 1 else 0) + phaseOccurrences phase tail

theorem measuredPhase_occurs_once (phase : MeasuredPhase) :
    phaseOccurrences phase measuredPhases = 1 := by
  cases phase <;> decide

/-- Representation work emitted by the recursive generators themselves. This
is separate from invoking `generate`: the appended step, provenance unit,
certificate and initial perimeter deployment are all material outputs. -/
def ConstitutiveResolutionRun.generationMaterializationWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  (((run.initialization.appendedSteps + run.initialization.provenanceUnits) +
      run.initialization.certificatesProduced) + run.initialization.perimeterDeployments) +
    ((run.production.appendedSteps + run.production.provenanceUnits) +
      run.production.certificatesProduced)

/-- Control operations already emitted by the stage/history runs, but not part
of the comparison-work counters. -/
def ConstitutiveResolutionRun.scheduleWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.scheduleAtoms

def ConstitutiveResolutionRun.validationQueryWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.validationPrimitiveQueries

def ConstitutiveResolutionRun.extractedCandidateWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.extractedCandidates

/-- One owner for candidate-loop control. `testedCandidates` is the retained
trace length and is proved equal to this emitted attempt count; it is not added
a second time. -/
def ConstitutiveResolutionRun.candidateTestWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.discoveryAttempts

def ConstitutiveResolutionRun.relationQueryWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.relationQueries

def ConstitutiveResolutionRun.validatedAtomWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat := run.stats.validatedAtoms

def ConstitutiveResolutionRun.executionQueryWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.stats.executionPrimitiveQueries + run.stats.compositionCandidates

def ConstitutiveResolutionRun.codeApplicationWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.stats.appliedCodeAtoms + run.stats.continuationApplications

/-- New feedback operations have their own producers.  Realization,
state-dependent extraction and next discovery remain charged by their existing
phases, so the transmitted-state ledger introduces no duplicate charge. -/
def ConstitutiveResolutionRun.decisionAccumulationWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.feedbackStats.decisionAccumulations

def ConstitutiveResolutionRun.decisionProvenanceWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.feedbackStats.provenanceVisits

def ConstitutiveResolutionRun.historyFilteringWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.feedbackStats.historyFilteringVisits

/-- The shared source is constructed once. The two finder/interpreter calls
belong to different executions and both contribute their emitted work. -/
def IntegratedProjectionExperiment.measuredWork {depth : Nat} {input : SequentialAssignment depth}
    {stage : SequentialStageRun depth input} (experiment : IntegratedProjectionExperiment stage) : Nat :=
  experiment.constructionWork.total +
    (experiment.positiveRun.queryWork.total + experiment.positiveRun.readWork.total) +
    (experiment.negativeRun.queryWork.total + experiment.negativeRun.readWork.total)

/-- Project only counters produced by the run. This ledger covers instrumented
operations; it does not silently declare uninstrumented driver work free. -/
def ConstitutiveResolutionRun.phaseWork {input : Nat} (run : ConstitutiveResolutionRun input) :
    MeasuredPhase → Nat
  | .production => run.productionCalls
  | .generationMaterialization => run.generationMaterializationWork
  | .realization => run.measuredRealizationWork.total
  | .extraction => run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits
  | .extractedCandidates => run.extractedCandidateWork
  | .discovery => (run.measuredComparisonWork.add run.measuredConstructionWork).total
  | .candidateTests => run.candidateTestWork
  | .relationQueries => run.relationQueryWork
  | .schedule => run.scheduleWork
  | .validationSearch => run.measuredValidationWork.total
  | .validatedAtoms => run.validatedAtomWork
  | .validationQueries => run.validationQueryWork
  | .executionSearch => run.measuredExecutionWork.total
  | .executionQueries => run.executionQueryWork
  | .codeApplication => run.codeApplicationWork
  | .decisionAccumulation => run.decisionAccumulationWork
  | .decisionProvenance => run.decisionProvenanceWork
  | .historyFiltering => run.historyFilteringWork
  | .terminal => run.terminal.measuredReadWork
  | .projection => run.projectionExperiment.measuredWork

def sumPhaseWork (work : MeasuredPhase → Nat) : List MeasuredPhase → Nat
  | [] => 0
  | phase :: tail => work phase + sumPhaseWork work tail

def ConstitutiveResolutionRun.instrumentedWork {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  sumPhaseWork run.phaseWork measuredPhases

/-- No freely supplied cost can replace the canonical ledger. -/
structure CanonicalMeasuredAccounting (input : Nat) where
  phaseWork : MeasuredPhase → Nat
  phaseWorkExact : phaseWork = (executeConstitutiveResolution input).phaseWork
  total : Nat
  totalExact : total = sumPhaseWork phaseWork measuredPhases

def canonicalMeasuredAccounting (input : Nat) : CanonicalMeasuredAccounting input :=
  let run := executeConstitutiveResolution input
  ⟨run.phaseWork, rfl, run.instrumentedWork, rfl⟩

theorem CanonicalMeasuredAccounting.total_is_canonical {input : Nat}
    (accounting : CanonicalMeasuredAccounting input) :
    accounting.total = (executeConstitutiveResolution input).instrumentedWork := by
  rw [accounting.totalExact, accounting.phaseWorkExact]
  rfl

theorem canonicalMeasuredAccounting_not_inflatable {input : Nat}
    (first second : CanonicalMeasuredAccounting input) : first.total = second.total :=
  Eq.trans first.total_is_canonical second.total_is_canonical.symm

theorem discoveryWork_does_not_add_legacy_surface {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.phaseWork .discovery = run.measuredComparisonWork.total + run.measuredConstructionWork.total :=
  ComparisonWork.total_add _ _

theorem projectionWork_shared_source_once {depth : Nat} {input : SequentialAssignment depth}
    {stage : SequentialStageRun depth input} (experiment : IntegratedProjectionExperiment stage) :
    experiment.measuredWork =
      ((experiment.source.work.total + experiment.positiveTarget.work.total) + experiment.negativeTarget.work.total) +
        (experiment.positiveRun.queryWork.total + experiment.positiveRun.readWork.total) +
        (experiment.negativeRun.queryWork.total + experiment.negativeRun.readWork.total) := by
  unfold IntegratedProjectionExperiment.measuredWork
  rw [experiment.constructionWorkExact, ComparisonWork.total_add, ComparisonWork.total_add]

def stageExtractionEnvelope (depth : Nat) : Nat :=
  growingFormulaSizeEnvelope (2 * (depth + 3))

theorem stageExtractionEnvelope_mono {first second : Nat} (before : first ≤ second) :
    stageExtractionEnvelope first ≤ stageExtractionEnvelope second :=
  growingFormulaSizeEnvelope_mono (Nat.mul_le_mul_left 2 (Nat.add_le_add_right before 3))

theorem retainedStageExtraction_bound {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits ≤ stageExtractionEnvelope (depth + 1) := by
  change run.discoveryRun.extraction.stats.clauseVisits + run.discoveryRun.extraction.stats.literalVisits ≤ _
  rw [run.extractionExact]
  have bound := Nat.le_trans
    (cnfExtraction_visits_bound (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))))
    (growingFormula_unarySize_bound (constitutedSearchIndex (depth + 1)))
  exact Nat.le_trans bound (Nat.le_of_eq
    (congrArg growingFormulaSizeEnvelope (constitutedSearchIndex_exact (depth + 1))))

theorem historyExtraction_bound {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    history.stats.extractionClauseVisits + history.stats.extractionLiteralVisits ≤
      count * stageExtractionEnvelope (depth + count) := by
  induction history with
  | nil => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | @step depth count input head tail ih =>
    change (tail.stats.extractionClauseVisits + head.stats.extractionClauseVisits) +
      (tail.stats.extractionLiteralVisits + head.stats.extractionLiteralVisits) ≤ _
    rw [Nat.add_add_add_comm]
    have later := stageExtractionEnvelope_mono
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
    have headBound := Nat.le_trans (retainedStageExtraction_bound head) later
    have depthEq : depth + 1 + count = depth + (count + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 count]
    rw [depthEq] at ih
    rw [Nat.succ_mul]
    exact Nat.add_le_add ih headBound

def resolutionExtractionPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .mul count (growingFormulaSizePolynomial (.mul (.constant 2) (.add last (.constant 3))))

theorem ConstitutiveResolutionRun.extractionWork_bound {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.phaseWork .extraction ≤ resolutionExtractionPolynomial.eval input := by
  change run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits ≤ _
  rw [run.statsExact]
  exact historyExtraction_bound run.history

theorem ConstitutiveResolutionRun.extractedCandidateWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.extractedCandidateWork ≤ resolutionExtractionPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.extractedCandidateWork
  have statsCausal :
      run.stats = run.constitutiveFeedbackHistory.toSequentialHistory.stats :=
    Eq.trans run.statsExact
      (congrArg (fun history => history.stats) run.historyFromCausalExecution)
  have control := run.constitutiveFeedbackHistory.controlStats_exact
  have bound := run.extractionWork_bound
  change run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits ≤ _ at bound
  calc
    run.stats.extractedCandidates =
        run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractedCandidates :=
      congrArg (fun stats : SequentialHistoryStats => stats.extractedCandidates) statsCausal
    _ = run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractionLiteralVisits :=
      control.1
    _ ≤ run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractionClauseVisits +
        run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractionLiteralVisits :=
      Nat.le_add_left _ _
    _ = run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits :=
      congrArg
        (fun stats : SequentialHistoryStats =>
          stats.extractionClauseVisits + stats.extractionLiteralVisits)
        statsCausal.symm
    _ ≤ resolutionExtractionPolynomial.eval input := bound

def resolutionAttemptPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .mul count (.add (.mul (.constant 2) last) (.constant 10))

theorem resolutionAttemptPolynomial_eval (input : Nat) :
    resolutionAttemptPolynomial.eval input =
      (resolutionLength input) *
        (2 * (input + resolutionLength input) + 10) := by
  rfl

theorem ConstitutiveResolutionRun.candidateTestWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.candidateTestWork ≤ resolutionExtractionPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.candidateTestWork
  have statsCausal :
      run.stats = run.constitutiveFeedbackHistory.toSequentialHistory.stats :=
    Eq.trans run.statsExact
      (congrArg (fun history => history.stats) run.historyFromCausalExecution)
  have extracted := run.extractedCandidateWork_bound
  unfold ConstitutiveResolutionRun.extractedCandidateWork at extracted
  calc
    run.stats.discoveryAttempts =
        run.constitutiveFeedbackHistory.toSequentialHistory.stats.discoveryAttempts :=
      congrArg (fun stats : SequentialHistoryStats => stats.discoveryAttempts) statsCausal
    _ ≤ run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractedCandidates :=
      (run.constitutiveFeedbackHistory.controlStats_exact).2.1
    _ = run.stats.extractedCandidates :=
      congrArg (fun stats : SequentialHistoryStats => stats.extractedCandidates) statsCausal.symm
    _ ≤ resolutionExtractionPolynomial.eval input := extracted

theorem ConstitutiveResolutionRun.relationQueryWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.relationQueryWork ≤ resolutionExtractionPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.relationQueryWork
  have statsCausal :
      run.stats = run.constitutiveFeedbackHistory.toSequentialHistory.stats :=
    Eq.trans run.statsExact
      (congrArg (fun history => history.stats) run.historyFromCausalExecution)
  have extracted := run.extractedCandidateWork_bound
  unfold ConstitutiveResolutionRun.extractedCandidateWork at extracted
  calc
    run.stats.relationQueries =
        run.constitutiveFeedbackHistory.toSequentialHistory.stats.relationQueries :=
      congrArg (fun stats : SequentialHistoryStats => stats.relationQueries) statsCausal
    _ = run.constitutiveFeedbackHistory.toSequentialHistory.stats.discoveryAttempts :=
      run.constitutiveFeedbackHistory.relationQueries_eq_attempts
    _ ≤ run.constitutiveFeedbackHistory.toSequentialHistory.stats.extractedCandidates :=
      (run.constitutiveFeedbackHistory.controlStats_exact).2.1
    _ = run.stats.extractedCandidates :=
      congrArg (fun stats : SequentialHistoryStats => stats.extractedCandidates) statsCausal.symm
    _ ≤ resolutionExtractionPolynomial.eval input := extracted

def resolutionValidatedAtomPolynomial : CostPolynomial :=
  .add .input (.constant 1)

theorem ConstitutiveResolutionRun.validatedAtomWork_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.validatedAtomWork = resolutionValidatedAtomPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.validatedAtomWork resolutionValidatedAtomPolynomial
  have statsCausal :
      run.stats = run.constitutiveFeedbackHistory.toSequentialHistory.stats :=
    Eq.trans run.statsExact
      (congrArg (fun history => history.stats) run.historyFromCausalExecution)
  change run.stats.validatedAtoms = input + 1
  calc
    run.stats.validatedAtoms =
        run.constitutiveFeedbackHistory.toSequentialHistory.stats.validatedAtoms :=
      congrArg (fun stats : SequentialHistoryStats => stats.validatedAtoms) statsCausal
    _ = resolutionLength input :=
      (run.constitutiveFeedbackHistory.controlStats_exact).2.2
    _ = input + 1 := rfl

/-- The §7 counters not already owned by recursive comparison/search work.
Candidate traces are not charged twice: the emitted attempt is the unique
owner of the test-loop transition. -/
def ConstitutiveResolutionRun.section7ControlWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  ((run.extractedCandidateWork + run.candidateTestWork) +
    run.relationQueryWork) + run.validatedAtomWork

def resolutionSection7ControlPolynomial : CostPolynomial :=
  .add (.add (.add resolutionExtractionPolynomial resolutionExtractionPolynomial)
    resolutionExtractionPolynomial) resolutionValidatedAtomPolynomial

theorem ConstitutiveResolutionRun.section7ControlWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.section7ControlWork ≤ resolutionSection7ControlPolynomial.eval input := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add run.extractedCandidateWork_bound run.candidateTestWork_bound)
      run.relationQueryWork_bound)
    (Nat.le_of_eq run.validatedAtomWork_exact)

/-- The previously measured search/read core. It remains useful as a bound
component, but is no longer presented as the complete main-pipeline cost. -/
def ConstitutiveResolutionRun.baseInstrumentedWork {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  ((run.productionCalls + run.measuredRealizationWork.total) + run.phaseWork .extraction) +
    run.measuredSearchWork + run.terminal.measuredReadWork

def resolutionBaseInstrumentedPolynomial : CostPolynomial :=
  .add (.add (.add (.add (.add .input (.add .input (.constant 1))) resolutionRealizationPolynomial)
    resolutionExtractionPolynomial) resolutionMeasuredSearchPolynomial) resolutionTerminalReadPolynomial

theorem ConstitutiveResolutionRun.baseInstrumentedWork_bound {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.baseInstrumentedWork ≤ resolutionBaseInstrumentedPolynomial.eval input := by
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.le_of_eq run.productionCalls_exact) run.realizationWork_bound)
    run.extractionWork_bound) run.measuredSearchWork_bound) run.terminalReadWork_bound

theorem ConstitutiveResolutionRun.generationMaterializationWork_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.generationMaterializationWork =
      (((input + input) + input) + 1) +
        (((input + 1) + (input + 1)) + (input + 1)) := by
  unfold ConstitutiveResolutionRun.generationMaterializationWork
  rw [run.initializationExact, run.productionExact]
  rw [(initializeConstitutiveHistory_counts input).2.1,
    (initializeConstitutiveHistory_counts input).2.2,
    (initializeConstitutiveHistory_material_counts input).1,
    (initializeConstitutiveHistory_material_counts input).2]
  have generationCanonical : run.threadedInitialState.generation =
      generateCanonicalStage input := by
    exact run.threadedInitialGenerationExact
  have produced := run.constitutiveFeedbackHistory.productionStats_exact generationCanonical
  unfold ConstitutiveExecutionHistory.toProductionRun
  rw [produced.2.1, produced.2.2.1, produced.2.2.2]
  rfl

theorem ConstitutiveResolutionRun.continuationApplications_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.stats.continuationApplications = input + 1 := by
  rw [run.statsExact, run.historyFromCausalExecution]
  exact run.constitutiveFeedbackHistory.continuationApplications_eq_count

/-- Previously owned control/material operations, retained as a separately
proved component of the exhaustive §7 ledger. -/
def ConstitutiveResolutionRun.previouslyOwnedWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  ((((run.generationMaterializationWork + run.scheduleWork) +
      run.validationQueryWork) + run.executionQueryWork) + run.codeApplicationWork)

def resolutionPreviouslyOwnedPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let generation := .add
    (.add (.add (.add .input .input) .input) (.constant 1))
    (.add (.add count count) count)
  .add (.add (.add (.add generation count) count) count) (.add count count)

theorem ConstitutiveResolutionRun.previouslyOwnedWork_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.previouslyOwnedWork = resolutionPreviouslyOwnedPolynomial.eval input := by
  have statsEq : run.stats = (executeConstitutiveResolution input).stats := by
    rw [run.statsExact, (executeConstitutiveResolution input).statsExact]
    rw [run.historyExact, (executeConstitutiveResolution input).historyExact]
  unfold ConstitutiveResolutionRun.previouslyOwnedWork
    ConstitutiveResolutionRun.scheduleWork
    ConstitutiveResolutionRun.validationQueryWork
    ConstitutiveResolutionRun.executionQueryWork
    ConstitutiveResolutionRun.codeApplicationWork
    resolutionPreviouslyOwnedPolynomial
  rw [run.generationMaterializationWork_exact, statsEq]
  rw [executeConstitutiveResolution_scheduleAtoms,
    executeConstitutiveResolution_validationQueries,
    executeConstitutiveResolution_executionQueries,
    executeConstitutiveResolution_noGlobalComposition,
    executeConstitutiveResolution_appliedAtoms,
    (executeConstitutiveResolution input).continuationApplications_exact]
  rfl

/-- Polynomial envelope for the feedback counters emitted by the dependent
history recursion: one decision insertion, one provenance insertion and at
most a full scan of the accumulated history at every stage. -/
def resolutionFeedbackPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let candidateBound : CostPolynomial :=
    .add (.mul (.constant 2) (.add .input count)) (.constant 13)
  .add (.add count count) (.mul count (.mul candidateBound count))

def ConstitutiveResolutionRun.feedbackControlWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  (run.decisionAccumulationWork + run.decisionProvenanceWork) +
    run.historyFilteringWork

theorem ConstitutiveResolutionRun.feedbackControlWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.feedbackControlWork ≤ resolutionFeedbackPolynomial.eval input := by
  have decisionExact := run.constitutiveFeedbackHistory.decisionAccumulations_eq_count
  have provenanceExact := run.constitutiveFeedbackHistory.provenanceVisits_eq_count
  have inspectionBound := run.constitutiveFeedbackHistory.inspections_bound
  have initialLength : run.threadedInitialState.decisions.length = 0 := by
    rw [run.threadedInitialStateExact]
    rfl
  unfold ConstitutiveResolutionRun.feedbackControlWork
    ConstitutiveResolutionRun.decisionAccumulationWork
    ConstitutiveResolutionRun.decisionProvenanceWork
    ConstitutiveResolutionRun.historyFilteringWork
    resolutionFeedbackPolynomial
  rw [run.feedbackStatsExact, decisionExact, provenanceExact]
  rw [initialLength] at inspectionBound
  unfold resolutionLength at inspectionBound ⊢
  rw [Nat.zero_add] at inspectionBound
  change
    ((input + 1) + (input + 1)) +
        run.constitutiveFeedbackHistory.feedbackStats.historyFilteringVisits ≤
      ((input + 1) + (input + 1)) +
        ((input + 1) *
          ((2 * (input + (input + 1)) + 13) * (input + 1)))
  exact Nat.add_le_add (Nat.le_refl _) inspectionBound

theorem feedbackControlWork_inputPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).feedbackControlWork) := by
  refine ⟨resolutionFeedbackPolynomial, ?_⟩
  intro input
  dsimp only
  rw [encodeConstitutiveInput_length]
  exact (executeConstitutiveResolution input).feedbackControlWork_bound

/-- All control/material operations not contained in the comparison-work core.
Every summand is projected from an executable producer or stage run. -/
def ConstitutiveResolutionRun.additionalOwnedWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  (run.previouslyOwnedWork + run.section7ControlWork) + run.feedbackControlWork

def resolutionAdditionalOwnedPolynomial : CostPolynomial :=
  .add (.add resolutionPreviouslyOwnedPolynomial resolutionSection7ControlPolynomial)
    resolutionFeedbackPolynomial

theorem ConstitutiveResolutionRun.additionalOwnedWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.additionalOwnedWork ≤ resolutionAdditionalOwnedPolynomial.eval input := by
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.le_of_eq run.previouslyOwnedWork_exact)
      run.section7ControlWork_bound)
    run.feedbackControlWork_bound

/-- Canonical main-pipeline total of the published instrumented operations.
Unlike the former core-only counter, this
also owns generation materialization, scheduling, primitive queries and every
returned continuation application. -/
def ConstitutiveResolutionRun.mainInstrumentedWork {input : Nat}
    (run : ConstitutiveResolutionRun input) : Nat :=
  run.baseInstrumentedWork + run.additionalOwnedWork

def resolutionMainInstrumentedPolynomial : CostPolynomial :=
  .add resolutionBaseInstrumentedPolynomial resolutionAdditionalOwnedPolynomial

theorem ConstitutiveResolutionRun.mainInstrumentedWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.mainInstrumentedWork ≤ resolutionMainInstrumentedPolynomial.eval input := by
  exact Nat.add_le_add run.baseInstrumentedWork_bound
    run.additionalOwnedWork_bound

theorem mainInstrumentedWork_inputPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).mainInstrumentedWork) := by
  refine ⟨resolutionMainInstrumentedPolynomial, ?_⟩
  intro input
  dsimp only
  rw [encodeConstitutiveInput_length]
  exact (executeConstitutiveResolution input).mainInstrumentedWork_bound

/-- Exact partition of the implemented ledger. The projection experiment is
additional work, not an uncharged side result or a second copy of main work. -/
theorem ConstitutiveResolutionRun.instrumentedWork_partition {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.instrumentedWork = run.mainInstrumentedWork + run.projectionExperiment.measuredWork := by
  dsimp only [ConstitutiveResolutionRun.instrumentedWork, measuredPhases, sumPhaseWork,
    ConstitutiveResolutionRun.phaseWork, ConstitutiveResolutionRun.mainInstrumentedWork,
    ConstitutiveResolutionRun.baseInstrumentedWork,
    ConstitutiveResolutionRun.additionalOwnedWork,
    ConstitutiveResolutionRun.feedbackControlWork,
    ConstitutiveResolutionRun.previouslyOwnedWork,
    ConstitutiveResolutionRun.section7ControlWork,
    ConstitutiveResolutionRun.generationMaterializationWork,
    ConstitutiveResolutionRun.extractedCandidateWork,
    ConstitutiveResolutionRun.candidateTestWork,
    ConstitutiveResolutionRun.relationQueryWork,
    ConstitutiveResolutionRun.validatedAtomWork,
    ConstitutiveResolutionRun.scheduleWork,
    ConstitutiveResolutionRun.validationQueryWork,
    ConstitutiveResolutionRun.executionQueryWork,
    ConstitutiveResolutionRun.codeApplicationWork,
    ConstitutiveResolutionRun.decisionAccumulationWork,
    ConstitutiveResolutionRun.decisionProvenanceWork,
    ConstitutiveResolutionRun.historyFilteringWork,
    ConstitutiveResolutionRun.measuredSearchWork]
  rw [ComparisonWork.total_add, ComparisonWork.total_add]
  repeat rw [Nat.add_assoc]
  rw [Nat.add_zero]

/-- A bound for the same finder/interpreter used by both organizations.
The returned code is interpreted only in the successful branch. -/
theorem measuredProjection_search_read_bound {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1) :
    let run := runMeasuredProjection selected source target continuation reader
    run.queryWork.total + run.readWork.total ≤
      (((unaryCnfSize source.context.formula + unaryCnfSize target.context.formula) +
        unaryHistorySize source.context.decisions) + unaryHistorySize target.context.decisions) +
      ((reader selected).work.total + (selected + 2)) := by
  have queryBound := searchMeasuredRelation_bound selected source target
  unfold runMeasuredProjection
  dsimp only
  split
  · change (searchMeasuredRelation selected source target).work.total + 0 ≤ _
    rw [Nat.add_zero]
    exact Nat.le_trans queryBound (Nat.le_add_right _ _)
  · exact Nat.add_le_add queryBound (readFlippedAssignment_bound selected reader selected)

/-- Synthesis over one and the same public run. This records the closed
instrumented obligations, without upgrading their coverage to total runtime. -/
structure MeasuredConstitutiveEvidence {input : Nat} (run : ConstitutiveResolutionRun input) : Prop where
  retainsGeneratedHistory : run.history.generatedHistory = run.generatedHistory
  genericTraversalUsesStoredDiscoveries :
    HEq (concreteConstitutiveOperationalInterface.discoverHistory run.generatedHistory.asGeneric)
      (some run.history.genericDiscovered)
  observedVariableFromExecution : run.terminal.variableReadout.result = some run.terminal.observedVar
  productionCallsExact : run.productionCalls = input + (input + 1)
  accountingPartition : run.instrumentedWork = run.mainInstrumentedWork + run.projectionExperiment.measuredWork
  phaseOwnershipUnique : ∀ phase, phaseOccurrences phase measuredPhases = 1
  mainMeasuredBound : run.mainInstrumentedWork ≤ resolutionMainInstrumentedPolynomial.eval input
  sameRunProjectionLoss :
    ¬ ValueFactorsThrough (integratedInputProjection run.history.firstStage)
      (fun organization => (integratedOrganizationObservation run.history.firstStage organization).terminalBit)

theorem measuredConstitutiveEvidence {input : Nat} (run : ConstitutiveResolutionRun input) :
    MeasuredConstitutiveEvidence run :=
  { retainsGeneratedHistory := run.generatorsExact
    genericTraversalUsesStoredDiscoveries := run.genericTraversalExact
    observedVariableFromExecution := run.terminal.observedVarFromReadout
    productionCallsExact := run.productionCalls_exact
    accountingPartition := run.instrumentedWork_partition
    phaseOwnershipUnique := measuredPhase_occurs_once
    mainMeasuredBound := run.mainInstrumentedWork_bound
    sameRunProjectionLoss := integrated_projection_not_factors _ }

theorem measuredProductionCalls_strict {first second : Nat} (before : first < second) :
    (executeConstitutiveResolution first).productionCalls <
      (executeConstitutiveResolution second).productionCalls := by
  rw [ConstitutiveResolutionRun.productionCalls_exact, ConstitutiveResolutionRun.productionCalls_exact]
  exact Nat.add_lt_add before (Nat.add_lt_add_right before 1)

def projectionSearchEnvelope {root : Cnf} (source target : GeneratedStructuralBranchContext root) : Nat :=
  ((unaryCnfSize source.context.formula + unaryCnfSize target.context.formula) +
    unaryHistorySize source.context.decisions) + unaryHistorySize target.context.decisions

def integratedProjectionEnvelope {depth : Nat} {input : SequentialAssignment depth}
    (stage : SequentialStageRun depth input) : Nat :=
  let sourceSize := unaryCnfSize stage.storedSchedule.entry.source.context.formula
  let targetSize := unaryCnfSize stage.storedSchedule.entry.target.context.formula
  let selected := stage.storedSchedule.entry.var
  let readBound := (input.reader selected).work.total + (selected + 2)
  (((sourceSize + 1) + (targetSize + 1)) + (targetSize + 1)) +
    (projectionSearchEnvelope (integratedMarkedSource stage) (integratedMarkedTarget stage 2 (by decide)) + readBound) +
    (projectionSearchEnvelope (integratedMarkedSource stage) (integratedMarkedTarget stage 4 (by decide)) + readBound)

theorem integratedProjection_measured_bound {depth : Nat} {input : SequentialAssignment depth}
    (stage : SequentialStageRun depth input) :
    (runIntegratedProjectionExperiment stage).measuredWork ≤ integratedProjectionEnvelope stage := by
  let experiment := runIntegratedProjectionExperiment stage
  have construction : experiment.constructionWork.total ≤
      ((unaryCnfSize stage.storedSchedule.entry.source.context.formula + 1) +
        (unaryCnfSize stage.storedSchedule.entry.target.context.formula + 1)) +
        (unaryCnfSize stage.storedSchedule.entry.target.context.formula + 1) := by
    change ((experiment.source.work.add experiment.positiveTarget.work).add experiment.negativeTarget.work).total ≤ _
    rw [ComparisonWork.total_add, ComparisonWork.total_add]
    exact Nat.add_le_add
      (Nat.add_le_add (constructMeasuredChild_bound _ _ _ _) (constructMeasuredChild_bound _ _ _ _))
      (constructMeasuredChild_bound _ _ _ _)
  have positive : experiment.positiveRun.queryWork.total + experiment.positiveRun.readWork.total ≤
      projectionSearchEnvelope (integratedMarkedSource stage) (integratedMarkedTarget stage 2 (by decide)) +
        ((input.reader stage.storedSchedule.entry.var).work.total + (stage.storedSchedule.entry.var + 2)) := by
    rw [experiment.positiveRunExact]
    exact measuredProjection_search_read_bound _ _ _ _ _
  have negative : experiment.negativeRun.queryWork.total + experiment.negativeRun.readWork.total ≤
      projectionSearchEnvelope (integratedMarkedSource stage) (integratedMarkedTarget stage 4 (by decide)) +
        ((input.reader stage.storedSchedule.entry.var).work.total + (stage.storedSchedule.entry.var + 2)) := by
    rw [experiment.negativeRunExact]
    exact measuredProjection_search_read_bound _ _ _ _ _
  exact Nat.add_le_add (Nat.add_le_add construction positive) negative

theorem ConstitutiveResolutionRun.projectionWork_bound {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.projectionExperiment.measuredWork ≤ integratedProjectionEnvelope run.history.firstStage := by
  rw [run.projectionExperimentExact]
  exact integratedProjection_measured_bound _

/-- Closed bound for all counters currently owned by the phase ledger.
The projection envelope still exposes the produced representation and reader;
this is not yet an input-polynomial bound for the full procedure. -/
theorem ConstitutiveResolutionRun.instrumentedWork_bound {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.instrumentedWork ≤ resolutionMainInstrumentedPolynomial.eval input +
      integratedProjectionEnvelope run.history.firstStage := by
  rw [run.instrumentedWork_partition]
  exact Nat.add_le_add run.mainInstrumentedWork_bound run.projectionWork_bound

def projectionStageEnvelope (depth : Nat) : Nat :=
  let index := constitutedSearchIndex depth
  let size := growingFormulaSizeEnvelope index
  let selected := index + 2
  let history := ((selected + 4) + 3) + ((selected + 3) + 1 + 1) + 1
  let read := (selected + 1) + (selected + 2)
  (((size + 1) + (size + 1)) + (size + 1)) +
    ((((size + size) + history) + history) + read) +
    ((((size + size) + history) + history) + read)

theorem retainedSource_formula_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    unaryCnfSize run.storedSchedule.entry.source.context.formula ≤
      unaryCnfSize (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))) := by
  rw [run.storedSchedule.entryExact]
  exact branchResidual_unarySize_le _ _ false

theorem retainedTarget_formula_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    unaryCnfSize run.storedSchedule.entry.target.context.formula ≤
      unaryCnfSize (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))) := by
  rw [run.storedSchedule.entryExact]
  exact branchResidual_unarySize_le _ _ true

theorem markedSource_formula_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    unaryCnfSize (integratedMarkedSource run).context.formula ≤
      unaryCnfSize (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))) :=
  Nat.le_trans (branchResidual_unarySize_le _ _ false) (retainedSource_formula_size run)

theorem markedTarget_formula_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 0 < offset) :
    unaryCnfSize (integratedMarkedTarget run offset positive).context.formula ≤
      unaryCnfSize (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))) :=
  Nat.le_trans (branchResidual_unarySize_le _ _ false) (retainedTarget_formula_size run)

theorem markedSource_history_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    unaryHistorySize (integratedMarkedSource run).context.decisions =
      ((run.storedSchedule.entry.var + 2) + 3) +
        ((run.storedSchedule.entry.var + 3) + 1 + 1) + 1 := by
  unfold integratedMarkedSource unaryHistorySize
  change unaryListSize unaryDecisionSize
    (⟨run.storedSchedule.entry.var + 2, false⟩ ::
      run.storedSchedule.entry.source.context.decisions) = _
  rw [(retained_decisions_exact run).1]
  rfl

theorem markedTarget_history_size {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 0 < offset) :
    unaryHistorySize (integratedMarkedTarget run offset positive).context.decisions =
      ((run.storedSchedule.entry.var + offset) + 3) +
        ((run.storedSchedule.entry.var + 3) + 1 + 1) + 1 := by
  unfold integratedMarkedTarget unaryHistorySize
  change unaryListSize unaryDecisionSize
    (⟨run.storedSchedule.entry.var + offset, false⟩ ::
      run.storedSchedule.entry.target.context.decisions) = _
  rw [(retained_decisions_exact run).2]
  rfl

theorem integratedProjectionEnvelope_stage_bound {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input)
    (readerBound : (input.reader (constitutedSearchIndex (depth + 1) + 2)).work.total ≤
      constitutedSearchIndex (depth + 1) + 2 + 1) :
    integratedProjectionEnvelope run ≤
      projectionStageEnvelope (depth + 1) := by
  let index := constitutedSearchIndex (depth + 1)
  let size := growingFormulaSizeEnvelope index
  have rootSize : unaryCnfSize (distinctGrowingDiscoveryFormula index) ≤ size :=
    growingFormula_unarySize_bound index
  have sourceSize := Nat.le_trans (retainedSource_formula_size run) rootSize
  have targetSize := Nat.le_trans (retainedTarget_formula_size run) rootSize
  have markedSourceSize := Nat.le_trans (markedSource_formula_size run) rootSize
  have positiveSize := Nat.le_trans (markedTarget_formula_size run 2 (by decide)) rootSize
  have negativeSize := Nat.le_trans (markedTarget_formula_size run 4 (by decide)) rootSize
  have selectedExact : run.storedSchedule.entry.var = index + 2 := by
    rw [run.storedSchedule.entryExact]
    change run.discovery.var = _
    have same : run.discovery.var = stageSelectedVar (depth + 1) := by
      have entry := sequentialStage_selected_exact run
      rw [run.scheduleExact] at entry
      exact entry
    rw [same]
    rfl
  let history := (((index + 2 + 4) + 3) + (((index + 2) + 3) + 1 + 1)) + 1
  have sourceHistory : unaryHistorySize (integratedMarkedSource run).context.decisions ≤ history := by
    rw [markedSource_history_size, selectedExact]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left (by decide : 2 ≤ 4) (index + 2)) 3)
        (((index + 2) + 3) + 1 + 1)) 1
  have positiveHistory : unaryHistorySize (integratedMarkedTarget run 2 (by decide)).context.decisions ≤
      history := by
    rw [markedTarget_history_size, selectedExact]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left (by decide : 2 ≤ 4) (index + 2)) 3)
        (((index + 2) + 3) + 1 + 1)) 1
  have negativeHistory : unaryHistorySize (integratedMarkedTarget run 4 (by decide)).context.decisions ≤
      history := by
    rw [markedTarget_history_size, selectedExact]
    exact Nat.le_refl _
  have construction :
      ((unaryCnfSize run.storedSchedule.entry.source.context.formula + 1) +
          (unaryCnfSize run.storedSchedule.entry.target.context.formula + 1)) +
          (unaryCnfSize run.storedSchedule.entry.target.context.formula + 1) ≤
        ((size + 1) + (size + 1)) + (size + 1) :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add_right sourceSize 1) (Nat.add_le_add_right targetSize 1))
      (Nat.add_le_add_right targetSize 1)
  have positiveSearch :
      projectionSearchEnvelope (integratedMarkedSource run) (integratedMarkedTarget run 2 (by decide)) ≤
        ((size + size) + history) + history :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add markedSourceSize positiveSize) sourceHistory)
      positiveHistory
  have negativeSearch :
      projectionSearchEnvelope (integratedMarkedSource run) (integratedMarkedTarget run 4 (by decide)) ≤
        ((size + size) + history) + history :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add markedSourceSize negativeSize) sourceHistory)
      negativeHistory
  have readTotal :
      (input.reader (index + 2)).work.total + (index + 2 + 2) ≤
        (index + 2 + 1) + (index + 2 + 2) :=
    Nat.add_le_add readerBound (Nat.le_refl _)
  unfold integratedProjectionEnvelope projectionSearchEnvelope
  dsimp only
  rw [selectedExact]
  unfold projectionStageEnvelope
  dsimp only
  exact Nat.add_le_add
    (Nat.add_le_add construction (Nat.add_le_add positiveSearch readTotal))
    (Nat.add_le_add negativeSearch readTotal)

theorem canonicalIntegratedProjectionEnvelope_bound (depth : Nat) :
    integratedProjectionEnvelope (executeSequentialStage depth (initialSequentialAssignment depth)) ≤
      projectionStageEnvelope (depth + 1) :=
  integratedProjectionEnvelope_stage_bound _ (readAlternatingAssignment_bound _)

/-- Syntactic polynomial whose evaluation is the complete first-stage
projection envelope. -/
def projectionStagePolynomial (depth : CostPolynomial) : CostPolynomial :=
  let one : CostPolynomial := .constant 1
  let two : CostPolynomial := .constant 2
  let three : CostPolynomial := .constant 3
  let four : CostPolynomial := .constant 4
  let index := .mul two (.add depth three)
  let size := growingFormulaSizePolynomial index
  let selected := .add index two
  let history := .add
    (.add (.add (.add selected four) three)
      (.add (.add (.add selected three) one) one)) one
  let read := .add (.add selected one) (.add selected two)
  let construction := .add (.add (.add size one) (.add size one)) (.add size one)
  let search := .add (.add (.add size size) history) history
  .add (.add construction (.add search read)) (.add search read)

theorem projectionStagePolynomial_eval (depth : CostPolynomial) (input : Nat) :
    (projectionStagePolynomial depth).eval input = projectionStageEnvelope (depth.eval input) := by
  unfold projectionStagePolynomial projectionStageEnvelope
  dsimp only
  simp only [CostPolynomial.eval]
  rw [growingFormulaSizePolynomial_eval]
  simp only [CostPolynomial.eval]
  rw [constitutedSearchIndex_exact]

def resolutionProjectionPolynomial : CostPolynomial :=
  projectionStagePolynomial (.add .input (.constant 1))

theorem ConstitutiveResolutionRun.projectionEnvelope_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    integratedProjectionEnvelope run.history.firstStage ≤
      resolutionProjectionPolynomial.eval input := by
  exact Nat.le_trans
    (integratedProjectionEnvelope_stage_bound run.history.firstStage
      (readAlternatingAssignment_bound _))
    (Nat.le_of_eq
      (projectionStagePolynomial_eval (.add .input (.constant 1)) input).symm)

def resolutionInstrumentedPolynomial : CostPolynomial :=
  .add resolutionMainInstrumentedPolynomial resolutionProjectionPolynomial

theorem ConstitutiveResolutionRun.instrumentedWork_polynomial_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.instrumentedWork ≤ resolutionInstrumentedPolynomial.eval input := by
  rw [run.instrumentedWork_partition]
  exact Nat.add_le_add run.mainInstrumentedWork_bound
    (Nat.le_trans run.projectionWork_bound run.projectionEnvelope_bound)

theorem instrumentedWork_inputPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).instrumentedWork) := by
  refine ⟨resolutionInstrumentedPolynomial, ?_⟩
  intro input
  dsimp only
  rw [encodeConstitutiveInput_length]
  exact (executeConstitutiveResolution input).instrumentedWork_polynomial_bound

/--
Formal coverage certificate for the exhaustive §7 ledger.  Every published
operation is assigned to one phase projected from the executed run.  The
retained tested-candidate trace is identified with the emitted attempt count,
so it witnesses the loop without creating a second charge.
-/
structure Section7AccountingCoverage {input : Nat}
    (run : ConstitutiveResolutionRun input) : Prop where
  productionOwned : run.phaseWork .production = run.productionCalls
  generationMaterializationOwned :
    run.phaseWork .generationMaterialization = run.generationMaterializationWork
  realizationOwned : run.phaseWork .realization = run.measuredRealizationWork.total
  extractionTraversalOwned :
    run.phaseWork .extraction =
      run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits
  extractedCandidatesOwned :
    run.phaseWork .extractedCandidates = run.stats.extractedCandidates
  discoveryRecursionOwned :
    run.phaseWork .discovery =
      (run.measuredComparisonWork.add run.measuredConstructionWork).total
  candidateTestsOwned :
    run.phaseWork .candidateTests = run.stats.discoveryAttempts
  testedTraceMatchesChargedAttempts :
    run.stats.testedCandidates = run.stats.discoveryAttempts
  relationQueriesOwned :
    run.phaseWork .relationQueries = run.stats.relationQueries
  scheduleOwned : run.phaseWork .schedule = run.stats.scheduleAtoms
  validationSearchOwned :
    run.phaseWork .validationSearch = run.measuredValidationWork.total
  validatedAtomsOwned :
    run.phaseWork .validatedAtoms = run.stats.validatedAtoms
  validationQueriesOwned :
    run.phaseWork .validationQueries = run.stats.validationPrimitiveQueries
  executionSearchOwned :
    run.phaseWork .executionSearch = run.measuredExecutionWork.total
  executionQueriesOwned :
    run.phaseWork .executionQueries =
      run.stats.executionPrimitiveQueries + run.stats.compositionCandidates
  codeApplicationOwned :
    run.phaseWork .codeApplication =
      run.stats.appliedCodeAtoms + run.stats.continuationApplications
  decisionAccumulationOwned :
    run.phaseWork .decisionAccumulation = run.feedbackStats.decisionAccumulations
  decisionProvenanceOwned :
    run.phaseWork .decisionProvenance = run.feedbackStats.provenanceVisits
  historyFilteringOwned :
    run.phaseWork .historyFiltering =
      run.feedbackStats.historyFilteringVisits
  nextStateRealizationUsesExistingOwner :
    run.phaseWork .realization = run.measuredRealizationWork.total
  stateDependentExtractionUsesExistingOwner :
    run.phaseWork .extraction =
      run.stats.extractionClauseVisits + run.stats.extractionLiteralVisits
  nextDiscoveryUsesExistingOwner :
    run.phaseWork .discovery =
      (run.measuredComparisonWork.add run.measuredConstructionWork).total
  terminalOwned : run.phaseWork .terminal = run.terminal.measuredReadWork
  projectionOwned :
    run.phaseWork .projection = run.projectionExperiment.measuredWork
  canonicalTotalExact :
    run.instrumentedWork = sumPhaseWork run.phaseWork measuredPhases

theorem executeConstitutiveResolution_section7Coverage (input : Nat) :
    Section7AccountingCoverage (executeConstitutiveResolution input) := by
  refine
    { productionOwned := rfl
      generationMaterializationOwned := rfl
      realizationOwned := rfl
      extractionTraversalOwned := rfl
      extractedCandidatesOwned := rfl
      discoveryRecursionOwned := rfl
      candidateTestsOwned := rfl
      testedTraceMatchesChargedAttempts := ?_
      relationQueriesOwned := rfl
      scheduleOwned := rfl
      validationSearchOwned := rfl
      validatedAtomsOwned := rfl
      validationQueriesOwned := rfl
      executionSearchOwned := rfl
      executionQueriesOwned := rfl
      codeApplicationOwned := rfl
      decisionAccumulationOwned := rfl
      decisionProvenanceOwned := rfl
      historyFilteringOwned := rfl
      nextStateRealizationUsesExistingOwner := rfl
      stateDependentExtractionUsesExistingOwner := rfl
      nextDiscoveryUsesExistingOwner := rfl
      terminalOwned := rfl
      projectionOwned := rfl
      canonicalTotalExact := rfl }
  let run := executeConstitutiveResolution input
  have statsCausal :
      run.stats = run.constitutiveFeedbackHistory.toSequentialHistory.stats :=
    Eq.trans run.statsExact
      (congrArg (fun history => history.stats) run.historyFromCausalExecution)
  exact Eq.trans
    (congrArg (fun stats : SequentialHistoryStats => stats.testedCandidates) statsCausal)
    (Eq.trans run.constitutiveFeedbackHistory.testedCandidates_eq_attempts
      (congrArg (fun stats : SequentialHistoryStats => stats.discoveryAttempts)
        statsCausal).symm)

/--
Final evidence for one concrete input.  The constitutive evidence and its
accounting certificate are carried by the same value: the ledger is the one
projected from `core.run`, its total is exactly that run's instrumented work,
every §7 operation has an owner, and the polynomial bound applies to this very
run.  No family-level theorem has to be consulted to recover these facts.
-/
structure EndogenousOperationalDecompositionPerInputEvidence (input : Nat) : Type 3 where
  core : EndogenousOperationalDecompositionEvidence input
  canonicalAccounting : CanonicalMeasuredAccounting input
  phaseWorkExact : canonicalAccounting.phaseWork = core.run.phaseWork
  totalWorkExact : canonicalAccounting.total = core.run.instrumentedWork
  section7Coverage : Section7AccountingCoverage core.run
  phaseOwnershipUnique : ∀ phase, phaseOccurrences phase measuredPhases = 1
  accountingPartition :
    core.run.instrumentedWork =
      core.run.mainInstrumentedWork + core.run.projectionExperiment.measuredWork
  totalWorkBound :
    core.run.instrumentedWork ≤ resolutionInstrumentedPolynomial.eval input
  feedbackAccountingExact :
    core.run.feedbackStats = core.run.constitutiveFeedbackHistory.feedbackStats
  feedbackWorkBound :
    core.run.feedbackControlWork ≤ resolutionFeedbackPolynomial.eval input
  nextDiscoveryDependsOnConstitution :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := input))
        (nextDiscoveryOutcome (depth := input))

/-- The exact final evidence is constructed independently for every input. -/
def endogenousOperationalDecompositionPerInputEvidence (input : Nat) :
    EndogenousOperationalDecompositionPerInputEvidence input := by
  let core := endogenousOperationalDecompositionEvidence input
  let accounting := canonicalMeasuredAccounting input
  refine
    { core := core
      canonicalAccounting := accounting
      phaseWorkExact := ?_
      totalWorkExact := ?_
      section7Coverage := ?_
      phaseOwnershipUnique := measuredPhase_occurs_once
      accountingPartition := ?_
      totalWorkBound := ?_
      feedbackAccountingExact := core.run.feedbackStatsExact
      feedbackWorkBound := ?_
      nextDiscoveryDependsOnConstitution := nextDiscovery_not_factors input }
  · rw [core.runExact, accounting.phaseWorkExact]
  · rw [core.runExact]
    exact accounting.total_is_canonical
  · rw [core.runExact]
    exact executeConstitutiveResolution_section7Coverage input
  · rw [core.runExact]
    exact (executeConstitutiveResolution input).instrumentedWork_partition
  · rw [core.runExact]
    exact (executeConstitutiveResolution input).instrumentedWork_polynomial_bound
  · exact core.run.feedbackControlWork_bound

/-- Final integrated family for the construction currently proved. Its work
field is the canonical phase-owned ledger, not the legacy structural surface.
This is a synthesis of the concrete family only, not a universal closure claim. -/
structure EndogenousOperationalDecompositionFamily : Type 3 where
  perInput : ∀ input, EndogenousOperationalDecompositionPerInputEvidence input
  generatedWorkStrict :
    ∀ input,
      (perInput input).core.run.stats.generatedSteps <
        (perInput (input + 1)).core.run.stats.generatedSteps
  discoveryAttemptsStrict :
    ∀ input,
      (stageRecordedDiscoveryRun input).outcome.attempts <
        (stageRecordedDiscoveryRun (input + 1)).outcome.attempts
  extractionVisitsStrict :
    ∀ input,
      (stageRecordedDiscoveryRun input).extraction.stats.literalVisits <
        (stageRecordedDiscoveryRun (input + 1)).extraction.stats.literalVisits
  formulaComparisonVisitsStrict :
    ∀ input,
      (stageRecordedDiscoveryRun input).outcome.formulaComparisonLiteralVisits <
        (stageRecordedDiscoveryRun
          (input + 1)).outcome.formulaComparisonLiteralVisits
  totalWorkBound :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).instrumentedWork)
  feedbackWorkBound :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).feedbackControlWork)
  canonicalAccounting : ∀ input, CanonicalMeasuredAccounting input
  section7Coverage :
    ∀ input, Section7AccountingCoverage (executeConstitutiveResolution input)
  phaseOwnershipUnique : ∀ phase, phaseOccurrences phase measuredPhases = 1
  accountingPartition : ∀ input,
    (executeConstitutiveResolution input).instrumentedWork =
      (executeConstitutiveResolution input).mainInstrumentedWork +
        (executeConstitutiveResolution input).projectionExperiment.measuredWork
  projectionCannotRecoverConstitution :
    ∀ input,
      ¬ ValueFactorsThrough
          (integratedInputProjection (perInput input).core.run.history.firstStage)
          (fun organization =>
            (integratedOrganizationObservation
              (perInput input).core.run.history.firstStage organization).terminalBit)
  nextDiscoveryCannotRecoverConstitution :
    ∀ input,
      ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := input))
          (nextDiscoveryOutcome (depth := input))

/-- The complete measured concrete family is constructed rather than assumed. -/
def endogenousOperationalDecompositionFamily : EndogenousOperationalDecompositionFamily :=
  { perInput := endogenousOperationalDecompositionPerInputEvidence
    generatedWorkStrict := resolution_generatedSteps_strict
    discoveryAttemptsStrict := stageRecordedDiscovery_attempts_strict
    extractionVisitsStrict := stageRecordedExtractionLiteralVisits_strict
    formulaComparisonVisitsStrict := stageRecordedFormulaComparisonVisits_strict
    totalWorkBound := instrumentedWork_inputPolynomial
    feedbackWorkBound := feedbackControlWork_inputPolynomial
    canonicalAccounting := canonicalMeasuredAccounting
    section7Coverage := executeConstitutiveResolution_section7Coverage
    phaseOwnershipUnique := measuredPhase_occurs_once
    accountingPartition := fun input =>
      (executeConstitutiveResolution input).instrumentedWork_partition
    projectionCannotRecoverConstitution :=
      fun input => integrated_projection_not_factors
        (endogenousOperationalDecompositionPerInputEvidence input).core.run.history.firstStage
    nextDiscoveryCannotRecoverConstitution := nextDiscovery_not_factors }

/-- Family-level synthesis of the implemented, measured constitutive procedure.
The full-work field includes the separately owned projection experiment. -/
structure MeasuredConstitutiveFamily : Prop where
  perInput : ∀ input, MeasuredConstitutiveEvidence (executeConstitutiveResolution input)
  mainWorkPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).mainInstrumentedWork)
  fullWorkPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).instrumentedWork)
  section7Coverage :
    ∀ input, Section7AccountingCoverage (executeConstitutiveResolution input)
  productionStrict : ∀ {first second}, first < second →
    (executeConstitutiveResolution first).productionCalls <
      (executeConstitutiveResolution second).productionCalls
  costNotInflatable : ∀ input (first second : CanonicalMeasuredAccounting input), first.total = second.total
  projectionIncluded : ∀ input,
    (executeConstitutiveResolution input).instrumentedWork =
      (executeConstitutiveResolution input).mainInstrumentedWork +
      (executeConstitutiveResolution input).projectionExperiment.measuredWork
  measuredCostBound : ∀ input,
    (executeConstitutiveResolution input).instrumentedWork ≤
      resolutionInstrumentedPolynomial.eval input

theorem measuredConstitutiveFamily : MeasuredConstitutiveFamily :=
  { perInput := fun input => measuredConstitutiveEvidence (executeConstitutiveResolution input)
    mainWorkPolynomial := mainInstrumentedWork_inputPolynomial
    fullWorkPolynomial := instrumentedWork_inputPolynomial
    section7Coverage := executeConstitutiveResolution_section7Coverage
    productionStrict := measuredProductionCalls_strict
    costNotInflatable := fun _ first second => canonicalMeasuredAccounting_not_inflatable first second
    projectionIncluded := fun input => (executeConstitutiveResolution input).instrumentedWork_partition
    measuredCostBound := fun input =>
      (executeConstitutiveResolution input).instrumentedWork_polynomial_bound }

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredPhase_occurs_once
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.generationMaterializationWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.generationMaterializationWork_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.extractedCandidateWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.resolutionAttemptPolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.candidateTestWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.relationQueryWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.validatedAtomWork_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.section7ControlWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.decisionAccumulationWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.decisionProvenanceWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.historyFilteringWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.feedbackControlWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.feedbackControlWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.feedbackControlWork_inputPolynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.additionalOwnedWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.previouslyOwnedWork_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.additionalOwnedWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.IntegratedProjectionExperiment.measuredWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.phaseWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.instrumentedWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.canonicalMeasuredAccounting
#print axioms ConstitutiveSearch.EndogenousDecomposition.CanonicalMeasuredAccounting.total_is_canonical
#print axioms ConstitutiveSearch.EndogenousDecomposition.canonicalMeasuredAccounting_not_inflatable
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryWork_does_not_add_legacy_surface
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectionWork_shared_source_once
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageExtractionEnvelope_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedStageExtraction_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyExtraction_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.extractionWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.mainInstrumentedWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.mainInstrumentedWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.mainInstrumentedWork_inputPolynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.instrumentedWork_partition
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredProjection_search_read_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredConstitutiveEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredProductionCalls_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedProjection_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.projectionWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.instrumentedWork_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.canonicalIntegratedProjectionEnvelope_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectionStagePolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.projectionEnvelope_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolutionRun.instrumentedWork_polynomial_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.instrumentedWork_inputPolynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution_section7Coverage
#print axioms ConstitutiveSearch.EndogenousDecomposition.endogenousOperationalDecompositionPerInputEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.endogenousOperationalDecompositionFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredConstitutiveFamily
/- AXIOM_AUDIT_END -/
