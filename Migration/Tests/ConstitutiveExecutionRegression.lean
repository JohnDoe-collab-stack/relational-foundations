import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAccounting
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFullStep
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAssignmentBounds
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredDiscoveryBounds

/-!
# Adversarial regressions for the isolated integration

These theorems pin the architectural facts targeted by the preceding audits.
They are ordinary production-independent propositions over the public concrete
run; no expected target, relation, code, terminal, or answer is an input to
`executeConstitutiveResolution`.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open ConstitutiveGeneration
open SAT

/-- Successive operational readouts differ; this supports, but does not itself
constitute, the target-injection counterprobe below. -/
theorem regression_successive_operational_indices_differ (depth : Nat) :
    (constructStage (depth + 1)).operationalIndex ≠
      (constructStage depth).operationalIndex :=
  constitutedOperationalIndex_succ_ne depth

/-- A direct attempted construction of a typed stage whose produced target is
identified with a target supplied independently by the caller. -/
structure ExternallyTargetedStageRunAttempt
    (depth : Nat)
    (input : SequentialAssignment depth)
    (externalTarget : PositiveConstitution examplePresentation) where
  run : SequentialStageRun depth input
  injectedTarget : run.generation.target = externalTarget

/-- No externally selected target distinct from the produced successor can be
installed in a typed stage run.  The contradiction is carried by the
`CanonicalStageGeneration.targetExact` field inside the attempted run. -/
theorem external_target_cannot_construct_typed_run
    {depth : Nat}
    {input : SequentialAssignment depth}
    {externalTarget : PositiveConstitution examplePresentation}
    (different :
      externalTarget ≠ (constructStage (depth + 1)).history.endpoint) :
    ¬ Nonempty (ExternallyTargetedStageRunAttempt depth input externalTarget) := by
  intro possible
  rcases possible with ⟨attempt⟩
  apply different
  rw [← attempt.injectedTarget]
  exact attempt.run.generation.targetExact

/-- Regression 1, exact counterprobe: even the current endpoint cannot be
injected as the target of the next typed run. -/
theorem regression_generated_target_not_injected
    (depth : Nat)
    (input : SequentialAssignment depth) :
    ¬ Nonempty
      (ExternallyTargetedStageRunAttempt depth input
        (constructStage depth).history.endpoint) := by
  apply external_target_cannot_construct_typed_run
  intro endpointEquality
  apply regression_successive_operational_indices_differ depth
  rw [constructStage_operationalIndex, constructStage_operationalIndex]
  exact (congrArg positiveDepth endpointEquality).symm

/-- Regression 2: stored execution code is the discovered schedule atom. -/
theorem regression_relation_substitution_rejected
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.execution.code = run.schedule.entry.code :=
  executedDiscoverySchedule_code run.execution

/-- Regression 3: the stage output is the evaluation of the returned code. -/
theorem regression_code_is_applied
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.application.output.1 =
      ((run.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)
          run.schedule.entry.var)).map
        run.sourceContinuation).1 :=
  run.application.assignment_from_returned_code

theorem regression_code_application_is_instrumented
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.application.evaluatedAtoms = run.execution.code.size ∧
      run.application.continuationApplications = run.execution.code.size :=
  ⟨run.application.evaluatedAtomsExact,
    run.application.continuationApplicationsExact⟩

theorem regression_application_fields_from_recursive_run
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.application.output =
        (applyMeasuredTransportCode
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            run.schedule.entry.var)
          run.execution.code run.sourceContinuation).output ∧
      run.application.evaluatedAtoms =
        (applyMeasuredTransportCode
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            run.schedule.entry.var)
          run.execution.code run.sourceContinuation).evaluatedAtoms ∧
      run.application.continuationApplications =
        (applyMeasuredTransportCode
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            run.schedule.entry.var)
          run.execution.code run.sourceContinuation).continuationApplications :=
  ⟨run.application.outputFromInstrumentedRun,
    run.application.evaluatedAtomsFromInstrumentedRun,
    run.application.continuationApplicationsFromInstrumentedRun⟩

theorem regression_application_stats_are_run_emitted
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.stats.appliedCodeAtoms = run.application.evaluatedAtoms ∧
      run.stats.continuationApplications =
        run.application.continuationApplications :=
  ⟨rfl, rfl⟩

/-- Regression 4: that exact application preserves source acceptance. -/
theorem regression_applied_code_preserves_acceptance
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input)
    (accepted :
      GeneratedStructuralBranchAccept
        run.schedule.entry.source
        run.sourceContinuation) :
    GeneratedStructuralBranchAccept
      run.schedule.entry.target
      run.application.output :=
  run.application.preservesAccept accepted

theorem regression_concrete_source_is_accepted
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    GeneratedStructuralBranchAccept
      run.schedule.entry.source run.sourceContinuation :=
  run.sourceAccepted

theorem regression_concrete_output_is_accepted
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    GeneratedStructuralBranchAccept
      run.schedule.entry.target run.application.output :=
  run.outputAccepted

/-- Regression 5: the selected variable is the executable discovery output. -/
theorem regression_selected_variable_is_discovered (depth : Nat) :
    (canonicalStageDiscovery depth).var = stageSelectedVar depth :=
  canonicalStageDiscovery_var depth

/-- Regression 6: discovery work cannot remain constant across stages. -/
theorem regression_discovery_not_constant (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.attempts <
      (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts :=
  stageRecordedDiscovery_attempts_strict depth

/-- Regression 7: even input plus projection cannot reconstruct the outcome. -/
theorem regression_no_factorization_by_input_and_projection (input : Nat) :
    ¬ ValueFactorsThrough
        (organizationInputProjection input)
        (organizationObservation input) :=
  operational_observation_not_factors_through_input input

/-- Regression 8: both witnesses literally carry the same external input. -/
theorem regression_witnesses_share_input (input : Nat) :
    (organizationInputProjection input .compatible).1 =
        (organizationInputProjection input .incompatible).1 ∧
      (organizationInputProjection input .compatible).1 = input := by
  exact ⟨rfl, rfl⟩

/-- Regression 9: the external index changes actual generated work. -/
theorem regression_index_not_spectator (input : Nat) :
    (executeConstitutiveResolution input).stats.generatedSteps <
      (executeConstitutiveResolution (input + 1)).stats.generatedSteps :=
  resolution_generatedSteps_strict input

/-- Regression 10: both extraction and candidate attempts grow strictly. -/
theorem regression_instrumented_work_grows (depth : Nat) :
    (stageRecordedDiscoveryRun depth).extraction.stats.literalVisits <
        (stageRecordedDiscoveryRun (depth + 1)).extraction.stats.literalVisits ∧
      (stageRecordedDiscoveryRun depth).outcome.attempts <
        (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts :=
  ⟨stageRecordedExtractionLiteralVisits_strict depth,
    stageRecordedDiscovery_attempts_strict depth⟩

/-- Regression 11: recorded candidate identities and charges cannot diverge. -/
theorem regression_tested_candidates_are_charged (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.testedCandidates.length =
      (stageRecordedDiscoveryRun depth).outcome.attempts :=
  stageRecordedDiscovery_tested_length depth

/-- Regression 12: the published total is a deterministic projection of the run. -/
theorem regression_cost_is_run_derived (input : Nat) :
    (executeConstitutiveResolution input).stats.total =
      (executeConstitutiveResolution input).history.stats.total := by
  exact
    congrArg
      SequentialHistoryStats.total
      (executeConstitutiveResolution input).statsExact

/-- Regression 13: the legacy structural profile is recursively run-derived. -/
theorem regression_structural_profile_is_run_derived (input : Nat) :
    (executeConstitutiveResolution input).structuralProfileCost =
      (executeConstitutiveResolution input).history.totalStructuralProfileCost :=
  (executeConstitutiveResolution input).structuralProfileCostExact

/-- Regression 15: no hidden global-composition search occurs. -/
theorem regression_no_global_closure (input : Nat) :
    (executeConstitutiveResolution input).stats.compositionCandidates = 0 :=
  executeConstitutiveResolution_noGlobalComposition input

/-- Regression 16: projection erases a distinction that remains operational. -/
theorem regression_provenance_erasure_is_observable (input : Nat) :
    (compatibleTarget input).context.decisions ≠
        (incompatibleTarget input).context.decisions ∧
      organizationInputProjection input .compatible =
        organizationInputProjection input .incompatible ∧
      organizationObservation input .compatible ≠
        organizationObservation input .incompatible :=
  ⟨organizations_constitutively_distinct input,
    organization_input_projection_equal input,
    organization_observation_different input⟩

/-- Regression 17: the terminal decision is downstream of the threaded trace. -/
theorem regression_terminal_is_trace_derived (input : Nat) :
    (executeConstitutiveResolution input).terminal =
        terminalFromSequentialHistory
          (executeConstitutiveResolution input).history ∧
      (executeConstitutiveResolution input).decision =
        decideSequentialTerminal
          (executeConstitutiveResolution input).terminal :=
  ⟨(executeConstitutiveResolution input).terminalExact,
    (executeConstitutiveResolution input).decisionExact⟩

/-- Regression 18: the decision folds bits read from actual applied outputs. -/
theorem regression_decision_reads_executed_bits (input : Nat) :
    (executeConstitutiveResolution input).terminal.observedBits =
        (executeConstitutiveResolution input).history.executedBits ∧
      (executeConstitutiveResolution input).decision =
        transportedBitParity
          (executeConstitutiveResolution input).terminal.observedBits := by
  constructor
  · exact (executeConstitutiveResolution input).terminal.observedBitsExact
  · exact
      (endogenousOperationalDecompositionEvidence input).decisionReadsTransportedBits

theorem regression_generated_history_is_consumed (input : Nat) :
    (executeConstitutiveResolution input).generatedHistory =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory.toGeneratedHistory :=
  (executeConstitutiveResolution input).historyConsumesGeneration

theorem regression_encoded_input_size (input : Nat) :
    (encodeConstitutiveInput input).length = input :=
  encodeConstitutiveInput_length input

theorem regression_relation_has_discovery_provenance
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.schedule.entry.relation = run.discovery.relation :=
  concreteRelation_comes_from_discovery run

theorem regression_phase_accounting_is_canonical (input : Nat) :
    (executeConstitutiveResolution input).phaseAccounting.total =
      (executeConstitutiveResolution input).structuralProfileCost :=
  (executeConstitutiveResolution input).phaseAccountingTotalExact

theorem regression_terminal_visits_are_executed (input : Nat) :
    (executeConstitutiveResolution input).terminal.readoutRun.bitVisits =
      (executeConstitutiveResolution input).terminal.observedBits.length :=
  (endogenousOperationalDecompositionEvidence input).terminalReadoutInstrumented

/-- Regression 24: the compared formula surface cannot stay constant. -/
theorem regression_formula_comparison_surface_grows (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.formulaComparisonLiteralVisits <
      (stageRecordedDiscoveryRun
        (depth + 1)).outcome.formulaComparisonLiteralVisits :=
  stageRecordedFormulaComparisonVisits_strict depth

/-- Regression 25: detailed discovery work is fixed by the executed stage. -/
theorem regression_detailed_discovery_work_is_exact
    (depth : Nat)
    (input : SequentialAssignment depth) :
    let stats := (executeSequentialStage depth input).stats
    stats.candidateConstructions = 2 * (2 * depth + 10) ∧
      stats.variableComparisonUnits =
        (2 * depth + 14) * (2 * depth + 10) ∧
      stats.formulaComparisonLiteralVisits =
        (2 * depth + 13) * (2 * depth + 10) ∧
      stats.historyComparisonDecisionVisits = 2 * depth + 10 ∧
      stats.relationQueries = 2 * depth + 10 :=
  executeSequentialStage_detailedDiscoveryStats depth input

/-- Regression 26: a relation query cannot escape the attempt accounting. -/
theorem regression_relation_queries_are_charged (input : Nat) :
    (executeConstitutiveResolution input).stats.relationQueries =
      (executeConstitutiveResolution input).stats.discoveryAttempts :=
  (endogenousOperationalDecompositionEvidence input).relationQueriesAreAttempts

/-- Regression 27: extraction emits its returned-candidate count. -/
theorem regression_extracted_candidates_are_run_emitted (input : Nat) :
    (executeConstitutiveResolution input).phaseWork .extractedCandidates =
      (executeConstitutiveResolution input).stats.extractedCandidates :=
  rfl

/-- Regression 28: validation emits its validated-atom count. -/
theorem regression_validated_atoms_are_run_emitted (input : Nat) :
    (executeConstitutiveResolution input).phaseWork .validatedAtoms =
      (executeConstitutiveResolution input).stats.validatedAtoms :=
  rfl

/-- Regression 29: each final per-input evidence carries the exhaustive §7 certificate. -/
theorem regression_section7_accounting_is_in_final_family (input : Nat) :
    Section7AccountingCoverage (executeConstitutiveResolution input) :=
  by
    have coverage :=
      (endogenousOperationalDecompositionPerInputEvidence input).section7Coverage
    rw [(endogenousOperationalDecompositionPerInputEvidence input).core.runExact] at coverage
    exact coverage

/-- Regression 29b: the per-input final evidence exposes its exact canonical total. -/
theorem regression_accounting_exact_in_final_per_input (input : Nat) :
    (endogenousOperationalDecompositionPerInputEvidence input).canonicalAccounting.total =
      (endogenousOperationalDecompositionPerInputEvidence input).core.run.instrumentedWork :=
  (endogenousOperationalDecompositionPerInputEvidence input).totalWorkExact

/-- Regression 30: the closed generic interface performs actual discovery. -/
theorem regression_concrete_interface_discovers (input : Nat) :
    concreteConstitutiveOperationalInterface.discover
        input
        (growingDiscoverySplitVar input) ≠
      none :=
  concreteInterface_discover_selected input

/-- Regression 28: the projection experiment is indexed by constitution. -/
theorem regression_projection_experiment_uses_constituted_index (input : Nat) :
    projectionSplitVar input =
        growingDiscoverySplitVar (constitutedSearchIndex input) ∧
      projectionRootFormula input =
        symmetricBlockFamily
          (growingDiscoverySplitVar (constitutedSearchIndex input))
          (growingDiscoveryAnchorVar (constitutedSearchIndex input))
          [] :=
  ⟨projectionSplitVar_from_constitution input,
    projectionRootFormula_from_constitution input⟩

/-- Regression 29: producer, provenance, and certificate units are not free. -/
theorem regression_generation_accounting_is_exact (input : Nat) :
    (executeConstitutiveResolution input).stats.generateCalls = input + 1 ∧
      (executeConstitutiveResolution input).stats.provenanceUnits = input + 1 ∧
      (executeConstitutiveResolution input).stats.generationCertificates =
        input + 1 :=
  ⟨(endogenousOperationalDecompositionEvidence input).generationCallsExact,
    (endogenousOperationalDecompositionEvidence input).provenanceUnitsExact,
    (endogenousOperationalDecompositionEvidence input).generationCertificatesExact⟩

/--
Regression 30: the history traversal is failure-aware, and this concrete family
closes its optional discoveries only through the returned successful outcomes.
-/
theorem regression_failure_aware_traversal_is_exact (input : Nat) :
    let run := executeConstitutiveResolution input
    run.discoveryTraversal.execution? = some run.history ∧
      run.discoveryTraversal.discoveryRuns = input + 1 ∧
      run.discoveryTraversal.successfulDiscoveries = input + 1 ∧
      run.discoveryTraversal.failureDepth? = none := by
  exact
    ⟨(endogenousOperationalDecompositionEvidence input).failureAwareTraversalConsumesDiscovery,
      (endogenousOperationalDecompositionEvidence input).discoveryRunsExact,
      (endogenousOperationalDecompositionEvidence input).successfulDiscoveriesExact,
      (endogenousOperationalDecompositionEvidence input).noDiscoveryFailure⟩

/-- Regression 32: every path cardinality is tied to the produced run. -/
theorem regression_all_structural_correspondences (input : Nat) :
    let run := executeConstitutiveResolution input
    run.generatedHistory.stepCount = input + 1 ∧
      run.stats.generatedSteps = input + 1 ∧
      run.discoveryTraversal.successfulDiscoveries = input + 1 ∧
      run.stats.scheduleAtoms = input + 1 ∧
      run.stats.appliedCodeAtoms = input + 1 ∧
      run.stats.validationPrimitiveQueries = input + 1 ∧
      run.stats.executionPrimitiveQueries = input + 1 ∧
      run.stats.compositionCandidates = 0 :=
  executeConstitutiveResolution_correspondences input

theorem regression_input_cannot_replace_applied_output
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.next.assignment run.schedule.entry.var ≠ input.assignment run.schedule.entry.var := by
  rw [sequentialStage_next_from_input, Assignment.flipAt_selected]
  cases input.assignment run.schedule.entry.var <;> intro impossible <;> cases impossible

theorem regression_wrong_source_assignment_rejected
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (other : Assignment) (query : Var)
    (different : other query ≠ input.assignment query) :
    run.sourceContinuation.1 ≠ other := by
  intro substituted
  apply different
  rw [← substituted, run.sourceAssignmentExact]

theorem regression_generation_alone_does_not_supply_relation
    (source : PositiveConstitution examplePresentation) :
    asymmetricConstitutiveInterface.discoverHistory
      (asymmetricConstitutiveInterface.produceHistory source 1).2 = none :=
  produced_step_does_not_imply_discovery source

theorem regression_returned_codes_compile_from_local_paths (input : Nat) :
    (executeConstitutiveResolution input).history.localPath.map LocalPrimitiveAtom.compile =
      (executeConstitutiveResolution input).history.returnedCodes :=
  localPath_compiles_to_returnedCodes _

theorem regression_terminal_readout_is_preserved (input : Nat) :
    let terminal := (executeConstitutiveResolution input).terminal
    terminal.executedVariables.map terminal.assignment = terminal.observedBits :=
  (endogenousOperationalDecompositionEvidence input).terminalReadoutPreserved

theorem regression_measured_comparison_not_list_size (leftRest rightRest : Clause) :
    (compareMeasuredList compareMeasuredLiteral
      (.positive 0 :: leftRest) (.negative 0 :: rightRest)).work = ⟨2, 0⟩ :=
  measuredComparison_short_circuits _ _

theorem regression_measured_discovery_is_reference_discovery {root : Cnf}
    (state : GeneratedStructuralBranchContext root) (candidate : Var) :
    (tryMeasuredCandidate state candidate).result = tryEndogenousFlipCandidate state candidate :=
  tryMeasuredCandidate_exact _ _

theorem regression_no_history_comparison_after_formula_failure :
    let root := GeneratedStructuralBranchContext.root [[Literal.positive 0]]
    let fresh : StructuralDecisionsAvoid 0 root.context.decisions := True.intro
    (searchMeasuredRelation 0 (root.child 0 false fresh) (root.child 0 true fresh)).historyComparison =
      ComparisonWork.zero := rfl

/-- The generic explorer agrees on all returned data, not merely its success bit. -/
theorem regression_generic_exploration_full_data (index : Nat) (candidates : List Var) :
    concreteConstitutiveOperationalInterface.explore index candidates =
      recordedAsGeneric index
        (exploreRecordedCandidates (distinctGrowingDiscoveryRoot index) candidates) :=
  genericExploration_refined index candidates

theorem regression_all_executed_stages_refine_generic (input : Nat) :
    GenericRefinedHistory (executeConstitutiveResolution input).history :=
  (executeConstitutiveResolution input).genericRefinement

theorem regression_execution_consumes_measured_schedule
    {depth : Nat} {input : SequentialAssignment depth} (run : SequentialStageRun depth input) :
    HEq run.execution run.measuredExecution.execution := run.executionFromMeasured

theorem regression_terminal_consumes_measured_reads (input : Nat) :
    (executeConstitutiveResolution input).terminal.observedBits =
      (executeConstitutiveResolution input).terminal.assignmentReadout.bits :=
  (executeConstitutiveResolution input).terminal.observedBitsFromReadout

/-- This read includes the input reader, the label comparison, and the flip. -/
theorem regression_transported_read_not_free :
    (readFlippedAssignment 0 readAlternatingAssignment 0).work.total = 3 ∧
      (readFlippedAssignment 0 readAlternatingAssignment 0).value = false := ⟨rfl, rfl⟩

theorem regression_terminal_reader_bound (depth count : Nat) :
    let history := executeSequentialHistory depth count (initialSequentialAssignment depth)
    let largest := stageSelectedVar (depth + count)
    (readAssignmentQueries history.final.reader history.executedVariables).work.total ≤
      ((largest + 1 + count * (largest + 2)) + 1) * count + 1 :=
  concreteTerminalQueries_bound depth count

/-- The separator is now built from a stage actually retained by the main run. -/
theorem regression_projection_consumes_executed_stage (input : Nat) :
    (executeConstitutiveResolution input).projectionExperiment =
      runIntegratedProjectionExperiment (executeConstitutiveResolution input).history.firstStage :=
  (executeConstitutiveResolution input).projectionExperimentExact

/-- The final evidence package exposes the formal refinement of the §3.1
search/apply/read semantics, so the replacement cannot remain documentary. -/
theorem regression_integrated_projection_refines_section31 (input : Nat) :
    Section31PrimitiveRaccord
      (executeConstitutiveResolution input).history.firstStage :=
  (endogenousOperationalDecompositionEvidence input).projectionUsesSection31Primitives

/-- The successful integrated organization executes one transport atom; the
incompatible organization executes none. Both counts are public run data. -/
theorem regression_integrated_projection_codeAtoms (input : Nat) :
    let run := executeConstitutiveResolution input
    run.projectionExperiment.positiveRun.codeAtoms = 1 ∧
      run.projectionExperiment.negativeRun.codeAtoms = 0 := by
  dsimp only
  exact ⟨(endogenousOperationalDecompositionEvidence input).projectionPositiveCodeAtoms,
    (endogenousOperationalDecompositionEvidence input).projectionNegativeCodeAtoms⟩

/-- The §6 obligations are exposed together for the actual public run. -/
def regression_section6_operational_succession (input : Nat) :
    Section6OperationalSuccessionEvidence (executeConstitutiveResolution input) :=
  (endogenousOperationalDecompositionEvidence input).section6Succession

theorem regression_projection_positive_reads_main_action (input : Nat) :
    let run := executeConstitutiveResolution input
    run.projectionExperiment.positiveRun.terminalBit =
      some (run.history.firstStage.application.output.1 run.history.firstStage.schedule.entry.var) := by
  dsimp only
  rw [(executeConstitutiveResolution input).projectionExperiment.positiveRunExact]
  exact integrated_positive_agrees_with_main _

theorem regression_integrated_projection_not_factors (input : Nat) :
    let head := (executeConstitutiveResolution input).history.firstStage
    ¬ ValueFactorsThrough (integratedInputProjection head)
      (fun organization => (integratedOrganizationObservation head organization).terminalBit) :=
  integrated_projection_not_factors _

/-- Empty clauses still incur extraction visits despite returning no candidates. -/
theorem regression_empty_clause_extraction_is_charged :
    (extractCnfCandidateRun [[]]).candidates = [] ∧
      (extractCnfCandidateRun [[]]).stats.clauseVisits = 1 := ⟨rfl, rfl⟩

theorem regression_discovery_measured_input_bound (formula : Cnf) :
    let run := runRecordedDiscovery (GeneratedStructuralBranchContext.root formula)
    (run.extraction.stats.clauseVisits + run.extraction.stats.literalVisits) +
      (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      discoveryWorkEnvelope (unaryCnfSize formula) :=
  rootDiscovery_with_extraction_bound formula

theorem regression_integrated_discovery_measured_bound (input : Nat) :
    let run := executeConstitutiveResolution input
    (run.measuredComparisonWork.add run.measuredConstructionWork).total ≤
      resolutionLength input * stageDiscoveryWorkEnvelope (input + resolutionLength input) := by
  dsimp only
  rw [(executeConstitutiveResolution input).measuredComparisonWorkExact,
    (executeConstitutiveResolution input).measuredConstructionWorkExact]
  exact historyDiscovery_measured_bound _

theorem regression_integrated_validation_execution_measured_bound (input : Nat) :
    let run := executeConstitutiveResolution input
    (run.measuredValidationWork.add run.measuredExecutionWork).total ≤
      resolutionLength input * (stageRelationWorkEnvelope (input + resolutionLength input) +
        stageRelationWorkEnvelope (input + resolutionLength input)) := by
  dsimp only
  rw [(executeConstitutiveResolution input).measuredValidationWorkExact,
    (executeConstitutiveResolution input).measuredExecutionWorkExact]
  exact historyValidationExecution_measured_bound _

theorem regression_generic_traversal_returns_stored_discoveries (input : Nat) :
    let run := executeConstitutiveResolution input
    HEq (concreteConstitutiveOperationalInterface.discoverHistory run.generatedHistory.asGeneric)
      (some run.history.genericDiscovered) :=
  (executeConstitutiveResolution input).genericTraversalExact

theorem regression_execution_retains_generated_history (input : Nat) :
    (executeConstitutiveResolution input).history.generatedHistory =
      (executeConstitutiveResolution input).generatedHistory :=
  (executeConstitutiveResolution input).generatorsExact

theorem regression_measured_search_input_polynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).measuredSearchWork) :=
  constitutiveMeasuredSearch_inputPolynomial

theorem regression_observed_variable_from_stored_schedule (input : Nat) :
    let terminal := (executeConstitutiveResolution input).terminal
    terminal.variableReadout.result = some terminal.observedVar :=
  (executeConstitutiveResolution input).terminal.observedVarFromReadout

theorem regression_observed_variable_traversal_charged (input : Nat) :
    (executeConstitutiveResolution input).terminal.variableReadout.visits = resolutionLength input + 1 := by
  rw [(executeConstitutiveResolution input).terminal.variableReadoutExact]
  exact SequentialHistory.lastVariableRun_visits _

theorem regression_production_consumes_initialized_endpoint (input : Nat) :
    let run := executeConstitutiveResolution input
    run.production =
      run.constitutiveFeedbackHistory.toProductionRun
        run.threadedInitialGenerationExact :=
  (executeConstitutiveResolution input).productionExact

theorem regression_generated_history_from_counted_producer (input : Nat) :
    (executeConstitutiveResolution input).generatedHistory =
      (executeConstitutiveResolution input).production.history :=
  (executeConstitutiveResolution input).generatedHistoryFromProduction

theorem regression_initialization_calls_charged (input : Nat) :
    (executeConstitutiveResolution input).initialization.generateCalls = input :=
  (initializeConstitutiveHistory_counts input).1

theorem regression_production_calls_charged (input : Nat) :
    (executeConstitutiveResolution input).production.generateCalls = resolutionLength input := by
  let run := executeConstitutiveResolution input
  have generationCanonical :
      run.threadedInitialState.generation = generateCanonicalStage input :=
    run.threadedInitialGenerationExact
  have stats := run.constitutiveFeedbackHistory.productionStats_exact generationCanonical
  exact Eq.trans
    (congrArg ConstitutiveProductionRun.generateCalls run.productionExact)
    stats.1

theorem regression_production_material_emitted (input : Nat) :
    (executeConstitutiveResolution input).production.provenanceUnits = resolutionLength input ∧
      (executeConstitutiveResolution input).production.certificatesProduced =
        resolutionLength input := by
  let run := executeConstitutiveResolution input
  have generationCanonical :
      run.threadedInitialState.generation = generateCanonicalStage input :=
    run.threadedInitialGenerationExact
  have stats := run.constitutiveFeedbackHistory.productionStats_exact generationCanonical
  exact
    ⟨Eq.trans
        (congrArg ConstitutiveProductionRun.provenanceUnits run.productionExact)
        stats.2.2.1,
      Eq.trans
        (congrArg ConstitutiveProductionRun.certificatesProduced run.productionExact)
        stats.2.2.2⟩

theorem regression_stage_generation_stats_from_producer {depth : Nat}
    {input : SequentialAssignment depth} (run : SequentialStageRun depth input) :
    run.stats.provenanceUnits = run.generation.provenanceUnits ∧
      run.stats.generationCertificates = run.generation.certificatesProduced :=
  ⟨rfl, rfl⟩

theorem regression_measured_accounting_not_inflatable {input : Nat}
    (first second : CanonicalMeasuredAccounting input) : first.total = second.total :=
  canonicalMeasuredAccounting_not_inflatable first second

theorem regression_main_measured_phases_polynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).mainInstrumentedWork) :=
  mainInstrumentedWork_inputPolynomial

theorem regression_total_instrumented_work_polynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).instrumentedWork) :=
  instrumentedWork_inputPolynomial

theorem regression_phase_ownership_unique (phase : MeasuredPhase) :
    phaseOccurrences phase measuredPhases = 1 := measuredPhase_occurs_once phase

theorem regression_measured_synthesis_same_run (input : Nat) :
    MeasuredConstitutiveEvidence (executeConstitutiveResolution input) :=
  measuredConstitutiveEvidence _

theorem regression_projection_accounting_included (input : Nat) :
    let run := executeConstitutiveResolution input
    run.instrumentedWork = run.mainInstrumentedWork + run.projectionExperiment.measuredWork :=
  (executeConstitutiveResolution input).instrumentedWork_partition

theorem regression_measured_production_strict {first second : Nat} (before : first < second) :
    (executeConstitutiveResolution first).productionCalls <
      (executeConstitutiveResolution second).productionCalls := measuredProductionCalls_strict before

theorem regression_instrumented_family : MeasuredConstitutiveFamily := measuredConstitutiveFamily

def regression_integrated_measured_family : EndogenousOperationalDecompositionFamily :=
  endogenousOperationalDecompositionFamily

theorem regression_projection_measured_bound (input : Nat) :
    (executeConstitutiveResolution input).projectionExperiment.measuredWork ≤
      integratedProjectionEnvelope (executeConstitutiveResolution input).history.firstStage :=
  (executeConstitutiveResolution input).projectionWork_bound

theorem regression_every_action_changes_produced_assignment {depth : Nat}
    {input : SequentialAssignment depth} (run : SequentialStageRun depth input) :
    run.next.assignment ≠ input.assignment := executedStage_next_not_input run

theorem regression_full_step_includes_opening (depth : Nat) (input : SequentialAssignment depth) :
    (executeFullConstitutiveStage depth input).1 =
      (executeSequentialStage depth input).next.assignment :=
  executeFullConstitutiveStage_is_next depth input

def regression_every_stage_is_a_full_step (input : Nat) :
    FullHistoryExecution (executeConstitutiveResolution input).history :=
  (executeConstitutiveResolution input).fullHistoryExecution

def regression_every_stage_carries_four_roles (input : Nat) :
    ConstitutiveRoleHistory (executeConstitutiveResolution input).history :=
  (executeConstitutiveResolution input).roleHistory

/-! Counterprobes for the strong constitutive feedback of §8. -/

theorem regression_public_history_is_causal (input : Nat) :
    (executeConstitutiveResolution input).history =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory.toSequentialHistory :=
  (executeConstitutiveResolution input).historyFromCausalExecution

theorem regression_causal_history_matches_reference_after_execution (input : Nat) :
    (executeConstitutiveResolution input).constitutiveFeedbackHistory.toSequentialHistory =
      resolutionHistory input :=
  Eq.trans
    (executeConstitutiveResolution input).historyFromCausalExecution.symm
    (executeConstitutiveResolution input).historyExact

theorem regression_stage_is_constructed_from_returned_discovery
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (built : ConstructedThreadedStageRun state) :
    built.stage = executeSequentialStageFromActiveRecorded depth assignment state.generation
      built.run.discoveryRun.asRecorded
      built.run.discoveryRun.extractionExact
      built.run.discovery built.run.recordedDiscoveryFound built.run.discoveryExact
      built.run.discoveryWorkLeCanonical :=
  built.run.stageFromDiscovery

theorem regression_provenance_filter_matches_prior_history_filter
    (decisions : List StructuralBranchDecision)
    (candidates : List Var) :
    let provenance := decisions.map (fun decision => decision.var)
    let byProvenance := filterCandidatesByProvenance provenance candidates
    let byHistory := filterCandidatesByHistory decisions candidates
    byProvenance.retained = byHistory.retained ∧
      byProvenance.rejected = byHistory.rejected ∧
      byProvenance.trace = byHistory.trace ∧
      byProvenance.visits = byHistory.visits :=
  filterCandidatesByProvenance_matches_history decisions candidates

theorem regression_feedback_next_contains_executed_output_and_decision_history
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.threadedAssignment.assignment = stage.application.output.1 ∧
      run.nextRun.next.decisions =
        ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions ∧
      run.nextRun.next.provenance =
        stageSelectedVar (depth + 1) :: state.provenance :=
  roleStage_output_constitutes_nextOperationalState run

theorem regression_feedback_provenance_from_scheduled_operation
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.provenance =
      stage.schedule.entry.var :: state.provenance :=
  run.nextRun.provenanceFromScheduledOperation

theorem regression_next_discovery_consumes_produced_provenance
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    nextDiscovery.candidates =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).retained ∧
      nextDiscovery.filtering.visits =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).visits :=
  run.nextDiscoveryConsumesProducedProvenance

theorem regression_feedback_search_seed_from_produced_state
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.searchSeed = executedProducedSearchSeed stage :=
  run.nextRun.searchSeedFromProducedState

theorem regression_next_discovery_consumes_retained_search_seed
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    run.nextRun.next.searchSeed = executedProducedSearchSeed stage ∧
      nextDiscovery.generated =
        measuredGeneratedExtractionFromSeed
          run.nextRun.next.generation
          run.nextRun.next.searchSeed
          run.nextRun.next.searchSeedExact :=
  run.nextDiscoveryConsumesRetainedSearchSeed

theorem regression_next_operational_state_consumes_generated_target
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.generation =
        generateCanonicalStageFromSource state.generation.target state.generation.targetExact ∧
      run.nextRun.next.threadedAssignment.assignment = stage.next.assignment :=
  ⟨run.nextRun.generationFromProducedTarget, run.nextRun.assignmentFromExecution⟩

theorem regression_old_input_cannot_replace_feedback_output
    {depth : Nat} {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    stage.next.assignment stage.schedule.entry.var ≠
      assignment.assignment stage.schedule.entry.var :=
  regression_input_cannot_replace_applied_output stage

theorem regression_other_decision_history_changes_next_discovery (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠
      nextDiscoveryOutcome (nextDiscoveryConstitution depth .blocked) :=
  nextDiscovery_outcome_different depth

theorem regression_same_depth_projection_different_next_discovery (depth : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
        nextDiscoveryProjection (nextDiscoveryConstitution depth .blocked) ∧
      nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠
        nextDiscoveryOutcome (nextDiscoveryConstitution depth .blocked) :=
  ⟨nextDiscovery_projection_equal depth, nextDiscovery_outcome_different depth⟩

theorem regression_next_discovery_not_depth_factor (depth : Nat) :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := depth))
        (nextDiscoveryOutcome (depth := depth)) :=
  nextDiscovery_not_factors depth

theorem regression_feedback_relation_is_from_transmitted_run
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.discovered? = some stage.discovery :=
  run.relationFromTransmittedState

theorem regression_feedback_code_is_from_discovered_relation
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.execution.code = stage.schedule.entry.code ∧
      stage.application.output =
        (stage.execution.code.eval
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
            stage.schedule.entry.var)).map stage.sourceContinuation :=
  ⟨run.returnedCodeFromThatRelation, run.executedOutputFromThatCode⟩

theorem regression_feedback_failure_produces_nothing (depth : Nat) :
    (feedbackFailureArtifacts depth).codeAtoms = 0 ∧
      (feedbackFailureArtifacts depth).nextProduced = false ∧
      (feedbackFailureArtifacts depth).terminalProduced = false := by
  rw [feedbackFailureArtifacts_exact]
  exact ⟨rfl, rfl, rfl⟩

theorem regression_failed_discovery_constructs_no_stage (depth : Nat) :
    (runThreadedNextDiscovery
      (blockedNextDiscoveryState depth).state).outcome.discovered? = none :=
  blocked_discovery_constructs_no_stage depth

theorem regression_failed_discovery_has_no_positive_history (depth count : Nat)
    (history : ConstitutiveExecutionHistory
      (count := count + 1) (blockedNextDiscoveryState depth).state) : False :=
  failedDiscovery_noPositiveHistory _ (nextDiscovery_blocked_none depth) history

theorem regression_authoritative_attempts_strict (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts :=
  executeConstitutiveResolution_attempts_strict input

theorem regression_blocked_state_is_constructed_from_child (depth : Nat) :
    (blockedNextDiscoveryState depth).state.decisions =
        (blockedNextDiscoveryCarrier depth).context.decisions ∧
      (blockedNextDiscoveryState depth).state.provenance =
        (blockedNextDiscoveryCarrier depth).context.decisions.map
          (fun decision => decision.var) := by
  exact
    ⟨(blockedNextDiscoveryConstruction depth).decisionsFromChild,
      (blockedNextDiscoveryConstruction depth).provenanceFromChild⟩

theorem regression_separator_states_share_executed_origin (depth : Nat) :
      (nextDiscoveryConstitution depth .retained).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next ∧
      (nextDiscoveryConstitution depth .blocked).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next :=
  nextDiscovery_states_share_executed_origin depth

theorem regression_separator_states_are_complete_and_distinct (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions ≠
      (nextDiscoveryConstitution depth .blocked).packed.state.decisions :=
  nextDiscovery_histories_distinct depth

theorem regression_feedback_inspects_no_global_composition (input : Nat) :
    (executeConstitutiveResolution input).stats.compositionCandidates = 0 :=
  executeConstitutiveResolution_noGlobalComposition input

theorem regression_prior_integrated_results_remain_available (input : Nat) :
    Section31PrimitiveRaccord (executeConstitutiveResolution input).history.firstStage ∧
      Nonempty (Section6OperationalSuccessionEvidence (executeConstitutiveResolution input)) ∧
      Nonempty (EndogenousOperationalDecompositionPerInputEvidence input) :=
  ⟨regression_integrated_projection_refines_section31 input,
    ⟨regression_section6_operational_succession input⟩,
    ⟨endogenousOperationalDecompositionPerInputEvidence input⟩⟩

theorem regression_feedback_accounting_is_canonical (input : Nat) :
    let run := executeConstitutiveResolution input
    run.phaseWork .decisionAccumulation = run.feedbackStats.decisionAccumulations ∧
      run.phaseWork .decisionProvenance = run.feedbackStats.provenanceVisits ∧
      run.phaseWork .historyFiltering =
        run.feedbackStats.historyFilteringVisits := by
  exact ⟨rfl, rfl, rfl⟩

theorem regression_public_run_is_single_pass (input : Nat) :
    let run := executeConstitutiveResolution input
    run.history = run.constitutiveFeedbackHistory.toSequentialHistory ∧
      run.generatedHistory = run.constitutiveFeedbackHistory.toGeneratedHistory ∧
      run.discoveryTraversal = run.constitutiveFeedbackHistory.toDiscoveryTraversal := by
  let run := executeConstitutiveResolution input
  exact ⟨run.historyFromCausalExecution, run.historyConsumesGeneration,
    run.discoveryTraversalExact⟩

theorem regression_reachable_history_changes_candidate_trace (depth : Nat) :
    (runThreadedNextDiscovery
        (retainedNextDiscoveryState depth).state).candidates ≠
      (runThreadedNextDiscovery
        (erasedNextDiscoveryState depth).state).candidates :=
  reachableHistory_candidateTraces_different depth

theorem regression_filtering_cost_is_owned_once (input : Nat) :
    let run := executeConstitutiveResolution input
    run.phaseWork .historyFiltering =
      run.constitutiveFeedbackHistory.feedbackStats.historyFilteringVisits := by
  let run := executeConstitutiveResolution input
  change run.feedbackStats.historyFilteringVisits =
    run.constitutiveFeedbackHistory.feedbackStats.historyFilteringVisits
  exact congrArg (fun stats => stats.historyFilteringVisits) run.feedbackStatsExact

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_full_step_includes_opening
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_every_action_changes_produced_assignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_instrumented_family
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_measured_family
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_projection_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_synthesis_same_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_projection_accounting_included
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_production_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_accounting_not_inflatable
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_main_measured_phases_polynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_total_instrumented_work_polynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_phase_ownership_unique
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_observed_variable_from_stored_schedule
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_observed_variable_traversal_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_production_consumes_initialized_endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generated_history_from_counted_producer
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_initialization_calls_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_production_calls_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_production_material_emitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_stage_generation_stats_from_producer
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_search_input_polynomial
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generic_traversal_returns_stored_discoveries
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_execution_retains_generated_history
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_empty_clause_extraction_is_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_discovery_measured_input_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_discovery_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_validation_execution_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_projection_consumes_executed_stage
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_projection_refines_section31
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_projection_codeAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_section6_operational_succession
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_projection_positive_reads_main_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_integrated_projection_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generic_exploration_full_data
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_all_executed_stages_refine_generic
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_execution_consumes_measured_schedule
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_terminal_consumes_measured_reads
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_transported_read_not_free
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_terminal_reader_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_input_cannot_replace_applied_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_wrong_source_assignment_rejected
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generation_alone_does_not_supply_relation
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_returned_codes_compile_from_local_paths
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_terminal_readout_is_preserved
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_comparison_not_list_size
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_measured_discovery_is_reference_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_no_history_comparison_after_formula_failure
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generated_target_not_injected
#print axioms ConstitutiveSearch.EndogenousDecomposition.external_target_cannot_construct_typed_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_successive_operational_indices_differ
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_relation_substitution_rejected
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_code_is_applied
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_code_application_is_instrumented
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_application_fields_from_recursive_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_application_stats_are_run_emitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_applied_code_preserves_acceptance
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_concrete_source_is_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_concrete_output_is_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_selected_variable_is_discovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_discovery_not_constant
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_no_factorization_by_input_and_projection
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_witnesses_share_input
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_index_not_spectator
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_instrumented_work_grows
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_tested_candidates_are_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_cost_is_run_derived
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_structural_profile_is_run_derived
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_no_global_closure
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_provenance_erasure_is_observable
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_terminal_is_trace_derived
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_decision_reads_executed_bits
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generated_history_is_consumed
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_encoded_input_size
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_relation_has_discovery_provenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_phase_accounting_is_canonical
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_terminal_visits_are_executed
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_formula_comparison_surface_grows
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_detailed_discovery_work_is_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_relation_queries_are_charged
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_extracted_candidates_are_run_emitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_validated_atoms_are_run_emitted
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_section7_accounting_is_in_final_family
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_accounting_exact_in_final_per_input
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_concrete_interface_discovers
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_projection_experiment_uses_constituted_index
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_generation_accounting_is_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_failure_aware_traversal_is_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_all_structural_correspondences
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_public_history_is_causal
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_causal_history_matches_reference_after_execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_stage_is_constructed_from_returned_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_provenance_filter_matches_prior_history_filter
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_next_contains_executed_output_and_decision_history
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_provenance_from_scheduled_operation
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_next_discovery_consumes_produced_provenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_search_seed_from_produced_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_next_discovery_consumes_retained_search_seed
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_next_operational_state_consumes_generated_target
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_old_input_cannot_replace_feedback_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_other_decision_history_changes_next_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_same_depth_projection_different_next_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_next_discovery_not_depth_factor
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_relation_is_from_transmitted_run
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_code_is_from_discovered_relation
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_failure_produces_nothing
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_failed_discovery_constructs_no_stage
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_failed_discovery_has_no_positive_history
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_authoritative_attempts_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_blocked_state_is_constructed_from_child
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_separator_states_share_executed_origin
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_separator_states_are_complete_and_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_inspects_no_global_composition
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_prior_integrated_results_remain_available
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_feedback_accounting_is_canonical
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_public_run_is_single_pass
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_reachable_history_changes_candidate_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.regression_filtering_cost_is_owned_once
/- AXIOM_AUDIT_END -/
