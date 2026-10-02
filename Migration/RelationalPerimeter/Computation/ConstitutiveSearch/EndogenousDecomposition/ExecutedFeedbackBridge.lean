import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory

/-!
# Existing endogenous production on the authoritative executed history

This bridge reuses the established discovery, action, absorption and feedback
proofs. It does not rerun discovery or introduce a second source-profile carrier.
The recursive predicate follows the very heads and dependent tails from which
the public relational roles and operational regime are obtained.
-/
namespace ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback
open ConstitutiveSearch.SAT

/-- Facts about one actual step; none is inferred from an obligation width. -/
structure StepFacts {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Prop where
  discoveredFromSource :
    (runThreadedNextDiscovery state).outcome.discovered? = some stage.discovery
  actionFromDiscovery : stage.application.output =
    stage.schedule.entry.relation.mapContinuation stage.sourceContinuation
  outputBecomesNext : stage.application.output.1 =
    run.nextRun.next.threadedAssignment.assignment
  decisionBecomesNext : run.nextRun.next.decisions =
    executedBranchDecision stage :: state.decisions
  provenanceBecomesNext : run.nextRun.next.provenance =
    stage.schedule.entry.var :: state.provenance
  seedBecomesNext : run.nextRun.next.searchSeed = executedProducedSearchSeed stage
  nextCandidateDomain :
    (runThreadedNextDiscovery run.nextRun.next).candidates =
      (filterCandidatesByProvenance (stage.schedule.entry.var :: state.provenance)
        (runThreadedNextDiscovery run.nextRun.next).generated.extraction.candidates).retained
  nextSeedIsUsed : (runThreadedNextDiscovery run.nextRun.next).generated =
    measuredGeneratedExtractionFromSeed run.nextRun.next.generation
      run.nextRun.next.searchSeed run.nextRun.next.searchSeedExact
  siblingStatesDistinct : (executedOpening run).left ≠ (executedOpening run).right
  removedSiblingStillViable :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)).Viable
        stage.schedule.entry.source
  absorptionPreservesViability :
    FrontierViable
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
      (executedOpenedFrontier run) ↔
    FrontierViable
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
      (executedSiblingReduction run).retained
  preservesArbitraryContinuations :
    ∀ c : GeneratedStructuralBranchContinuation (executedOpening run).left,
      GeneratedStructuralBranchAccept (executedOpening run).left c →
      GeneratedStructuralBranchAccept (executedOpening run).right
        (stage.discovery.relation.mapContinuation c)

/-- Reuse the existing step-level theorems on this exact executed run. -/
theorem stepFacts {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : StepFacts run :=
  { discoveredFromSource :=
      run.discoveryRunExact ▸ executedTransformation_from_discoveryOutcome run
    actionFromDiscovery := stageApplication_eq_returnedRelationMap run
    outputBecomesNext := executedOutput_eq_nextOperationalAssignment run
    decisionBecomesNext := run.nextRun.decisionsFromExecutedOutput
    provenanceBecomesNext := run.nextRun.provenanceFromScheduledOperation
    seedBecomesNext := run.nextRun.searchSeedFromProducedState
    nextCandidateDomain := run.nextDiscoveryConsumesProducedProvenance.1
    nextSeedIsUsed := run.nextDiscoveryConsumesRetainedSearchSeed.2
    siblingStatesDistinct := executedSiblingStates_distinct run
    removedSiblingStillViable := executedSourceSibling_viable run
    absorptionPreservesViability := (executedSiblingReduction run).preservation.viable_iff
    preservesArbitraryContinuations := executedSiblingReduction_preservesAccept run }

/-- The profile action is the discovered action, not a new or prescribed map. -/
theorem producedRoleAction_is_discovered
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (production : ExecutedStageOperationalProduction context (causalStageOfThreadedStage run))
    (c : GeneratedStructuralBranchContinuation (executedOpening run).left) :
    (compileRoleStageAtom production.decomposition.role).action c =
      stage.discovery.relation.mapContinuation c := by
  exact Eq.trans
    (compileRoleStageAtom_action_exact production.decomposition.role c)
    (congrArg (fun relation : GeneratedStructuralFlipAtRelation stage.discovery.var
      (executedOpening run).left (executedOpening run).right =>
      relation.mapContinuation c)
      production.decomposition.role.reconstructedRelationExact)

/-- Apply existing feedback facts at every actual head of the fused history. -/
def Along :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
    CausalOperationalExecutionHistory (_count := count) state context → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .step stage run production tail =>
      StepFacts run ∧
      RelationalRoleConstitutionExact production.decomposition.role ∧
      (∀ c : GeneratedStructuralBranchContinuation (executedOpening run).left,
        (compileRoleStageAtom production.decomposition.role).action c =
          stage.discovery.relation.mapContinuation c) ∧
      Along tail

/-- Structural induction preserves the original state-indexed dependency. -/
theorem along :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
    (history : CausalOperationalExecutionHistory (_count := count) state context) →
    Along history
  | _, _, _, _, _, .nil _ _ => True.intro
  | _, _, _, _, _, .step _ run production tail =>
      ⟨stepFacts run,
        (by rw [production.decomposition.roleExact]
            exact relationalConstitutiveRoleStage_exact _),
        producedRoleAction_is_discovered run production,
        along tail⟩

/-- Numerical observation of the existing local frontier objects, in run order. -/
def widthTrace :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
    CausalOperationalExecutionHistory (_count := count) state context → List Nat
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .step _ run _ tail =>
      executedStageWidthTrace run ++ widthTrace tail

/-- The transient trace is the existing trace of the same history's erasure. -/
theorem widthTrace_existing :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
    (history : CausalOperationalExecutionHistory (_count := count) state context) →
    widthTrace history =
      executedWidthTrace (buildThreadedConstitutiveRoleHistory history.instrumented)
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .step _ run _ tail =>
      congrArg (List.append (executedStageWidthTrace run)) (widthTrace_existing tail)

/-- Reuse the established bound; no exhaustive profile list is executed here. -/
theorem widthTrace_le_two
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (history : CausalOperationalExecutionHistory (_count := count) state context) :
    WidthTraceAtMost 2 (widthTrace history) := by
  rw [widthTrace_existing]
  exact executedWidthTrace_le_two (buildThreadedConstitutiveRoleHistory history.instrumented)

/-- The proof applies uniformly, including all dependent continuations. -/
theorem public_along (input : Nat) : Along (publicCausalOperationalExecution input) :=
  along (publicCausalOperationalExecution input)

/-- Transient frontier bound for the very history defining the public roles. -/
theorem public_widthTrace_le_two (input : Nat) :
    WidthTraceAtMost 2 (widthTrace (publicCausalOperationalExecution input)) :=
  widthTrace_le_two (publicCausalOperationalExecution input)

end ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.StepFacts
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.stepFacts
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.producedRoleAction_is_discovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.Along
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.along
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.widthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.widthTrace_existing
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.widthTrace_le_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.public_along
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedFeedback.public_widthTrace_le_two
/- AXIOM_AUDIT_END -/
