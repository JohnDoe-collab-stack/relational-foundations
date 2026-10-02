import RelationalPerimeter

/-!
# Regression gate for endogenous operational stability

These checks import only the public root.  They protect the semantic raccords,
not merely the final numerical width statements.
-/

namespace Tests.EndogenousOperationalStabilityRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

/-- The public construction closes every premise at input zero. -/
def publicEvidenceZero : OperationalStabilityEvidence 0 :=
  operationalStabilityEvidence 0

theorem publicStageCountZero :
    operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory = 1 :=
  operational_stage_count_exact 0

theorem publicStructuralWidthZero :
    structuralWidth (executeConstitutiveResolution 0).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  structural_width_is_exponential 0

theorem publicPendingWidthZero :
    pendingWidth (executeConstitutiveResolution 0).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  pending_operational_width_is_exponential 0

theorem publicRetainedWidthZero :
    executedWidth (executeConstitutiveResolution 0).feedbackRoleHistory = 1 :=
  retained_operational_width_is_one 0

theorem publicTransientBoundZero :
    WidthTraceAtMost 2
      (executedWidthTrace
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  transient_operational_width_is_bounded 0

theorem publicStrictSeparationZero :
    executedWidth (executeConstitutiveResolution 0).feedbackRoleHistory <
      pendingWidth (executeConstitutiveResolution 0).feedbackRoleHistory :=
  retained_width_is_strictly_below_pending 0

theorem publicMeasuredFailedMajorityZero :
    9 * (nextDiscoveryCommonOrigin 0).run.discoveryRun.outcome.attempts ≤
      10 * (executedDiscoveryWorkEvidence
        (nextDiscoveryCommonOrigin 0).run).search.failedCandidates.length :=
  initial_discovery_has_measured_failed_majority 0

/-- Every public structural profile is positively accepted and is normalized
through the executed transport history. -/
def normalizeEveryPublicStructuralProfileZero
    (profile : StructuralObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    OperationalAcceptedPayload
      (executeConstitutiveResolution 0).feedbackRoleHistory :=
  publicEvidenceZero.normalizeAcceptedPayload profile
    (publicEvidenceZero.acceptedPayload profile)

theorem publicReductionHistoryIsExactZero :
    publicEvidenceZero.reductions =
      buildExecutedOperationalReductionHistory
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  publicEvidenceZero.reductionsExact

theorem publicDiscoveryWorkIsExactZero :
    publicEvidenceZero.discoveryWork =
      buildExecutedDiscoveryWorkHistory
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  publicEvidenceZero.discoveryWorkExact

theorem publicProjectionHistoryIsExactZero :
    publicEvidenceZero.extensionalProjection =
      buildExtensionalOperationalStabilityHistory
        (executeConstitutiveResolution 0).feedbackRoleHistory :=
  publicEvidenceZero.extensionalProjectionExact

theorem publicNormalizerIsExecutedZero
    (profile : StructuralObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory)
    (payload : StructuralAcceptedPayload
      (executeConstitutiveResolution 0).feedbackRoleHistory profile) :
    publicEvidenceZero.normalizeAcceptedPayload profile payload =
      normalizeStructuralAcceptedPayload
        (executeConstitutiveResolution 0).feedbackRoleHistory profile payload :=
  publicEvidenceZero.normalizeAcceptedPayloadExact profile payload

/-- The measured prefix, not a decorative counter, determines attempts. -/
theorem measuredPrefixDeterminesAttempts {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.attempts =
      (executedDiscoveryWorkEvidence run).search.failedCandidates.length + 1 :=
  (executedDiscoveryWorkEvidence run).attemptsExact

theorem measuredPrefixContainsOnlyFailures {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    AllMeasuredCandidatesFail
      (constructStage (depth + 1)).operationalRoot
      (executedDiscoveryWorkEvidence run).search.failedCandidates :=
  (executedDiscoveryWorkEvidence run).failuresMeasured

/-- Opening is available before any operational relation is added to its
relation-free view. -/
theorem actualOpeningIsRelationFree {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    EndogenousFlipDiscovery.openingView stage.discovery =
      { var := stage.discovery.var
        fresh := stage.discovery.fresh
        split := generatedStructuralSplit
          (constructStage (depth + 1)).operationalRoot
          stage.discovery.var stage.discovery.fresh } :=
  executedOpening_exact run

/-- The transformation consumed by the reduction is the one returned by the
recorded executed search. -/
theorem actualDiscoveryOutcomeIsAuthoritative {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.discovered? = some stage.discovery :=
  (executedOperationalReductionEvidence run).outcomeExact

theorem actualDiscoveredTransportChangesSameOpeningWidth {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stageOperationalWidth
        (system := generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        (left := (executedOpening run).left)
        (right := (executedOpening run).right)
        none = 2 ∧
      stageOperationalWidth (executedOperationalStatus run) = 1 :=
  discovered_transport_reduces_same_opening_width run

theorem actualRetainedTargetIsExact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedSiblingReduction run).retained =
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh] :=
  (executedOperationalReductionEvidence run).retainedExact

/-- The left branch of the reduction uses the discovered total map. -/
theorem actualLeftActionUsesDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.head continuation) =
      .head (stage.discovery.relation.mapContinuation continuation) :=
  (executedOperationalReductionEvidence run).leftActionExact continuation

theorem actualRightActionIsRetained {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.tail (.head continuation)) = .head continuation :=
  (executedOperationalReductionEvidence run).rightActionExact continuation

theorem actualLeftActionPreservesCriterion {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh))
    (accepted : GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh) continuation) :
    GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)
      (stage.discovery.relation.mapContinuation continuation) :=
  (executedOperationalReductionEvidence run).criterionPreserved
    continuation accepted

theorem fullReductionIsEstablishedConstitutiveStep {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedFullPreservation run =
      EndogenousFlipDiscovery.fullStepPreservation stage.discovery :=
  executedFullPreservation_eq_discoveryFullStep run

theorem acceptedLeftPayloadUsesDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    (normalizeLocalAcceptedPayload run false payload).1 =
      stage.discovery.relation.mapContinuation payload.1 :=
  normalizeLocalAcceptedPayload_left_exact run payload

theorem absorbedSiblingRemainsViableAndDistinct {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
        stage.schedule.entry.source ∧
      (constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var false stage.discovery.fresh ≠
        (constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var true stage.discovery.fresh :=
  ⟨executedSourceSibling_viable run,
    executedSiblingStates_distinct run⟩

theorem retainedSiblingRemainsViable {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
        stage.schedule.entry.target :=
  executedTargetSibling_viable run

theorem executedApplicationUsesReturnedRelation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.application.output =
      stage.schedule.entry.relation.mapContinuation stage.sourceContinuation :=
  (executedOperationalReductionEvidence run).applicationUsesReturnedRelation

theorem executedOutputFeedsNextState {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.application.output.1 =
      run.nextRun.next.threadedAssignment.assignment :=
  (executedOperationalReductionEvidence run).outputConstitutesNext

theorem publicStructuralCarrierCompleteZero
    (profile : StructuralObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    List.Mem profile
      (structuralFrontier
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  structuralFrontier_complete _ profile

theorem publicStructuralCarrierNoDuplicatesZero :
    (structuralFrontier
      (executeConstitutiveResolution 0).feedbackRoleHistory).Nodup :=
  structuralFrontier_nodup _

theorem publicPendingCarrierCompleteZero
    (profile : PendingOperationalObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    List.Mem profile
      (pendingFrontier
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  publicEvidenceZero.pendingComplete profile

theorem publicPendingCarrierNoDuplicatesZero :
    (pendingFrontier
      (executeConstitutiveResolution 0).feedbackRoleHistory).Nodup :=
  publicEvidenceZero.pendingNoDuplicates

theorem publicOperationalCarrierCompleteZero
    (profile : OperationalObligation
      (executeConstitutiveResolution 0).feedbackRoleHistory) :
    List.Mem profile
      (operationalFrontier
        (executeConstitutiveResolution 0).feedbackRoleHistory) :=
  operationalFrontier_complete _ profile

theorem publicOperationalCarrierNoDuplicatesZero :
    (operationalFrontier
      (executeConstitutiveResolution 0).feedbackRoleHistory).Nodup :=
  operationalFrontier_nodup _

theorem actualStageTraceComesFromFrontiers {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run = [1, 2, 1] :=
  executedStageWidthTrace_exact run

theorem actualStageTraceIsFrontierProjection {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run =
      (executedStageFrontiers run).map List.length :=
  executedStageWidthTrace_from_frontiers run

theorem executedSystemHasNonFactorizingTotalActions {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (ExecutedExtensionalSeparator.discoveredTransport run).map
        (ExecutedExtensionalSeparator.alternateContinuation run) ≠
      (ExecutedExtensionalSeparator.observedConstantTransport run).map
        (ExecutedExtensionalSeparator.alternateContinuation run) :=
  ExecutedExtensionalSeparator.different_total_action run

theorem comparisonMatchesActualExecutedObservation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (ExecutedExtensionalSeparator.observedConstantTransport run).map
        (executedStepToExtensionalView run).observedSource =
      (executedStepToExtensionalView run).observedRetained :=
  comparison_transport_matches_executed_observation run

theorem projectedObservedActionIsExecuted {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).observedRetained =
      stage.schedule.entry.relation.mapContinuation
        (executedStepToExtensionalView run).observedSource :=
  extensionalView_observedOutput_exact run

theorem projectedTraceIsExecuted {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).widthTrace =
      executedStageWidthTrace run :=
  extensionalView_widthTrace_exact run

theorem executedViewIsDiscoveredProjection {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      transportToExtensionalStabilityView
        (ExecutedExtensionalSeparator.discoveredTransport run)
        stage.sourceContinuation stage.sourceAccepted
        (executedStageWidthTrace run) (executedStageWidthReadoutBound run) :=
  executed_extensional_view_is_discovered_projection run

theorem executedProjectedViewsAreEqual {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExecutedExtensionalSeparator.executedTransportProjection run
        (ExecutedExtensionalSeparator.discoveredTransport run) =
      ExecutedExtensionalSeparator.executedTransportProjection run
        (ExecutedExtensionalSeparator.observedConstantTransport run) :=
  ExecutedExtensionalSeparator.same_extensional_view run

/-- Regression on the production theorem's exact abstract factorization type.
This pins `operational_action_not_factors_on_executed_system` itself, not only
the public wrapper, so the production declaration cannot regress to the former
pair-specific recovery-hypothesis statement while the wrapper is re-proved
elsewhere. -/
theorem productionExecutedNonFactorizationHasAbstractType {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ActionFactorsThrough
      (ExecutedExtensionalSeparator.executedTransportProjection run)
      (ExecutedExtensionalSeparator.executedTransportAction run) :=
  ExecutedExtensionalSeparator.operational_action_not_factors_on_executed_system
    run

/-- Regression on the public wrapper's matching abstract factorization type. -/
theorem executedTotalActionDoesNotFactorThroughProjectedView {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ActionFactorsThrough
      (ExecutedExtensionalSeparator.executedTransportProjection run)
      (ExecutedExtensionalSeparator.executedTransportAction run) :=
  executed_state_width_view_does_not_determine_total_action run

/-- Equal width does not license a wrong retained target. -/
theorem wrongSingletonStillRejected {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (wrongSingleton run).length =
        (executedSiblingReduction run).retained.length ∧
      wrongSingleton run ≠ (executedSiblingReduction run).retained :=
  ⟨Eq.trans (wrongSingleton_width run)
      (executedSiblingReduction_width run).symm,
    wrongSingleton_ne_executedRetained run⟩

theorem separatorSameExecutedOutput :
    ExtensionalSeparator.preservingTransport.map
        ExtensionalSeparator.preservingView.observedSource =
      ExtensionalSeparator.collapsingTransport.map
        ExtensionalSeparator.collapsingView.observedSource :=
  ExtensionalSeparator.same_executed_output

theorem separatorProjectedViewsEqual :
    ExtensionalSeparator.preservingView =
      ExtensionalSeparator.collapsingView :=
  ExtensionalSeparator.same_extensional_stability_view

theorem separatorDifferentTotalAction :
    ExtensionalSeparator.preservingTransport.map true ≠
      ExtensionalSeparator.collapsingTransport.map true :=
  ExtensionalSeparator.different_arbitrary_continuation_action

theorem stateWidthViewCannotRecoverTotalAction :
    ¬ ActionFactorsThrough
      ExtensionalSeparator.projection
      ExtensionalSeparator.action :=
  ExtensionalSeparator.operational_action_not_factors_through_extensional_view

namespace ProjectionCollisionRegression

/-- A projection whose two selected values are propositionally equal but not
definitionally the same expression for an arbitrary tail. -/
def projection (tail : List Nat) : Bool → List Nat
  | false => tail ++ []
  | true => tail

def action : Bool → Bool → Bool
  | false => fun value => value
  | true => fun _ => false

theorem sameProjection (tail : List Nat) :
    projection tail false = projection tail true := by
  change tail ++ [] = tail
  induction tail with
  | nil => rfl
  | cons head rest ih =>
      change head :: (rest ++ []) = head :: rest
      rw [ih]

theorem differentAction :
    action false true ≠ action true true := by
  intro impossible
  exact Bool.noConfusion impossible

def collision (tail : List Nat) :
    ActionProjectionCollision (projection tail) action :=
  { first := false
    second := true
    sameProjection := sameProjection tail
    argument := true
    differentAction := differentAction }

/-- The generic theorem genuinely consumes a propositional projection equality;
the regression does not rely on the executed separator's definitional equality. -/
theorem actionDoesNotFactorThroughPropositionallyEqualProjection
    (tail : List Nat) :
    ¬ ActionFactorsThrough (projection tail) action :=
  action_not_factors_of_projection_collision (collision tail)

end ProjectionCollisionRegression

end Tests.EndogenousOperationalStabilityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.EndogenousOperationalStabilityRegression.publicEvidenceZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStageCountZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicPendingWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicRetainedWidthZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicTransientBoundZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStrictSeparationZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicMeasuredFailedMajorityZero
#print axioms Tests.EndogenousOperationalStabilityRegression.normalizeEveryPublicStructuralProfileZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicReductionHistoryIsExactZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicDiscoveryWorkIsExactZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicProjectionHistoryIsExactZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicNormalizerIsExecutedZero
#print axioms Tests.EndogenousOperationalStabilityRegression.measuredPrefixDeterminesAttempts
#print axioms Tests.EndogenousOperationalStabilityRegression.measuredPrefixContainsOnlyFailures
#print axioms Tests.EndogenousOperationalStabilityRegression.actualOpeningIsRelationFree
#print axioms Tests.EndogenousOperationalStabilityRegression.actualDiscoveryOutcomeIsAuthoritative
#print axioms Tests.EndogenousOperationalStabilityRegression.actualDiscoveredTransportChangesSameOpeningWidth
#print axioms Tests.EndogenousOperationalStabilityRegression.actualRetainedTargetIsExact
#print axioms Tests.EndogenousOperationalStabilityRegression.actualLeftActionUsesDiscovery
#print axioms Tests.EndogenousOperationalStabilityRegression.actualRightActionIsRetained
#print axioms Tests.EndogenousOperationalStabilityRegression.actualLeftActionPreservesCriterion
#print axioms Tests.EndogenousOperationalStabilityRegression.fullReductionIsEstablishedConstitutiveStep
#print axioms Tests.EndogenousOperationalStabilityRegression.acceptedLeftPayloadUsesDiscovery
#print axioms Tests.EndogenousOperationalStabilityRegression.absorbedSiblingRemainsViableAndDistinct
#print axioms Tests.EndogenousOperationalStabilityRegression.retainedSiblingRemainsViable
#print axioms Tests.EndogenousOperationalStabilityRegression.executedApplicationUsesReturnedRelation
#print axioms Tests.EndogenousOperationalStabilityRegression.executedOutputFeedsNextState
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralCarrierCompleteZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicStructuralCarrierNoDuplicatesZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicPendingCarrierCompleteZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicPendingCarrierNoDuplicatesZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicOperationalCarrierCompleteZero
#print axioms Tests.EndogenousOperationalStabilityRegression.publicOperationalCarrierNoDuplicatesZero
#print axioms Tests.EndogenousOperationalStabilityRegression.actualStageTraceComesFromFrontiers
#print axioms Tests.EndogenousOperationalStabilityRegression.actualStageTraceIsFrontierProjection
#print axioms Tests.EndogenousOperationalStabilityRegression.executedSystemHasNonFactorizingTotalActions
#print axioms Tests.EndogenousOperationalStabilityRegression.comparisonMatchesActualExecutedObservation
#print axioms Tests.EndogenousOperationalStabilityRegression.projectedObservedActionIsExecuted
#print axioms Tests.EndogenousOperationalStabilityRegression.projectedTraceIsExecuted
#print axioms Tests.EndogenousOperationalStabilityRegression.executedViewIsDiscoveredProjection
#print axioms Tests.EndogenousOperationalStabilityRegression.executedProjectedViewsAreEqual
#print axioms Tests.EndogenousOperationalStabilityRegression.productionExecutedNonFactorizationHasAbstractType
#print axioms Tests.EndogenousOperationalStabilityRegression.executedTotalActionDoesNotFactorThroughProjectedView
#print axioms Tests.EndogenousOperationalStabilityRegression.wrongSingletonStillRejected
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorSameExecutedOutput
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorProjectedViewsEqual
#print axioms Tests.EndogenousOperationalStabilityRegression.separatorDifferentTotalAction
#print axioms Tests.EndogenousOperationalStabilityRegression.stateWidthViewCannotRecoverTotalAction
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.projection
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.action
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.sameProjection
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.differentAction
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.collision
#print axioms Tests.EndogenousOperationalStabilityRegression.ProjectionCollisionRegression.actionDoesNotFactorThroughPropositionallyEqualProjection
/- AXIOM_AUDIT_END -/
