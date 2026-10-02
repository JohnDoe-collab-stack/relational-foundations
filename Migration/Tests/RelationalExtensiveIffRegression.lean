import RelationalPerimeter

/-!
# Regression gate for the constitutive extensive separation

The checks protect one dependency direction:

primitive relations -> executed stages -> constituted roles -> source profiles ->
executed reduction -> produced targets and traces -> proved convergence ->
obligation regime -> width.

No obligation carrier or operational width may be installed independently of the
executed convergent-target regime.
-/

namespace RelationalPerimeter.Tests.RelationalExtensiveIffRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.Extensive
open ConstitutiveSearch.RelationalExtensive
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

set_option maxHeartbeats 800000

/-- The target iff holds for every member of the general binary class. -/
theorem classLevelTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  binary_family_exponential_width_iff_distinct_separate_conservation
    family problem regime

/-- The general class also exposes the immutable literal `iff`. -/
theorem classLevelLiteralTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Function.Injective regime.carry :=
  binary_family_exponential_width_iff_carry_injective family problem regime

/-- Factorized separate capacity is equivalent to the same full-width side. -/
theorem classLevelCapacityTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  binary_family_exponential_width_iff_exact_separate_capacity
    family problem regime

theorem independentBinaryMemberIsUnbounded (bound : Nat) :
    bound ≤ abstractBinaryRelationalFamily.stageCount
      (abstractBinaryRelationalFamily.unboundedProblem bound) :=
  abstractBinaryRelationalFamily_unbounded bound

theorem generalClassIsNotOnlyBinary :
    (relationallyConstitutedOccurrenceFrontier
      (increasingArityStage 1)).length = 3 :=
  increasingArityRelationalFamily_variable 1

theorem publicBinaryMemberHasExactSourceWidth (input : Nat) :
    (publicBinaryExtensiveFamily.sourceCarrier
        (index := input) ()).frontier.length = 2 ^ (input + 1) :=
  publicBinaryExtensiveFamily.sourceWidth_eq_twoPow ()

/-- Every identity in the general-class carrier is constituted by its
formation and provenance relations. -/
theorem publicGeneralCarrierIsRelationallyConstituted (input : Nat) :
    (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
      (index := input) ()).Identity =
      RelationalOccurrenceProfile
        (publicGeneralRelationalHistory input) :=
  rfl

/-- The general opening uses the authoritative exact position-occurrence
transport, rather than a second occurrence carrier. -/
theorem publicOpeningTransportIsAuthoritative
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (generalOpeningStageOfRole role).positionOccurrenceTransport =
      openingPositionOccurrenceTransport role :=
  generalOpeningStage_positionOccurrenceTransport_exact role

/-- The concrete profile transport is the history-level general transport. -/
theorem publicProfileTransportIsGeneralTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    roleProfileTransport roles =
      relationalProfileTransport (generalHistoryOfRoleHistory roles) :=
  rfl

/-- The class carrier and the executed carrier are definitionally identical. -/
theorem publicClassCarrierIsExecutedCarrier (input : Nat) :
    publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) () =
      publicRoleProfileFiniteCarrier input :=
  rfl

/-- The public iff is stated on the carrier constituted by the executed roles. -/
theorem publicTarget
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  constituted_exponential_width_iff_distinct_separate_conservation
    input regime

/-- The target's literal `iff` is exposed without a surrogate predicate. -/
theorem publicLiteralTarget
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry :=
  constituted_exponential_width_iff_carry_injective input regime

theorem publicSeparateRegimeHasExponentialWidth (input : Nat) :
    (constitutedDistinctSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  constituted_distinct_separate_regime_has_exponential_width input

theorem publicSeparateRegimeConserves (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (constitutedDistinctSeparateRegime input) :=
  constituted_distinct_separate_regime_conserves input

/-- One stage constructs its decomposition without receiving a future tail. -/
def stageDecompositionIsPrefixLocal
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    ExecutedStageDecomposition stage :=
  executedStageDecomposition stage

theorem publicCertificateUsesCanonicalStagewiseDecomposition (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        (causalOperationalExecution input).causalRun :=
  causal_operational_decomposition_is_prefix_local input

/-- The richer execution erases exactly to the established authoritative run. -/
theorem publicFusedExecutionErasesExactly (input : Nat) :
    (causalOperationalExecution input).instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory :=
  causal_operational_execution_erases_to_authoritative input

/-- The causal run produced by the fused recursion is the run of the
authoritative public realization, not a second reconstructed history. -/
theorem publicFusedCausalRunIsAuthoritative (input : Nat) :
    (publicCausalOperationalExecution input).causalRun =
      (publicInstrumentedExecutionRealization input).causalRun :=
  publicCausalOperationalExecution_causalRun_exact input

/-- The relational roles consumed downstream are exactly those constituted
from the authoritative public run. -/
theorem publicFusedRolesAreAuthoritative (input : Nat) :
    (publicCausalOperationalExecution input).stagewiseDecomposition.roles =
      publicRelationalConstitutiveRoles input :=
  publicCausalOperationalExecution_roles_exact input

/-- The immutable target is inhabited by a closed production object. -/
def publicExactTargetIsClosed (input : Nat) :
    _root_.RelationalPerimeter.Computation.EndogenousOperationalDecomposition.ExactCausalExponentialTarget
      input :=
  exactCausalExponentialTargetEvidence input

/-- The public normalizer is the execution of that exact reduction history. -/
theorem publicNormalizationIsCanonical (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).normalization =
      executedCausalNormalization
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  (constitutiveExtensiveSeparationEvidence input).normalizationExact

/-- The regime is pinned to actual targets and their executed convergence. -/
theorem publicOperationalRegimeIsComputedImage (input : Nat) :
    (publicCertificateNormalization input).operationalRegime =
      (publicCertificateNormalization input).authorizedOperationalRegime
        (publicCertificateNormalization input).groupingAuthorization :=
  (publicCertificateNormalization input).operationalRegime_exact

/-- The public regime is only a projection of its exact executed realization. -/
theorem publicOperationalRegimeIsExactRealization (input : Nat) :
    executedConstitutiveObligationRegime input =
      (publicCertificateNormalization input).operationalRegime :=
  executed_constitutive_regime_is_exact_realization input

/-- Production code supplies a positive pair of distinct constituted profiles. -/
theorem publicExecutedProfilesRemainDistinct (input : Nat) :
    executedTransformedSourceProfile input ≠
      executedRetainedSourceProfile input :=
  executed_source_profiles_are_distinct input

/-- The two distinct profiles carry two traces to one produced target. -/
def publicExecutedProfilesAreCoDetermined (input : Nat) :
    OperationallyCoDetermined (publicCertificateNormalization input)
      (executedTransformedSourceProfile input)
      (executedRetainedSourceProfile input) :=
  executed_source_profiles_are_codetermined input

/-- Their shared obligation is obtained without identifying the profiles. -/
theorem publicExecutedDistinctProfilesCarryTogether (input : Nat) :
    (executedConstitutiveObligationRegime input).carry
        (executedTransformedSourceProfile input) =
      (executedConstitutiveObligationRegime input).carry
        (executedRetainedSourceProfile input) :=
  executed_distinct_profiles_carry_together input

/-- Each source profile carries the dependent trace producing its target. -/
def publicExecutedTargetHasExactTrace
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ExecutedRoleProfileReduction
      (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction
      profile
      (executedConstitutiveTarget input profile) :=
  executedConstitutiveTargetTrace input profile

theorem publicExecutedTargetIsExact
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    executedConstitutiveTarget input profile =
      retainedExecutedOperationalTargetProfile
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  executed_constitutive_target_exact input profile

/-- The target frontier is computed before its numerical width is read. -/
theorem publicExecutedProducedTargetFrontierIsExact (input : Nat) :
    (publicCertificateNormalization input).producedTargetFrontier =
      [retainedExecutedOperationalTargetProfile
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction] :=
  executed_produced_target_frontier_exact input

theorem publicExecutedWidthComesFromProducedTargetImage (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
      (publicCertificateNormalization input).producedTargetFrontier.length :=
  executed_causal_regime_width_eq_produced_target_width input

/-- Regime equality has exactly the fibres produced by execution. -/
theorem publicExecutedCarryFibresAreProducedTargetFibres
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    (executedConstitutiveObligationRegime input).carry left =
        (executedConstitutiveObligationRegime input).carry right ↔
      executedConstitutiveTarget input left =
        executedConstitutiveTarget input right :=
  executed_carry_eq_iff_produced_target_eq input left right

/-- The carried obligation contains the target produced for this source. -/
theorem publicExecutedCarryValueIsProducedTarget
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ((executedConstitutiveObligationRegime input).carry profile).1 =
      executedConstitutiveTarget input profile :=
  executed_carry_value_eq_produced_target input profile

/-- Fibre equality is constituted by the two executed traces themselves. -/
theorem publicExecutedCarryFibresAreOperationalCodetermination
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    (executedConstitutiveObligationRegime input).carry left =
        (executedConstitutiveObligationRegime input).carry right ↔
      Nonempty
        (OperationallyCoDetermined (publicCertificateNormalization input)
          left right) :=
  executed_carry_eq_iff_operational_codetermination input left right

theorem publicExecutedRegimeUsesSameConstitutedCarrier (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
        2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
        (executedConstitutiveObligationRegime input) :=
  executed_regime_exponential_width_iff_separate_preservation input

/-- Width one is the terminal readout of executed target convergence. -/
theorem publicExecutedWidthIsOne (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length = 1 :=
  executed_constitutive_obligation_width_is_one input

/-- The executed grouping changes obligation status without identifying sources. -/
theorem publicExecutedReductionRejectsSeparateObligationStatus
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (executedConstitutiveObligationRegime input) :=
  executed_reduction_does_not_preserve_separate_obligations input

/-- The compiled action materially transforms the executed source. -/
theorem compiledActionIsMaterial
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage run) :
    ((compileRoleStageAtom role).action run.sourceContinuation).1 ≠
      run.sourceContinuation.1 :=
  compiledRoleStage_action_changes_executed_source run role

theorem transformedOccurrenceUsesDiscoveredAction
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) :
    interpretRoleStageAtom (compileRoleStageAtom role)
        (roleConstitutedOccurrenceAt role .left)
        (roleConstitutionEvidence role
          (roleConstitutedOccurrenceAt role .left)) continuation =
      role.reconstructedRelation.mapContinuation continuation :=
  interpretCompiledRoleStage_left role continuation

/-- The transformed operational target is literally the executed action output;
convergence is proved only afterwards. -/
theorem transformedTargetIsExecutedAction
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    let license := executedRoleReductionLicense role
    let absorption := criterionPreservingAbsorption license
    transformedExecutedRoleOperationalTarget absorption =
      interpretRoleStageAtom (compileRoleStageAtom role)
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput) :=
  transformedExecutedRoleOperationalTarget_is_executed_action _

/-- Preservation for arbitrary continuations remains a separate witness. -/
theorem reductionCarriesArbitraryContinuationPreservation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh))
    (accepted : GeneratedStructuralBranchAccept
      (causalOpeningLeft source run.selected run.fresh) continuation) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      ((compileRoleStageAtom role).action continuation) :=
  let license := executedRoleReductionLicense role
  let absorption := criterionPreservingAbsorption license
  criterionPreservingAbsorption_preservesCriterion absorption
    continuation accepted

theorem reductionKeepsOccurrencesDistinct
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (executedRoleReductionLicense role).transformedOccurrence ≠
      (executedRoleReductionLicense role).retainedOccurrence :=
  (executedRoleReductionLicense role).occurrencesRemainDistinct

/-- Regression gate for the formerly bypassable transformed decision: its
target is definitionally the output of the executed relation. -/
theorem transformedDecisionTargetIsExecutedAction
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    let license := executedRoleReductionLicense role
    (executedTransformedRoleOccurrenceDecision license).target =
      interpretRoleStageAtom (compileRoleStageAtom role)
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput) :=
  rfl

/-- The executed-action output is an index of the transformed decision type,
not a label attached after the decision has been constructed. -/
def transformedDecisionHasExecutedActionIndex
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    let license := executedRoleReductionLicense role
    ExecutedRoleOccurrenceDecision license license.transformedOccurrence
      (interpretRoleStageAtom (compileRoleStageAtom role)
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput)) :=
  executedTransformedRoleOccurrenceDecision (executedRoleReductionLicense role)

/-- The only accepted producer has the exact stage-only function type. -/
def exactPrefixLocalProducerType : PrefixLocalOperationalProducer :=
  prefixLocalOperationalProducer

/-- The canonical head production carries exactly the already-produced context
that was available before its dependent tail is constructed. -/
theorem prefixLocalProductionCarriesExactPriorContext
    {source : CausalConstitutiveState}
    (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer context stage).priorContext = context :=
  (prefixLocalOperationalProducer context stage).priorContextExact

/-- The public normalizer is definitionally built by consuming the complete
role-by-role constitutive chain. -/
theorem publicNormalizationConsumesConstitutiveChain (input : Nat) :
    (publicCertificateNormalization input).constitutiveChain =
      executedReductionConstitutiveChain
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  rfl

/-- The normalized pair is a definitional elimination of that chain.  There is
no stored result field in which a prescribed target can be installed and
justified by transporting the trace afterwards. -/
theorem normalizationResultIsChainElimination
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (source : RoleOccurrenceProfile roles) :
    normalization.result source =
      normalizeExecutedRoleProfileFromChain
        normalization.constitutiveChain source :=
  rfl

/-- The consumed chain still exposes the action, preservation, acceptance and
source-distinction witness at every dependent role. -/
def publicNormalizationChainIsCausallyExact (input : Nat) :
    ExecutedReductionCausalExact
      (publicCertificateNormalization input).constitutiveChain :=
  (publicCertificateNormalization input).constitutiveChainExact

/-- Grouping is authorized by the preservation chain extracted from the same
executed constitutive chain that produces the normalized targets. -/
def publicGroupingRetainsPreservation (input : Nat) :
    ExecutedReductionPreservationExact
      (publicCertificateNormalization input).constitutiveChain :=
  (publicCertificateExactExecutedRegime input).groupingAuthorization.preservation

/-- Grouping is simultaneously authorized by persistent separation of the
source occurrences; grouping therefore does not identify them. -/
def publicGroupingRetainsOccurrenceSeparation (input : Nat) :
    ExecutedReductionOccurrenceSeparationExact
      (publicCertificateNormalization input).constitutiveChain :=
  (publicCertificateExactExecutedRegime input).groupingAuthorization
    |>.occurrenceSeparation

/-- The exact target closes both authorization dependencies explicitly. -/
def publicExactTargetGroupingAuthorization (input : Nat) :
    ExecutedOperationalGroupingAuthorization
      (publicCertificateNormalization input) :=
  (publicCertificateExactExecutedRegime input).groupingAuthorization

/-- The class-level exponential `iff` is available on the literal carrier of
the authoritative executed roles, with no adapter carrier in its statement. -/
theorem publicClassIffUsesAuthoritativeExecutedCarrier
    (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry :=
  (exactCausalExponentialTargetEvidence input)
    |>.width.exponentialIffCarryInjective regime

/-- The public regime is definitionally the exact regime projected from the
same normalization; an unrelated singleton cannot replace it. -/
theorem publicRegimeIsExactNormalizationProjection (input : Nat) :
    executedConstitutiveObligationRegime input =
      (publicCertificateNormalization input).operationalRegime :=
  rfl

end RelationalPerimeter.Tests.RelationalExtensiveIffRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.classLevelTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.classLevelLiteralTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.classLevelCapacityTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.independentBinaryMemberIsUnbounded
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.generalClassIsNotOnlyBinary
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicBinaryMemberHasExactSourceWidth
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicGeneralCarrierIsRelationallyConstituted
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicOpeningTransportIsAuthoritative
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicProfileTransportIsGeneralTransport
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicClassCarrierIsExecutedCarrier
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicLiteralTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicSeparateRegimeHasExponentialWidth
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicSeparateRegimeConserves
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.stageDecompositionIsPrefixLocal
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicCertificateUsesCanonicalStagewiseDecomposition
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicFusedExecutionErasesExactly
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicFusedCausalRunIsAuthoritative
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicFusedRolesAreAuthoritative
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExactTargetIsClosed
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicNormalizationIsCanonical
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicOperationalRegimeIsComputedImage
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicOperationalRegimeIsExactRealization
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedProfilesRemainDistinct
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedProfilesAreCoDetermined
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedDistinctProfilesCarryTogether
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedTargetHasExactTrace
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedTargetIsExact
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedProducedTargetFrontierIsExact
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedWidthComesFromProducedTargetImage
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryFibresAreProducedTargetFibres
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryValueIsProducedTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryFibresAreOperationalCodetermination
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedRegimeUsesSameConstitutedCarrier
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedWidthIsOne
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedReductionRejectsSeparateObligationStatus
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.compiledActionIsMaterial
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedOccurrenceUsesDiscoveredAction
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedTargetIsExecutedAction
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionCarriesArbitraryContinuationPreservation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionKeepsOccurrencesDistinct
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedDecisionTargetIsExecutedAction
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedDecisionHasExecutedActionIndex
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.exactPrefixLocalProducerType
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.prefixLocalProductionCarriesExactPriorContext
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicNormalizationConsumesConstitutiveChain
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.normalizationResultIsChainElimination
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicNormalizationChainIsCausallyExact
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicGroupingRetainsPreservation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicGroupingRetainsOccurrenceSeparation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExactTargetGroupingAuthorization
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicClassIffUsesAuthoritativeExecutedCarrier
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicRegimeIsExactNormalizationProjection
/- AXIOM_AUDIT_END -/
