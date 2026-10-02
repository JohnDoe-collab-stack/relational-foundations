import RelationalPerimeter

/-! Client checks of the exact realization, before and after admission. -/
namespace ConstitutiveContinuityRegression
open ConstitutiveSearch ConstitutiveSearch.Extensive
open ConstitutiveSearch.EndogenousDecomposition

set_option maxHeartbeats 800000

/-- Both return laws hold for every policy, including pending and mixed roles. -/
theorem occurrence_roundTrips
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles)
    (q : RolewiseObligation history.policy) (p : history.ProducedOccurrence) :
    history.producedOccurrenceTransport.backward
        (history.producedOccurrenceTransport.forward q) = q ∧
      history.producedOccurrenceTransport.forward
        (history.producedOccurrenceTransport.backward p) = p :=
  ⟨history.producedOccurrenceTransport.forwardBackward q,
    history.producedOccurrenceTransport.backwardForward p⟩

/-- Equality of realized occurrences reflects equality of policy obligations. -/
theorem occurrence_reflects_obligations
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles)
    (left right : RolewiseObligation history.policy)
    (same : history.realize left = history.realize right) : left = right :=
  history.realize_injective same

/-- The lower local producer supplies its status before any continuation. -/
theorem local_status_from_head
    {source : CausalConstitutiveState}
    (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer context stage).operationalStatus =
      (executedStageDecomposition stage).operationalStatus :=
  prefixLocalOperationalProducer_status_exact context stage

/-- The public output policy is the projection of stored head output images. -/
theorem public_output_projection (input : Nat) :
    publicExecutedOutputPolicy input =
      ExecutedOutput.ofStagewise
        (publicCausalOperationalExecution input).stagewiseDecomposition := rfl

theorem actual_output_roundTrips
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (q : RolewiseObligation (ExecutedOutput.policy reduction)) :
    ExecutedOutput.reify reduction (ExecutedOutput.value reduction q)
      (ExecutedOutput.value_isProduced reduction q) = q :=
  ExecutedOutput.reify_value reduction q

/-- A comparative readout of the same formed occurrences, not another execution. -/
def distinguishingOutput
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (o : RoleConstitutedOccurrence role) : Bool :=
  match o.position with
  | .left => false
  | .right => true

theorem nonconvergent_image_keeps_distinctions
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ProducedOutputImage.carry (roleOpeningFiniteCarrier role) (distinguishingOutput role)
        (roleConstitutedOccurrenceAt role .left) ≠
      ProducedOutputImage.carry (roleOpeningFiniteCarrier role) (distinguishingOutput role)
        (roleConstitutedOccurrenceAt role .right) := by
  intro same
  have impossible : (false : Bool) = true := congrArg Subtype.val same
  cases impossible

theorem no_convergence_from_image_type
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ¬ (∀ p q, distinguishingOutput role p = distinguishingOutput role q) := by
  intro converges
  have impossible : (false : Bool) = true :=
    converges (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right)
  cases impossible

/-- A comparison on the same constituted sources. No convergent licence is
passed to this regime: duplicate removal compares the produced Boolean values. -/
def distinguishingRegime
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ObligationRegime (roleOpeningFiniteCarrier role) :=
  ProducedOutputImage.imageRegime (roleOpeningFiniteCarrier role) (distinguishingOutput role)
    (ProducedOutputImage.targetEquality _ _ inferInstance)

theorem distinguishingOutput_injective
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    Function.Injective (distinguishingOutput role) := by
  intro left right same
  have positionExact : left.position = right.position := by
    cases lp : left.position <;> cases rp : right.position
    · rfl
    · have impossible : (false : Bool) = true := by
        simpa only [distinguishingOutput, lp, rp] using same
      cases impossible
    · have impossible : (true : Bool) = false := by
        simpa only [distinguishingOutput, lp, rp] using same
      cases impossible
    · rfl
  exact Eq.trans (roleConstitutedOccurrence_roundTrip left).symm
    (Eq.trans (congrArg (roleConstitutedOccurrenceAt role) positionExact)
      (roleConstitutedOccurrence_roundTrip right))

/-- The actual image construction keeps both obligations when both outputs
are distinct. This excludes a singleton imposed by the image grammar itself. -/
theorem distinguishingRegime_width_two
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (distinguishingRegime role).frontier.length = 2 := by
  have preserves : Function.Injective (distinguishingRegime role).carry := by
    intro left right same
    exact distinguishingOutput_injective role (congrArg Subtype.val same)
  exact full_width_of_preserves (distinguishingRegime role) preserves

/-- The closed scientific certificate includes chronology and output origin,
not merely the terminal value of the recursion. -/
theorem certified_production_order (input : Nat) :
    (publicCausalOperationalExecutionWithTrace input).2 =
      operationalProductionTimeline (resolutionLength input) input :=
  (exactCausalExponentialTarget input).execution.primitiveOperationOrder

/-- This policy reads the stored output images, not a presence-only marker. -/
theorem public_width_from_actual_outputs (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length =
      (rolewiseObligationFrontier (publicExecutedOutputPolicy input)).length :=
  publicRegimeWidth_eq_producedOutputs input

/-- The status history remains a separate projected readout. -/
theorem public_status_projection (input : Nat) :
    publicOperationalStatuses input =
      RoleStatus.ofStagewise
        (publicCausalOperationalExecution input).stagewiseDecomposition := rfl

theorem public_policy_roundTrip (input : Nat)
    (q : RolewiseObligation
      (ExecutedOutput.policy
        (publicCausalOperationalExecution input).stagewiseDecomposition.reduction)) :
    (publicProducedObligationTransport input).backward
      ((publicProducedObligationTransport input).forward q) = q :=
  (publicProducedObligationTransport input).forwardBackward q

theorem public_admitted_roundTrip (input : Nat)
    (q : AuthorizedProducedTargetObligation (publicCertificateNormalization input)) :
    (publicProducedObligationTransport input).forward
      ((publicProducedObligationTransport input).backward q) = q :=
  (publicProducedObligationTransport input).backwardForward q

theorem public_carry_commutes (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)) :
    (publicProducedObligationTransport input).forward
      (rolewiseCarry
        (ExecutedOutput.policy
          (publicCausalOperationalExecution input).stagewiseDecomposition.reduction) p) =
      (publicCertificateExecutedRegime input).carry p :=
  publicProducedObligationTransport_carry input p

/-- Target agreement is a theorem, not a numeric singleton comparison. -/
theorem public_carry_target (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)) :
    ((publicCertificateExecutedRegime input).carry p).value =
      (publicCertificateNormalization input).target p :=
  publicCertificate_carry_value_eq_produced_target input p

/-- Equality with a separate status readout; this is not the width derivation. -/
theorem public_width_from_recorded_productions (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length =
      (rolewiseObligationFrontier (publicOperationalStatuses input).policy).length :=
  publicRegimeWidth_eq_producedStatuses input

theorem arbitrary_payload_action (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input))
    (payload : RoleProfilePayload p) :
    (publicCarriedProfilePayload input p payload).1 =
      RoleSemantics.actProfile
        (publicCausalOperationalExecution input).stagewiseDecomposition.reduction p payload :=
  publicCarriedProfilePayload_action input p payload

theorem arbitrary_payload_preservation (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input))
    (payload : RoleProfilePayload p) (accepted : RoleSemantics.ProfileAccept p payload) :
    RoleSemantics.TargetAccept
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction
      (publicCarriedProfilePayload input p payload).1 :=
  publicCarriedProfilePayload_preserves input p payload accepted

/-- Source distinctions survive the exact obligation realization. -/
theorem distinct_sources_grouped (input : Nat) :
    publicCertificateTransformedProfile input ≠ publicCertificateRetainedProfile input ∧
      (publicCertificateExecutedRegime input).carry (publicCertificateTransformedProfile input) =
        (publicCertificateExecutedRegime input).carry (publicCertificateRetainedProfile input) :=
  ⟨publicCertificateProfiles_distinct input, publicCertificateProfiles_carryTogether input⟩

end ConstitutiveContinuityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveContinuityRegression.public_output_projection
#print axioms ConstitutiveContinuityRegression.actual_output_roundTrips
#print axioms ConstitutiveContinuityRegression.distinguishingOutput
#print axioms ConstitutiveContinuityRegression.nonconvergent_image_keeps_distinctions
#print axioms ConstitutiveContinuityRegression.no_convergence_from_image_type
#print axioms ConstitutiveContinuityRegression.distinguishingRegime
#print axioms ConstitutiveContinuityRegression.distinguishingOutput_injective
#print axioms ConstitutiveContinuityRegression.distinguishingRegime_width_two
#print axioms ConstitutiveContinuityRegression.certified_production_order
#print axioms ConstitutiveContinuityRegression.public_width_from_actual_outputs
#print axioms ConstitutiveContinuityRegression.occurrence_roundTrips
#print axioms ConstitutiveContinuityRegression.occurrence_reflects_obligations
#print axioms ConstitutiveContinuityRegression.local_status_from_head
#print axioms ConstitutiveContinuityRegression.public_status_projection
#print axioms ConstitutiveContinuityRegression.public_policy_roundTrip
#print axioms ConstitutiveContinuityRegression.public_admitted_roundTrip
#print axioms ConstitutiveContinuityRegression.public_carry_commutes
#print axioms ConstitutiveContinuityRegression.public_carry_target
#print axioms ConstitutiveContinuityRegression.public_width_from_recorded_productions
#print axioms ConstitutiveContinuityRegression.arbitrary_payload_action
#print axioms ConstitutiveContinuityRegression.arbitrary_payload_preservation
#print axioms ConstitutiveContinuityRegression.distinct_sources_grouped
/- AXIOM_AUDIT_END -/
