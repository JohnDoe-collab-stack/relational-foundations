import RelationalPerimeter

namespace ConstitutiveObjectiveRegression
open ConstitutiveSearch
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Extensive

/-- The strengthened public certificate is inhabited at every depth. -/
example (input : Nat) : ExactCausalExponentialTarget input :=
  exactCausalExponentialTarget input

/-- The semantic description does not introduce a new source carrier. -/
example (input : Nat) :
    (publicCertificateNormalization input).imageDescription.Source =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

example (input : Nat) :
    (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier (index := input) ()).Identity =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

theorem universalPreservation
    (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input))
    (payload : RoleProfilePayload p) (accepted : RoleSemantics.ProfileAccept p payload) :
    RoleSemantics.TargetAccept
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction
      (publicCarriedProfilePayload input p payload).1 :=
  publicCarriedProfilePayload_preserves input p payload accepted

theorem preservationAndReflection (input : Nat) :
    (∃ p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input),
      ∃ payload : RoleProfilePayload p, RoleSemantics.ProfileAccept p payload) ↔
    (∃ target : ExecutedOperationalTargetProfile
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction,
      RoleSemantics.TargetAccept
        (publicCausalOperationalExecution input).stagewiseDecomposition.reduction target) :=
  (publicCertificateNormalization input).viable_iff

theorem distinctProfilesGrouped (input : Nat) :
    publicCertificateTransformedProfile input ≠ publicCertificateRetainedProfile input ∧
    (publicCertificateExecutedRegime input).carry (publicCertificateTransformedProfile input) =
      (publicCertificateExecutedRegime input).carry (publicCertificateRetainedProfile input) :=
  ⟨publicCertificateProfiles_distinct input, publicCertificateProfiles_carryTogether input⟩

theorem exactWidths (input : Nat) :
    (publicRoleProfileFiniteCarrier input).frontier.length = 2 ^ (input + 1) ∧
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  ⟨publicRoleProfileFiniteCarrier_width input, publicCertificate_executedRegime_width input⟩

theorem fullWidthExactlyInjective (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔ Function.Injective regime.carry :=
  publicCertificate_exponential_iff_carry_injective input regime

theorem horizonDoesNotChooseHead
    (left right : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory (left + 1) state context fresh).head? =
      (executeCausalOperationalExecutionHistory (right + 1) state context fresh).head? :=
  executeCausalOperationalExecutionHistory_head_independent left right state context fresh

end ConstitutiveObjectiveRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveObjectiveRegression.universalPreservation
#print axioms ConstitutiveObjectiveRegression.preservationAndReflection
#print axioms ConstitutiveObjectiveRegression.distinctProfilesGrouped
#print axioms ConstitutiveObjectiveRegression.exactWidths
#print axioms ConstitutiveObjectiveRegression.fullWidthExactlyInjective
#print axioms ConstitutiveObjectiveRegression.horizonDoesNotChooseHead
/- AXIOM_AUDIT_END -/
