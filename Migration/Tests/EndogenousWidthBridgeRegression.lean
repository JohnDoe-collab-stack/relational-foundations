import RelationalPerimeter

/-! Client checks of the existing-endogeneity to exact-width bridge. -/
namespace EndogenousWidthBridgeRegression
open ConstitutiveSearch
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Extensive

/-- One theorem, for every input, with no open operational assumptions. -/
theorem fullBridge (input : Nat) : EndogenousDecompositionAndWidth input :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenous_production_and_width_separation input

/-- The feedback property refers to the same history that defines the carrier. -/
theorem existingEndogeneity (input : Nat) :
    ExecutedFeedback.Along (publicCausalOperationalExecution input) :=
  (fullBridge input).feedbackAtEveryStep

example (input : Nat) :
    (publicCertificateNormalization input).imageDescription.Source =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

example (input : Nat) :
    (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier (index := input) ()).Identity =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

/-- No source profile is refuted to justify its grouping. -/
theorem allSourcesViable (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)) :
    ∃ payload : RoleProfilePayload p, RoleSemantics.ProfileAccept p payload :=
  (fullBridge input).allProfilesRemainViable p

/-- All source indices retain their executed trace to their carried value. -/
theorem allSourcesHaveTheirTrace (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)) :
    Nonempty (ExecutedRoleProfileReduction
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction p
      ((publicCertificateExecutedRegime input).carry p).value) :=
  (fullBridge input).sourceIndexedTrace p

/-- Final regime width and transient local frontier width remain distinct. -/
theorem widthReadings (input : Nat) :
    (publicRoleProfileFiniteCarrier input).frontier.length = 2 ^ (input + 1) ∧
    (publicCertificateExecutedRegime input).frontier.length = 1 ∧
    WidthTraceAtMost 2 (ExecutedFeedback.widthTrace (publicCausalOperationalExecution input)) :=
  ⟨(fullBridge input).extensiveWidth, (fullBridge input).executedWidth,
    (fullBridge input).transientWidth⟩

/-- The binary-class theorem is not restricted to the constructed SAT member. -/
theorem arbitraryBinaryMember
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔ Function.Injective regime.carry :=
  binaryClass_fullWidthExactlyInjective family problem regime

/-- The executed witness, not an independent singleton, refutes necessity. -/
theorem fullWidthNotForced (input : Nat) :
    ¬ (∀ regime : ObligationRegime (publicRoleProfileFiniteCarrier input),
      regime.frontier.length = 2 ^ (input + 1)) :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.extensive_multiplicity_does_not_force_full_operational_width input

end EndogenousWidthBridgeRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms EndogenousWidthBridgeRegression.fullBridge
#print axioms EndogenousWidthBridgeRegression.existingEndogeneity
#print axioms EndogenousWidthBridgeRegression.allSourcesViable
#print axioms EndogenousWidthBridgeRegression.allSourcesHaveTheirTrace
#print axioms EndogenousWidthBridgeRegression.widthReadings
#print axioms EndogenousWidthBridgeRegression.arbitraryBinaryMember
#print axioms EndogenousWidthBridgeRegression.fullWidthNotForced
/- AXIOM_AUDIT_END -/
