import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileFiniteCarrier

/-!
# Obligation regimes over role-constituted extensive profiles

The source identities in this module are the occurrence profiles already
constituted from a dependent history of relational roles.  A regime is strictly
downstream: it may preserve or merge those identities, but it neither creates
them nor changes their formation history.

The central equivalence is stated for every causal role history and every
surjective obligation regime over its source carrier.  Exponential width is a
property of the regime frontier; preservation as distinct and separately
addressable identities is a property of its carry map and its factorized
addressing.  Neither side is a field or definition of the other.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive
open RelationalExtensive

/-- The finite source carrier derived only from an authoritative role history. -/
def roleProfileFiniteCarrier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : FiniteCarrier :=
  relationalProfileFiniteCarrier (generalHistoryOfRoleHistory roles)

theorem roleProfileFiniteCarrier_width
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    (roleProfileFiniteCarrier roles).frontier.length = 2 ^ count :=
  roleProfileWidth_eq_two_pow_count roles

/--
The regime conserves already constituted source identities as distinct and
separately addressable obligations.  The address is required to factor through
`regime.carry`; it is not a direct address assigned behind the regime's back.
-/
structure ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
    {source : FiniteCarrier}
    (regime : ObligationRegime source) : Prop where
  preservesDistinctIdentities : PreservesIdentitiesSeparately regime
  separatelyAddressableThroughRegime :
    Nonempty (RegimeSeparateAddressingAt regime source.frontier.length)

/-- Separate preservation constructively supplies the factorized addressing. -/
theorem roleIdentityConservationOfPreserves
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (preserves : PreservesIdentitiesSeparately regime) :
    ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  { preservesDistinctIdentities := preserves
    separatelyAddressableThroughRegime :=
      ⟨(exactRegimeCapacityOfPreserves regime preserves).attained⟩ }

/-- The combined conservation condition has exactly the injective content. -/
theorem preservesIdentitiesSeparately_iff_roleIdentityConservation
    {source : FiniteCarrier}
    (regime : ObligationRegime source) :
    PreservesIdentitiesSeparately regime ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  ⟨roleIdentityConservationOfPreserves regime,
    fun conservation => conservation.preservesDistinctIdentities⟩

/--
Independent quantitative predicate: the regime itself carries one obligation
for every member of the exponential role-profile frontier.
-/
def HasRoleConstitutedExponentialWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) : Prop :=
  regime.frontier.length = 2 ^ count

/--
Target equivalence for the general class of binary causal role histories:
exponential obligation width appears exactly when the regime conserves the
role-constituted alternatives as distinct and separately addressable
identities.
-/
theorem roleConstituted_exponentialWidth_iff_distinctSeparateConservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) :
    HasRoleConstitutedExponentialWidth roles regime ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime := by
  constructor
  · intro exponentialWidth
    have fullWidth : regime.HasFullExtensiveWidth := by
      unfold ObligationRegime.HasFullExtensiveWidth
      exact Eq.trans exponentialWidth
        (roleProfileFiniteCarrier_width roles).symm
    exact roleIdentityConservationOfPreserves regime
      (preserves_of_full_width regime fullWidth)
  · intro conservation
    have fullWidth : regime.HasFullExtensiveWidth :=
      full_width_of_preserves regime
        conservation.preservesDistinctIdentities
    unfold HasRoleConstitutedExponentialWidth
    unfold ObligationRegime.HasFullExtensiveWidth at fullWidth
    exact Eq.trans fullWidth (roleProfileFiniteCarrier_width roles)

/-- The immutable target in its literal form: full binary width is equivalent
to injectivity of the regime's own carry map on the constituted profiles. -/
theorem roleConstituted_exponentialWidth_iff_carry_injective
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) :
    regime.frontier.length = 2 ^ count ↔
      Function.Injective regime.carry := by
  exact Iff.trans
    (roleConstituted_exponentialWidth_iff_distinctSeparateConservation
      roles regime)
    (preservesIdentitiesSeparately_iff_roleIdentityConservation regime).symm

/-- The same target stated through exact minimum factorized capacity. -/
theorem roleConstituted_exponentialWidth_iff_exactRegimeCapacity
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) :
    HasRoleConstitutedExponentialWidth roles regime ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (roleProfileFiniteCarrier roles).frontier.length) := by
  exact Iff.trans
    (roleConstituted_exponentialWidth_iff_distinctSeparateConservation
      roles regime)
    (Iff.trans
      (preservesIdentitiesSeparately_iff_roleIdentityConservation regime).symm
      (preservesIdentitiesSeparately_iff_exactRegimeCapacity regime))

/-- Every positive-length role history produces a genuinely non-singleton source. -/
theorem positiveRoleHistory_has_nontrivial_extensive_width
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory (count + 1) state}
    (roles : RelationalConstitutiveRoleHistory run) :
    1 < (roleProfileFiniteCarrier roles).frontier.length := by
  exact Eq.mpr
    (congrArg (fun width => 1 < width)
      (roleProfileFiniteCarrier_width roles))
    (Constructive.two_pow_strictly_grows (Nat.zero_lt_succ count))

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFiniteCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFiniteCarrier_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleIdentityConservationOfPreserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.preservesIdentitiesSeparately_iff_roleIdentityConservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.HasRoleConstitutedExponentialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstituted_exponentialWidth_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstituted_exponentialWidth_iff_carry_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstituted_exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.positiveRoleHistory_has_nontrivial_extensive_width
/- AXIOM_AUDIT_END -/
