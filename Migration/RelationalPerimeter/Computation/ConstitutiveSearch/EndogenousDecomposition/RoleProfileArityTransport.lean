import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles

/-!
# Exact arity readout of role-constituted profiles

Arity is extracted only after the realized openings and their occurrence
profiles have been constituted.  The numerical profile is connected to the
occurrence profile by an explicit constructive `RelationalFoundations.ExactTransport`; it is not
used to define the roles, occurrences, or profiles upstream.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

/-- Numerical arities read from the realized openings of the role history. -/
def roleHistoryArities :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      RelationalConstitutiveRoleHistory run → List Nat
  | _, _, _, .nil => []
  | _, _, _, .step _ tailRoles => 2 :: roleHistoryArities tailRoles

/-- Product carrier associated with an already extracted arity list. -/
def ArityProfile : List Nat → Type
  | [] => Unit
  | arity :: tail => Fin arity × ArityProfile tail

/-- Read one role position as its numerical position in the binary opening. -/
def openingRolePositionToFinTwo
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} :
    OpeningRolePosition role → Fin 2
  | .left => ⟨0, by decide⟩
  | .right => ⟨1, by decide⟩

/-- Recover one binary role position from its exact numerical readout. -/
def finTwoToOpeningRolePosition
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    Fin 2 → OpeningRolePosition role
  | ⟨0, _⟩ => .left
  | ⟨_ + 1, _⟩ => .right

theorem openingRolePosition_finTwo_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    finTwoToOpeningRolePosition role
        (openingRolePositionToFinTwo position) = position := by
  cases position <;> rfl

theorem finTwo_openingRolePosition_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (index : Fin 2) :
    openingRolePositionToFinTwo
        (finTwoToOpeningRolePosition role index) = index := by
  cases index with
  | mk value before =>
      cases value with
      | zero => rfl
      | succ value =>
          cases value with
          | zero => rfl
          | succ value =>
              have impossible : value < 0 :=
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ before)
              exact False.elim (Nat.not_lt_zero value impossible)

/-- Exact local transport from binary role positions to `Fin 2`. -/
def openingRolePositionFinTwoTransport
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    RelationalFoundations.ExactTransport (OpeningRolePosition role) (Fin 2) :=
  { forward := openingRolePositionToFinTwo
    backward := finTwoToOpeningRolePosition role
    forwardBackward := openingRolePosition_finTwo_roundTrip role
    backwardForward := finTwo_openingRolePosition_roundTrip role }

/-- Read a role-position profile into the extracted arity product. -/
def rolePositionProfileToArityProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RolePositionProfile roles → ArityProfile (roleHistoryArities roles)
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile =>
      (openingRolePositionToFinTwo profile.1,
        rolePositionProfileToArityProfile tailRoles profile.2)

/-- Reconstruct the role-position profile from the exact arity readout. -/
def arityProfileToRolePositionProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      ArityProfile (roleHistoryArities roles) → RolePositionProfile roles
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile =>
      (finTwoToOpeningRolePosition headRole profile.1,
        arityProfileToRolePositionProfile tailRoles profile.2)

theorem rolePositionProfile_arity_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RolePositionProfile roles) →
      arityProfileToRolePositionProfile roles
          (rolePositionProfileToArityProfile roles profile) = profile
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      exact Prod.ext
        (openingRolePosition_finTwo_roundTrip headRole profile.1)
        (rolePositionProfile_arity_roundTrip tailRoles profile.2)

theorem arityProfile_rolePositionProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : ArityProfile (roleHistoryArities roles)) →
      rolePositionProfileToArityProfile roles
          (arityProfileToRolePositionProfile roles profile) = profile
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      exact Prod.ext
        (finTwo_openingRolePosition_roundTrip headRole profile.1)
        (arityProfile_rolePositionProfile_roundTrip tailRoles profile.2)

/-- Exact transport from position profiles to the numerical arity readout. -/
def rolePositionArityTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    RelationalFoundations.ExactTransport
      (RolePositionProfile roles)
      (ArityProfile (roleHistoryArities roles)) :=
  { forward := rolePositionProfileToArityProfile roles
    backward := arityProfileToRolePositionProfile roles
    forwardBackward := rolePositionProfile_arity_roundTrip roles
    backwardForward := arityProfile_rolePositionProfile_roundTrip roles }

/-- Exact transport from realized occurrence profiles to the arity readout. -/
def roleOccurrenceArityTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    RelationalFoundations.ExactTransport
      (RoleOccurrenceProfile roles)
      (ArityProfile (roleHistoryArities roles)) :=
  RelationalFoundations.ExactTransport.compose
    (RelationalFoundations.ExactTransport.reverse (roleProfileTransport roles))
    (rolePositionArityTransport roles)

/-- The extracted arity list contains one entry for every role. -/
theorem roleHistoryArities_length :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (roleHistoryArities roles).length = count
  | _, _, _, .nil => rfl
  | _, _, _, .step _ tailRoles =>
      congrArg Nat.succ (roleHistoryArities_length tailRoles)

/-- The product of extracted local arities is the profile width. -/
theorem roleProfileWidth_eq_arityProduct :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      roleProfileWidth roles = (roleHistoryArities roles).prod
  | _, _, _, .nil => rfl
  | _, _, _, .step headRole tailRoles => by
      rw [roleProfileWidth_step,
        roleProfileWidth_eq_arityProduct tailRoles]
      exact (Nat.mul_comm _ 2)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleHistoryArities
#print axioms ConstitutiveSearch.EndogenousDecomposition.ArityProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingRolePositionFinTwoTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolePositionProfileToArityProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.arityProfileToRolePositionProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolePositionArityTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleOccurrenceArityTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleHistoryArities_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_eq_arityProduct
/- AXIOM_AUDIT_END -/
