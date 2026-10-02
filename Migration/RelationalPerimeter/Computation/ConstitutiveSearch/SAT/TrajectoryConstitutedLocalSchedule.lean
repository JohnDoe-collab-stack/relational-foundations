import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.TrajectoryConstitutedLocalScheduleCore
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyTransportCosts
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Explicit-family instance and quantitative bounds for the local schedule

The generic constituted schedule is defined and proved correct in
`TrajectoryConstitutedLocalScheduleCore`. This facade keeps the explicit-family
specialization, the comparison with certificate syntax, and the later
input-polynomial bounds.
-/

namespace ConstitutiveSearch
namespace SAT

namespace FlipSymmetricTrajectory

/--
The endogenous production count agrees with the transport-certificate atom
count. Both read the same proof-relevant trajectory.
-/
theorem constitutedLocalAtomCount_eq_transportCertificateAtomCount
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory : FlipSymmetricTrajectory start finish length) :
    ConstitutedLocalSchedule.atomCount trajectory.constitutedLocalWitnesses =
      trajectory.transportCertificateAtomCount := by
  rw [
    trajectory.constitutedLocalAtomCount_eq_length,
    trajectory.transportCertificateAtomCount_eq_index
  ]

end FlipSymmetricTrajectory

/-- Canonical constituted local schedule for the closed explicit SAT family. -/
def explicitFamilyConstitutedLocalWitnesses
    (count : Nat) :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalWitnesses

/-- F(n) produces exactly n local constituted witnesses. -/
theorem explicitFamilyConstitutedLocalWitnesses_length
    (count : Nat) :
    (explicitFamilyConstitutedLocalWitnesses count).length = count :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalWitnesses_length

/-- F(n) schedule variables are exactly the trajectory provenance. -/
theorem explicitFamilyConstitutedLocalWitnesses_vars
    (count : Nat) :
    (explicitFamilyConstitutedLocalWitnesses count).map (fun entry => entry.var) =
      (explicitFamilyResourceTrajectory count).trajectory.decisionVars :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalWitnesses_vars

/-- F(n) produces exactly n primitive transport atoms. -/
theorem explicitFamilyConstitutedLocalAtomCount
    (count : Nat) :
    ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses count) = count :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalAtomCount_eq_length

/-- F(n) validates its complete local schedule in exactly n queries. -/
theorem explicitFamilyConstitutedLocalValidationQueries
    (count : Nat) :
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses count) = count :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalValidationQueries_eq_length

/-- F(n) actual local execution performs exactly n primitive queries. -/
theorem explicitFamilyConstitutedLocalExecutionQueries
    (count : Nat) :
    ConstitutedLocalSchedule.executionPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses count) = count :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalExecutionQueries_eq_length

/-- F(n) actual local execution inspects no composition candidates. -/
theorem explicitFamilyConstitutedLocalExecutionCompositionCandidates
    (count : Nat) :
    ConstitutedLocalSchedule.executionCompositionCandidates
        (explicitFamilyConstitutedLocalWitnesses count) = 0 :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalExecutionCompositionCandidates_eq_zero

/-- Every locally constituted F(n) code validates successfully. -/
theorem explicitFamilyConstitutedLocalValidationSucceeds
    (count : Nat) :
    ConstitutedLocalSchedule.ValidationSucceeds
      (explicitFamilyConstitutedLocalWitnesses count) :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalValidationSucceeds

/-- Every locally constituted F(n) code admits candidate-free execution. -/
theorem explicitFamilyConstitutedLocalHasLocalExecutions
    (count : Nat) :
    ConstitutedLocalSchedule.HasLocalExecutions
      (explicitFamilyConstitutedLocalWitnesses count) :=
  (explicitFamilyResourceTrajectory count).trajectory.constitutedLocalHasLocalExecutions

/-- Production atom count of the endogenous F(n) schedule is input-polynomial. -/
theorem explicitFamilyConstitutedLocalAtomCount_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.atomCount
          (explicitFamilyConstitutedLocalWitnesses count)) := by
  refine ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses count) ≤
      explicitFamilyInputBitSize count
  rw [explicitFamilyConstitutedLocalAtomCount]
  exact explicitFamilyIndex_le_inputBitSize count

/-- Actual local execution primitive-query count of F(n) is input-polynomial. -/
theorem explicitFamilyConstitutedLocalExecution_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.executionPrimitiveQueries
          (explicitFamilyConstitutedLocalWitnesses count)) := by
  refine ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.executionPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses count) ≤
      explicitFamilyInputBitSize count
  rw [explicitFamilyConstitutedLocalExecutionQueries]
  exact explicitFamilyIndex_le_inputBitSize count

/-- Actual local execution composition-candidate count is constantly zero. -/
theorem explicitFamilyConstitutedLocalExecutionComposition_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.executionCompositionCandidates
          (explicitFamilyConstitutedLocalWitnesses count)) := by
  refine ⟨CostPolynomial.constant 0, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.executionCompositionCandidates
        (explicitFamilyConstitutedLocalWitnesses count) ≤ 0
  rw [explicitFamilyConstitutedLocalExecutionCompositionCandidates]
  exact Nat.le_refl 0

/-- Validation query count of the endogenous F(n) schedule is input-polynomial. -/
theorem explicitFamilyConstitutedLocalValidation_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.validationPrimitiveQueries
          (explicitFamilyConstitutedLocalWitnesses count)) := by
  refine ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses count) ≤
      explicitFamilyInputBitSize count
  rw [explicitFamilyConstitutedLocalValidationQueries]
  exact explicitFamilyIndex_le_inputBitSize count

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalAtomCount_eq_transportCertificateAtomCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalWitnesses
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalWitnesses_length
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalWitnesses_vars
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalAtomCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidationQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalExecutionQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalExecutionCompositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidationSucceeds
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalHasLocalExecutions
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalAtomCount_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalExecution_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalExecutionComposition_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidation_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
