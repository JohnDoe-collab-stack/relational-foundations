import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.TrajectoryDerivedClosureCore
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyResources

/-!
# Closure data for the closed explicit SAT family

The generic reconstruction from proof-relevant trajectories lives in
`TrajectoryDerivedClosureCore`. This facade specializes it to the explicit
family and keeps the established public names.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Generator variables extracted from the actual resource-aligned F(n) trajectory. -/
def explicitFamilyTrajectoryDecisionVars
    (count : Nat) :
    List Var :=
  (explicitFamilyResourceTrajectory count).trajectory.decisionVars

/-- Split-frontier states extracted from the actual F(n) trajectory. -/
def explicitFamilyTrajectoryClosureCandidates
    (count : Nat) :
    List
      (GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count)) :=
  (explicitFamilyResourceTrajectory count).trajectory.splitCandidates

/-- Closure fuel extracted from the actual F(n) trajectory. -/
def explicitFamilyTrajectoryClosureFuel
    (count : Nat) :
    Nat :=
  (explicitFamilyResourceTrajectory count).trajectory.closureFuel

/-- The extracted generator list has exactly n entries. -/
theorem explicitFamilyTrajectoryDecisionVars_length
    (count : Nat) :
    (explicitFamilyTrajectoryDecisionVars count).length = count :=
  (explicitFamilyResourceTrajectory count).trajectory.decisionVars_length

/-- The extracted split-state candidate list has exactly 2n entries. -/
theorem explicitFamilyTrajectoryClosureCandidates_length
    (count : Nat) :
    (explicitFamilyTrajectoryClosureCandidates count).length = 2 * count :=
  (explicitFamilyResourceTrajectory count).trajectory.splitCandidates_length

/-- The extracted closure fuel is exactly n. -/
theorem explicitFamilyTrajectoryClosureFuel_eq
    (count : Nat) :
    explicitFamilyTrajectoryClosureFuel count = count :=
  (explicitFamilyResourceTrajectory count).trajectory.closureFuel_eq_length

/--
The fully derived bounded closure search for the closed F(n) trajectory.

Its primitive variables, candidate states and fuel are all reconstructed from
the same proof-relevant trajectory.
-/
def explicitFamilyTrajectoryDerivedClosureSearch
    (count : Nat) :
    RelationSearch
      (TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula := explicitStackedSymmetricFamily count)
          (explicitFamilyTrajectoryDecisionVars count))) :=
  (explicitFamilyResourceTrajectory count).trajectory.derivedClosureSearch

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryDecisionVars
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryClosureCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryClosureFuel
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryDecisionVars_length
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryClosureCandidates_length
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryClosureFuel_eq
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryDerivedClosureSearch
/- AXIOM_AUDIT_END -/
