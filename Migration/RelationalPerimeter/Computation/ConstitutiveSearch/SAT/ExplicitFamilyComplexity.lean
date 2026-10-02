import RelationalPerimeter.Computation.ConstitutiveSearch.ComplexityInterface
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyNormalizationCosts
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyTransportCosts

/-!
# Conditional complexity profile for the explicit SAT family

This module instantiates the generic complexity interface with event counts that
have already been certified for the closed family F(n).

The resulting charged cost is still conditional on declared atomic costs.
No bit-model or machine-runtime bound is smuggled into the event counts.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Certified source-level event profile for the announced local-flip strategy. -/
def explicitFamilyComplexityCounts
    (count : Nat) : ComplexityCounts :=
  { syntaxUnits := 4 * count
    frontierSlots := 3 * count + 1
    provenanceUnits := count
    certificateAtoms := count
    relationFindCalls := 2 * count
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 1 }

/--
Evidence connecting every charged count to the previously formalized execution
objects.  Closure-search counters are zero because this particular family uses
the direct sibling-flip search, not composition search.
-/
structure ExplicitFamilyComplexityEvidence
    (count : Nat) : Prop where
  syntaxExact :
    Cnf.literalCount
        (explicitStackedSymmetricFamily count) =
      (explicitFamilyComplexityCounts count).syntaxUnits
  frontierExact :
    FlipSymmetricTrajectory.frontierSlotCount
        (explicitFamilyResourceTrajectory count).trajectory =
      (explicitFamilyComplexityCounts count).frontierSlots
  provenanceExact :
    (explicitFamilyResourceTrajectory count).finish.provenanceSize =
      (explicitFamilyComplexityCounts count).provenanceUnits
  certificateExact :
    FlipSymmetricTrajectory.transportCertificateAtomCount
        (explicitFamilyResourceTrajectory count).trajectory =
      (explicitFamilyComplexityCounts count).certificateAtoms
  relationFindExact :
    FlipSymmetricTrajectory.normalizationFindCallCount
        (explicitFamilyResourceTrajectory count).trajectory =
      (explicitFamilyComplexityCounts count).relationFindCalls
  closurePrimitiveZero :
    (explicitFamilyComplexityCounts count).closurePrimitiveQueries = 0
  closureCandidatesZero :
    (explicitFamilyComplexityCounts count).closureCompositionCandidates = 0
  terminalChargedOnce :
    (explicitFamilyComplexityCounts count).terminalChecks = 1
  endpointTerminal :
    ResourceTerminal
      (explicitFamilyResourceTrajectory count).finish
      []

/-- Complete evidence package for every member F(n). -/
theorem explicitFamilyComplexityEvidence
    (count : Nat) :
    ExplicitFamilyComplexityEvidence count := by
  constructor
  · change
      Cnf.literalCount
          (stackedSymmetricBlocks count count) =
        4 * count
    exact
      stackedSymmetricBlocks_literalCount
        count
        count
  · change
      FlipSymmetricTrajectory.frontierSlotCount
          (explicitFamilyResourceTrajectory count).trajectory =
        3 * count + 1
    exact
      FlipSymmetricTrajectory.frontierSlotCount_eq
        (explicitFamilyResourceTrajectory count).trajectory
  · change
      (explicitFamilyResourceTrajectory count).finish.provenanceSize =
        count
    exact
      explicitFamilyEndpoint_provenanceSize count
  · change
      FlipSymmetricTrajectory.transportCertificateAtomCount
          (explicitFamilyResourceTrajectory count).trajectory =
        count
    exact
      explicitFamilyTransportCertificateAtomCount count
  · change
      FlipSymmetricTrajectory.normalizationFindCallCount
          (explicitFamilyResourceTrajectory count).trajectory =
        2 * count
    exact
      explicitFamilyNormalizationFindCallCount count
  · rfl
  · rfl
  · rfl
  · exact
      explicitFamilyEndpoint_terminal count

/-- Charged conditional cost for the explicit family under a declared cost model. -/
def explicitFamilyChargedCost
    (count : Nat)
    (costs : AtomicCosts) : Nat :=
  chargedCost
    (explicitFamilyComplexityCounts count)
    costs

/-- Uniform structural envelope for F(n) under one common atomic-cost bound. -/
def explicitFamilyUniformChargedBudget
    (count unitBound : Nat) : Nat :=
  uniformChargedBudget
    (explicitFamilyComplexityCounts count)
    unitBound

/-- Conditional aggregate-cost theorem for the closed family. -/
theorem explicitFamilyChargedCost_le_uniform
    (count : Nat)
    (costs : AtomicCosts)
    (unitBound : Nat)
    (bounded :
      UniformAtomicBound costs unitBound) :
    explicitFamilyChargedCost count costs ≤
      explicitFamilyUniformChargedBudget
        count
        unitBound :=
  chargedCost_le_of_uniformBound
    (explicitFamilyComplexityCounts count)
    costs
    unitBound
    bounded

/--
If every atomic operation has an explicitly proved cost at most n+1, the family
inherits the corresponding expanded structural envelope.

This theorem is conditional on that atomic-cost hypothesis; it does not prove
the hypothesis.
-/
theorem explicitFamilyChargedCost_le_linearAtomicEnvelope
    (count : Nat)
    (costs : AtomicCosts)
    (bounded :
      UniformAtomicBound
        costs
        (count + 1)) :
    explicitFamilyChargedCost count costs ≤
      explicitFamilyUniformChargedBudget
        count
        (count + 1) :=
  explicitFamilyChargedCost_le_uniform
    count
    costs
    (count + 1)
    bounded

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyComplexityCounts
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyComplexityEvidence
#print axioms ConstitutiveSearch.SAT.explicitFamilyComplexityEvidence
#print axioms ConstitutiveSearch.SAT.explicitFamilyChargedCost
#print axioms ConstitutiveSearch.SAT.explicitFamilyUniformChargedBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyChargedCost_le_uniform
#print axioms ConstitutiveSearch.SAT.explicitFamilyChargedCost_le_linearAtomicEnvelope
/- AXIOM_AUDIT_END -/
