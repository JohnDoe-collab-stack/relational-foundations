import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyEqualityCosts

/-!
# Concrete representation-charged cost model for F(n)

This module instantiates AtomicCosts with explicit binary representation charges.

The model is concrete:
* syntax unit: one bit;
* frontier slot: formula budget plus full-history budget;
* provenance unit: one encoded decision node;
* certificate atom: one tag plus the selected variable representation;
* relation query: the four-operand equality charge proved for structural flip;
* closure candidate: one encoded state envelope;
* terminal check: one encoded history envelope.

It is still a representation-charge model, not a theorem about wall-clock time
of Lean's runtime.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Uniform encoded state envelope for the explicit family. -/
def explicitFamilyStateBinaryBudget
    (count : Nat) : Nat :=
  explicitFamilyBinaryBudget count +
    StructuralDecisionHistory.binaryBudget
      count
      count

/-- Encoded envelope for one constituted decision/provenance unit. -/
def explicitFamilyProvenanceUnitBinaryBudget
    (count : Nat) : Nat :=
  StructuralDecisionHistory.binaryBudget
    count
    1

/-- Encoded charge of one local flip-certificate atom and its variable. -/
def explicitFamilyCertificateAtomBinaryBudget
    (count : Nat) : Nat :=
  Nat.succ
    (BinaryRepresentation.natBitSize count)

/--
Concrete representation charges assigned to the certified event profile of
F(n).
-/
def explicitFamilyRepresentationAtomicCosts
    (count : Nat) : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot :=
      explicitFamilyStateBinaryBudget count
    provenanceUnit :=
      explicitFamilyProvenanceUnitBinaryBudget count
    certificateAtom :=
      explicitFamilyCertificateAtomBinaryBudget count
    relationFindCall :=
      explicitFamilyRelationEqualityChargeBudget count
    closurePrimitiveQuery :=
      explicitFamilyRelationEqualityChargeBudget count
    closureCompositionCandidate :=
      explicitFamilyStateBinaryBudget count
    terminalCheck :=
      StructuralDecisionHistory.binaryBudget
        count
        count }

/-- Aggregate representation charge of the announced F(n) execution. -/
def explicitFamilyRepresentationChargedCost
    (count : Nat) : Nat :=
  explicitFamilyChargedCost
    count
    (explicitFamilyRepresentationAtomicCosts count)

/-- Relation calls are charged by the proved four-operand binary equality budget. -/
theorem explicitFamily_relationFind_atomicCost
    (count : Nat) :
    (explicitFamilyRepresentationAtomicCosts count).relationFindCall =
      explicitFamilyRelationEqualityChargeBudget count := by
  rfl

/-- Closure primitive queries use the same equality charge when later enabled. -/
theorem explicitFamily_closurePrimitive_atomicCost
    (count : Nat) :
    (explicitFamilyRepresentationAtomicCosts count).closurePrimitiveQuery =
      explicitFamilyRelationEqualityChargeBudget count := by
  rfl

/--
The local F(n) strategy pays zero closure-search charge because its certified
event profile contains no closure search.
-/
theorem explicitFamily_localStrategy_noClosureCharge
    (count : Nat) :
    (explicitFamilyComplexityCounts count).closurePrimitiveQueries *
          (explicitFamilyRepresentationAtomicCosts count).closurePrimitiveQuery +
        (explicitFamilyComplexityCounts count).closureCompositionCandidates *
          (explicitFamilyRepresentationAtomicCosts count).closureCompositionCandidate =
      0 := by
  change
    0 * explicitFamilyRelationEqualityChargeBudget count +
        0 * explicitFamilyStateBinaryBudget count =
      0
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]

/--
Closed aggregate representation budget for the announced local strategy on F(n).

This expression charges exactly the event classes that occur in the certified
profile.  Closure-search terms are absent because both closure counters are
proved to be zero for this strategy.
-/
def explicitFamilyRepresentationBudget
    (count : Nat) : Nat :=
  4 * count +
    ((3 * count + 1) *
        explicitFamilyStateBinaryBudget count +
      (count *
          explicitFamilyProvenanceUnitBinaryBudget count +
        (count *
            explicitFamilyCertificateAtomBinaryBudget count +
          ((2 * count) *
              explicitFamilyRelationEqualityChargeBudget count +
            StructuralDecisionHistory.binaryBudget
              count
              count))))

/--
The representation-charged execution cost is exactly the closed budget above.

Unlike the earlier conditional uniform envelope, this theorem has no external
atomic-cost hypothesis: every charged atomic cost is instantiated by the
concrete binary representation model.
-/
theorem explicitFamilyRepresentationChargedCost_eq_budget
    (count : Nat) :
    explicitFamilyRepresentationChargedCost count =
      explicitFamilyRepresentationBudget count := by
  change
    (4 * count) * 1 +
        ((3 * count + 1) *
            explicitFamilyStateBinaryBudget count +
          (count *
              explicitFamilyProvenanceUnitBinaryBudget count +
            (count *
                explicitFamilyCertificateAtomBinaryBudget count +
              ((2 * count) *
                  explicitFamilyRelationEqualityChargeBudget count +
                (0 *
                    explicitFamilyRelationEqualityChargeBudget count +
                  (0 *
                      explicitFamilyStateBinaryBudget count +
                    1 *
                      StructuralDecisionHistory.binaryBudget
                        count
                        count)))))) =
      4 * count +
        ((3 * count + 1) *
            explicitFamilyStateBinaryBudget count +
          (count *
              explicitFamilyProvenanceUnitBinaryBudget count +
            (count *
                explicitFamilyCertificateAtomBinaryBudget count +
              ((2 * count) *
                  explicitFamilyRelationEqualityChargeBudget count +
                StructuralDecisionHistory.binaryBudget
                  count
                  count))))
  rw [Nat.mul_one]
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]
  rw [Nat.one_mul]
  rw [Nat.zero_add]
  rw [Nat.zero_add]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyStateBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenanceUnitBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateAtomBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationAtomicCosts
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationChargedCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_relationFind_atomicCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_closurePrimitive_atomicCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_localStrategy_noClosureCharge
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationChargedCost_eq_budget
/- AXIOM_AUDIT_END -/
