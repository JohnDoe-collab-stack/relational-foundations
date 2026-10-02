import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyBitComplexity

/-!
# Polynomial representation-cost envelope for the explicit SAT family

The representation-charged model is already concrete.  This module removes the
remaining recursive presentation of its principal budgets.

It proves closed polynomial forms for:
* clause/history prefix-tag budgets;
* the stacked CNF budget;
* the complete state and relation-equality budgets.

The only inequality is the certificate-atom charge: the concrete binary digit
count is bounded coarsely by n+1, hence one tagged certificate atom by n+2.

The final theorem bounds the exact representation-charged cost by an explicit
polynomial expression in n.  This remains a representation-cost theorem, not a
wall-clock theorem for Lean's runtime or DecidableEq implementation.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Clause

/-- Closed form of the prefix-tag clause budget. -/
theorem binaryBudget_closed
    (maximum count : Nat) :
    binaryBudget maximum count =
      count * (maximum + 3) + 1 := by
  induction count with
  | zero =>
      change
        1 =
          0 * (maximum + 3) + 1
      rw [Nat.zero_mul]
  | succ count inductionHypothesis =>
      change
        Nat.succ
            ((maximum + 2) +
              binaryBudget maximum count) =
          Nat.succ count * (maximum + 3) + 1
      rw [
        inductionHypothesis,
        Nat.succ_mul count (maximum + 3)
      ]
      calc
        Nat.succ
            ((maximum + 2) +
              (count * (maximum + 3) + 1))
            =
          Nat.succ (maximum + 2) +
            (count * (maximum + 3) + 1) :=
              (Nat.succ_add
                (maximum + 2)
                (count * (maximum + 3) + 1)).symm
        _ =
          (maximum + 3) +
            (count * (maximum + 3) + 1) := by
              rfl
        _ =
          ((maximum + 3) +
            count * (maximum + 3)) + 1 :=
              (Nat.add_assoc
                (maximum + 3)
                (count * (maximum + 3))
                1).symm
        _ =
          (count * (maximum + 3) +
            (maximum + 3)) + 1 :=
              congrArg
                (fun value => value + 1)
                (Nat.add_comm
                  (maximum + 3)
                  (count * (maximum + 3)))

end Clause

namespace StructuralDecisionHistory

/-- Closed form of the prefix-tag decision-history budget. -/
theorem binaryBudget_closed
    (maximum count : Nat) :
    binaryBudget maximum count =
      count * (maximum + 3) + 1 := by
  induction count with
  | zero =>
      change
        1 =
          0 * (maximum + 3) + 1
      rw [Nat.zero_mul]
  | succ count inductionHypothesis =>
      change
        Nat.succ
            ((maximum + 2) +
              binaryBudget maximum count) =
          Nat.succ count * (maximum + 3) + 1
      rw [
        inductionHypothesis,
        Nat.succ_mul count (maximum + 3)
      ]
      calc
        Nat.succ
            ((maximum + 2) +
              (count * (maximum + 3) + 1))
            =
          Nat.succ (maximum + 2) +
            (count * (maximum + 3) + 1) :=
              (Nat.succ_add
                (maximum + 2)
                (count * (maximum + 3) + 1)).symm
        _ =
          (maximum + 3) +
            (count * (maximum + 3) + 1) := by
              rfl
        _ =
          ((maximum + 3) +
            count * (maximum + 3)) + 1 :=
              (Nat.add_assoc
                (maximum + 3)
                (count * (maximum + 3))
                1).symm
        _ =
          (count * (maximum + 3) +
            (maximum + 3)) + 1 :=
              congrArg
                (fun value => value + 1)
                (Nat.add_comm
                  (maximum + 3)
                  (count * (maximum + 3)))

end StructuralDecisionHistory

/-- Pure additive identity for one stacked serialization level. -/
theorem doubleBlockStep
    (block previous : Nat) :
    Nat.succ
        (block +
          Nat.succ
            (block + (previous + 1))) =
      previous +
          (block + block + 1 + 1) +
        1 := by
  have pair :
      (block + 1) + (block + 1) =
        block + block + 1 + 1 := by
    calc
      (block + 1) + (block + 1)
          =
        block + (1 + (block + 1)) :=
          Nat.add_assoc
            block
            1
            (block + 1)
      _ =
        block + ((1 + block) + 1) :=
          congrArg
            (Nat.add block)
            (Nat.add_assoc 1 block 1).symm
      _ =
        block + ((block + 1) + 1) :=
          congrArg
            (fun value =>
              block + (value + 1))
            (Nat.add_comm 1 block)
      _ =
        block + (block + (1 + 1)) :=
          congrArg
            (Nat.add block)
            (Nat.add_assoc block 1 1)
      _ =
        (block + block) + (1 + 1) :=
          (Nat.add_assoc
            block
            block
            (1 + 1)).symm
      _ =
        block + block + 1 + 1 :=
          (Nat.add_assoc
            (block + block)
            1
            1).symm
  calc
    Nat.succ
        (block +
          Nat.succ
            (block + (previous + 1)))
        =
      Nat.succ block +
        Nat.succ
          (block + (previous + 1)) :=
        (Nat.succ_add
          block
          (Nat.succ
            (block + (previous + 1)))).symm
    _ =
      Nat.succ block +
        (Nat.succ block + (previous + 1)) :=
        congrArg
          (Nat.add (Nat.succ block))
          (Nat.succ_add
            block
            (previous + 1)).symm
    _ =
      (block + 1) +
        ((block + 1) + (previous + 1)) := by
        rfl
    _ =
      ((block + 1) + (block + 1)) +
        (previous + 1) :=
        (Nat.add_assoc
          (block + 1)
          (block + 1)
          (previous + 1)).symm
    _ =
      (block + block + 1 + 1) +
        (previous + 1) :=
        congrArg
          (fun value =>
            value + (previous + 1))
          pair
    _ =
      ((block + block + 1 + 1) +
        previous) + 1 :=
        (Nat.add_assoc
          (block + block + 1 + 1)
          previous
          1).symm
    _ =
      (previous +
        (block + block + 1 + 1)) + 1 :=
        congrArg
          (fun value => value + 1)
          (Nat.add_comm
            (block + block + 1 + 1)
            previous)

/-- Closed form of the stacked CNF serialization budget. -/
theorem stackedSymmetricBinaryBudget_closed
    (anchor count : Nat) :
    stackedSymmetricBinaryBudget anchor count =
      count *
          ((2 * (anchor + 3) + 1) +
            (2 * (anchor + 3) + 1) +
            1 + 1) +
        1 := by
  induction count with
  | zero =>
      change
        1 =
          0 *
              ((2 * (anchor + 3) + 1) +
                (2 * (anchor + 3) + 1) +
                1 + 1) +
            1
      rw [Nat.zero_mul]
  | succ count inductionHypothesis =>
      change
        Nat.succ
            (Clause.binaryBudget anchor 2 +
              Nat.succ
                (Clause.binaryBudget anchor 2 +
                  stackedSymmetricBinaryBudget
                    anchor
                    count)) =
          Nat.succ count *
              ((2 * (anchor + 3) + 1) +
                (2 * (anchor + 3) + 1) +
                1 + 1) +
            1
      rw [
        Clause.binaryBudget_closed anchor 2,
        inductionHypothesis,
        Nat.succ_mul
          count
          ((2 * (anchor + 3) + 1) +
            (2 * (anchor + 3) + 1) +
            1 + 1)
      ]
      exact
        doubleBlockStep
          (2 * (anchor + 3) + 1)
          (count *
            ((2 * (anchor + 3) + 1) +
              (2 * (anchor + 3) + 1) +
              1 + 1))

/-- Polynomial formula-size envelope used below. -/
def explicitFamilyFormulaPolynomialBudget
    (count : Nat) : Nat :=
  count *
      ((2 * (count + 3) + 1) +
        (2 * (count + 3) + 1) +
        1 + 1) +
    1

/-- Polynomial history-size envelope used below. -/
def explicitFamilyHistoryPolynomialBudget
    (count : Nat) : Nat :=
  count * (count + 3) + 1

/-- Polynomial state-size envelope used below. -/
def explicitFamilyStatePolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyFormulaPolynomialBudget count +
    explicitFamilyHistoryPolynomialBudget count

/-- Polynomial provenance-unit envelope used below. -/
def explicitFamilyProvenancePolynomialBudget
    (count : Nat) : Nat :=
  1 * (count + 3) + 1

/-- Polynomial certificate-atom envelope used below. -/
def explicitFamilyCertificatePolynomialBudget
    (count : Nat) : Nat :=
  Nat.succ (count + 1)

/-- Polynomial equality-charge envelope for one relation-search call. -/
def explicitFamilyRelationPolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyFormulaPolynomialBudget count +
    explicitFamilyFormulaPolynomialBudget count +
      (explicitFamilyHistoryPolynomialBudget count +
        explicitFamilyHistoryPolynomialBudget count)

/-- The recursive closed-family CNF budget is exactly polynomial. -/
theorem explicitFamilyBinaryBudget_eq_polynomial
    (count : Nat) :
    explicitFamilyBinaryBudget count =
      explicitFamilyFormulaPolynomialBudget count := by
  exact
    stackedSymmetricBinaryBudget_closed
      count
      count

/-- The full endpoint-history budget is exactly polynomial. -/
theorem explicitFamilyHistoryBinaryBudget_eq_polynomial
    (count : Nat) :
    StructuralDecisionHistory.binaryBudget
        count
        count =
      explicitFamilyHistoryPolynomialBudget count := by
  exact
    StructuralDecisionHistory.binaryBudget_closed
      count
      count

/-- The encoded state envelope is exactly the stated polynomial budget. -/
theorem explicitFamilyStateBinaryBudget_eq_polynomial
    (count : Nat) :
    explicitFamilyStateBinaryBudget count =
      explicitFamilyStatePolynomialBudget count := by
  unfold explicitFamilyStateBinaryBudget
  unfold explicitFamilyStatePolynomialBudget
  rw [
    explicitFamilyBinaryBudget_eq_polynomial,
    explicitFamilyHistoryBinaryBudget_eq_polynomial
  ]

/-- One provenance unit has exact budget n+4. -/
theorem explicitFamilyProvenanceUnitBinaryBudget_eq_polynomial
    (count : Nat) :
    explicitFamilyProvenanceUnitBinaryBudget count =
      explicitFamilyProvenancePolynomialBudget count := by
  unfold explicitFamilyProvenanceUnitBinaryBudget
  unfold explicitFamilyProvenancePolynomialBudget
  exact
    StructuralDecisionHistory.binaryBudget_closed
      count
      1

/-- One tagged certificate atom costs at most n+2 bits in the coarse model. -/
theorem explicitFamilyCertificateAtomBinaryBudget_le_polynomial
    (count : Nat) :
    explicitFamilyCertificateAtomBinaryBudget count ≤
      explicitFamilyCertificatePolynomialBudget count := by
  unfold explicitFamilyCertificateAtomBinaryBudget
  unfold explicitFamilyCertificatePolynomialBudget
  have bitBound :
      BinaryRepresentation.natBitSize count ≤
        count + 1 :=
    BinaryRepresentation.natBitSize_le_succ count
  exact
    Nat.succ_le_succ bitBound

/-- The four-operand relation equality charge is exactly polynomial. -/
theorem explicitFamilyRelationEqualityChargeBudget_eq_polynomial
    (count : Nat) :
    explicitFamilyRelationEqualityChargeBudget count =
      explicitFamilyRelationPolynomialBudget count := by
  unfold explicitFamilyRelationEqualityChargeBudget
  unfold uniformGeneratedFlipEqualityCharge
  unfold explicitFamilyRelationPolynomialBudget
  rw [
    explicitFamilyBinaryBudget_eq_polynomial,
    explicitFamilyHistoryBinaryBudget_eq_polynomial
  ]

/--
Explicit polynomial envelope for the complete representation-charged execution.
The expression is intentionally left factored so every contribution remains
traceable to its certified event class.
-/
def explicitFamilyRepresentationPolynomialBudget
    (count : Nat) : Nat :=
  4 * count +
    ((3 * count + 1) *
        explicitFamilyStatePolynomialBudget count +
      (count *
          explicitFamilyProvenancePolynomialBudget count +
        (count *
            explicitFamilyCertificatePolynomialBudget count +
          ((2 * count) *
              explicitFamilyRelationPolynomialBudget count +
            explicitFamilyHistoryPolynomialBudget count))))

/-- The exact closed representation budget is bounded by the polynomial envelope. -/
theorem explicitFamilyRepresentationBudget_le_polynomial
    (count : Nat) :
    explicitFamilyRepresentationBudget count ≤
      explicitFamilyRepresentationPolynomialBudget count := by
  have certificateLe :
      explicitFamilyCertificateAtomBinaryBudget count ≤
        explicitFamilyCertificatePolynomialBudget count :=
    explicitFamilyCertificateAtomBinaryBudget_le_polynomial
      count
  unfold explicitFamilyRepresentationBudget
  unfold explicitFamilyRepresentationPolynomialBudget
  rw [
    explicitFamilyStateBinaryBudget_eq_polynomial,
    explicitFamilyProvenanceUnitBinaryBudget_eq_polynomial,
    explicitFamilyRelationEqualityChargeBudget_eq_polynomial,
    explicitFamilyHistoryBinaryBudget_eq_polynomial
  ]
  apply Nat.add_le_add
  · exact Nat.le_refl _
  · apply Nat.add_le_add
    · exact Nat.le_refl _
    · apply Nat.add_le_add
      · exact Nat.le_refl _
      · apply Nat.add_le_add
        · exact
            Nat.mul_le_mul_left
              count
              certificateLe
        · exact Nat.le_refl _

/--
Unconditional polynomial bound for the concrete representation-charged cost
of the announced F(n) strategy.
-/
theorem explicitFamilyRepresentationChargedCost_le_polynomial
    (count : Nat) :
    explicitFamilyRepresentationChargedCost count ≤
      explicitFamilyRepresentationPolynomialBudget count := by
  rw [explicitFamilyRepresentationChargedCost_eq_budget]
  exact
    explicitFamilyRepresentationBudget_le_polynomial
      count

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Clause.binaryBudget_closed
#print axioms ConstitutiveSearch.SAT.StructuralDecisionHistory.binaryBudget_closed
#print axioms ConstitutiveSearch.SAT.doubleBlockStep
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBinaryBudget_closed
#print axioms ConstitutiveSearch.SAT.explicitFamilyFormulaPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyHistoryPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyStatePolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenancePolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificatePolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyHistoryBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyStateBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenanceUnitBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateAtomBinaryBudget_le_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationEqualityChargeBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationBudget_le_polynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationChargedCost_le_polynomial
/- AXIOM_AUDIT_END -/
