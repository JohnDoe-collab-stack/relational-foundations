import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyPolynomialCosts

/-!
# Input-size indexing for the explicit SAT representation bound

The polynomial representation-cost envelope is initially indexed by the family
parameter n.  This module connects that parameter to the concrete binary size
of the actual input formula F(n).

The bridge has two parts:
* every CNF has encoded binary size at least its clause-list length;
* F(n) has exactly 2n clauses, hence n is bounded by its concrete input size.

The polynomial envelope is then proved monotone and re-indexed by the actual
binary input size.  The final theorem therefore bounds the representation charge
by an explicit polynomial expression evaluated at the concrete encoded input
size, without introducing an external size parameter.

This remains a representation-cost theorem.  It is not a wall-clock theorem for
Lean's runtime or its equality implementation.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Product monotonicity derived only from one-sided Nat multiplication lemmas. -/
theorem natMulLeMul
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (leftLe : leftSmall ≤ leftLarge)
    (rightLe : rightSmall ≤ rightLarge) :
    leftSmall * rightSmall ≤
      leftLarge * rightLarge := by
  have first :
      leftSmall * rightSmall ≤
        leftLarge * rightSmall := by
    calc
      leftSmall * rightSmall
          =
        rightSmall * leftSmall :=
          Nat.mul_comm leftSmall rightSmall
      _ ≤
        rightSmall * leftLarge :=
          Nat.mul_le_mul_left
            rightSmall
            leftLe
      _ =
        leftLarge * rightSmall :=
          Nat.mul_comm rightSmall leftLarge
  have second :
      leftLarge * rightSmall ≤
        leftLarge * rightLarge :=
    Nat.mul_le_mul_left
      leftLarge
      rightLe
  exact
    Nat.le_trans first second

namespace Cnf

/-- Prefix-tag CNF encoding is at least as large as the clause-list length. -/
theorem length_le_binarySize :
    ∀ formula : Cnf,
      formula.length ≤ binarySize formula
  | [] =>
      Nat.zero_le 1
  | clause :: rest => by
      change
        Nat.succ rest.length ≤
          Nat.succ
            (Clause.binarySize clause +
              binarySize rest)
      exact
        Nat.succ_le_succ
          (Nat.le_trans
            (length_le_binarySize rest)
            (Nat.le_add_left
              (binarySize rest)
              (Clause.binarySize clause)))

end Cnf

/-- The formula component of the polynomial envelope is monotone. -/
theorem explicitFamilyFormulaPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyFormulaPolynomialBudget small ≤
      explicitFamilyFormulaPolynomialBudget large := by
  have plusThreeLe :
      small + 3 ≤ large + 3 :=
    Nat.add_le_add_right smallLeLarge 3
  have twiceLe :
      2 * (small + 3) ≤
        2 * (large + 3) :=
    Nat.mul_le_mul_left
      2
      plusThreeLe
  have taggedLe :
      2 * (small + 3) + 1 ≤
        2 * (large + 3) + 1 :=
    Nat.add_le_add_right twiceLe 1
  have pairLe :
      (2 * (small + 3) + 1) +
          (2 * (small + 3) + 1) ≤
        (2 * (large + 3) + 1) +
          (2 * (large + 3) + 1) :=
    Nat.add_le_add taggedLe taggedLe
  have bodyOneLe :
      (2 * (small + 3) + 1) +
            (2 * (small + 3) + 1) +
          1 ≤
        (2 * (large + 3) + 1) +
            (2 * (large + 3) + 1) +
          1 :=
    Nat.add_le_add_right pairLe 1
  have bodyLe :
      (2 * (small + 3) + 1) +
              (2 * (small + 3) + 1) +
            1 +
          1 ≤
        (2 * (large + 3) + 1) +
              (2 * (large + 3) + 1) +
            1 +
          1 :=
    Nat.add_le_add_right bodyOneLe 1
  unfold explicitFamilyFormulaPolynomialBudget
  exact
    Nat.add_le_add_right
      (natMulLeMul
        smallLeLarge
        bodyLe)
      1

/-- The history component of the polynomial envelope is monotone. -/
theorem explicitFamilyHistoryPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyHistoryPolynomialBudget small ≤
      explicitFamilyHistoryPolynomialBudget large := by
  have plusThreeLe :
      small + 3 ≤ large + 3 :=
    Nat.add_le_add_right smallLeLarge 3
  unfold explicitFamilyHistoryPolynomialBudget
  exact
    Nat.add_le_add_right
      (natMulLeMul
        smallLeLarge
        plusThreeLe)
      1

/-- The complete state envelope is monotone. -/
theorem explicitFamilyStatePolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyStatePolynomialBudget small ≤
      explicitFamilyStatePolynomialBudget large := by
  unfold explicitFamilyStatePolynomialBudget
  exact
    Nat.add_le_add
      (explicitFamilyFormulaPolynomialBudget_mono
        smallLeLarge)
      (explicitFamilyHistoryPolynomialBudget_mono
        smallLeLarge)

/-- The provenance-unit envelope is monotone. -/
theorem explicitFamilyProvenancePolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyProvenancePolynomialBudget small ≤
      explicitFamilyProvenancePolynomialBudget large := by
  unfold explicitFamilyProvenancePolynomialBudget
  exact
    Nat.add_le_add_right
      (Nat.mul_le_mul_left
        1
        (Nat.add_le_add_right
          smallLeLarge
          3))
      1

/-- The certificate-atom envelope is monotone. -/
theorem explicitFamilyCertificatePolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyCertificatePolynomialBudget small ≤
      explicitFamilyCertificatePolynomialBudget large := by
  unfold explicitFamilyCertificatePolynomialBudget
  exact
    Nat.succ_le_succ
      (Nat.add_le_add_right
        smallLeLarge
        1)

/-- The relation-query envelope is monotone. -/
theorem explicitFamilyRelationPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyRelationPolynomialBudget small ≤
      explicitFamilyRelationPolynomialBudget large := by
  unfold explicitFamilyRelationPolynomialBudget
  have formulaLe :=
    explicitFamilyFormulaPolynomialBudget_mono
      smallLeLarge
  have historyLe :=
    explicitFamilyHistoryPolynomialBudget_mono
      smallLeLarge
  exact
    Nat.add_le_add
      (Nat.add_le_add
        formulaLe
        formulaLe)
      (Nat.add_le_add
        historyLe
        historyLe)

/-- The complete representation polynomial is monotone in its index. -/
theorem explicitFamilyRepresentationPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    explicitFamilyRepresentationPolynomialBudget small ≤
      explicitFamilyRepresentationPolynomialBudget large := by
  have syntaxLe :
      4 * small ≤
        4 * large :=
    Nat.mul_le_mul_left
      4
      smallLeLarge
  have frontierFactorLe :
      3 * small + 1 ≤
        3 * large + 1 :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_left
        3
        smallLeLarge)
      1
  have frontierLe :
      (3 * small + 1) *
          explicitFamilyStatePolynomialBudget small ≤
        (3 * large + 1) *
          explicitFamilyStatePolynomialBudget large :=
    natMulLeMul
      frontierFactorLe
      (explicitFamilyStatePolynomialBudget_mono
        smallLeLarge)
  have provenanceLe :
      small *
          explicitFamilyProvenancePolynomialBudget small ≤
        large *
          explicitFamilyProvenancePolynomialBudget large :=
    natMulLeMul
      smallLeLarge
      (explicitFamilyProvenancePolynomialBudget_mono
        smallLeLarge)
  have certificateLe :
      small *
          explicitFamilyCertificatePolynomialBudget small ≤
        large *
          explicitFamilyCertificatePolynomialBudget large :=
    natMulLeMul
      smallLeLarge
      (explicitFamilyCertificatePolynomialBudget_mono
        smallLeLarge)
  have relationFactorLe :
      2 * small ≤
        2 * large :=
    Nat.mul_le_mul_left
      2
      smallLeLarge
  have relationLe :
      (2 * small) *
          explicitFamilyRelationPolynomialBudget small ≤
        (2 * large) *
          explicitFamilyRelationPolynomialBudget large :=
    natMulLeMul
      relationFactorLe
      (explicitFamilyRelationPolynomialBudget_mono
        smallLeLarge)
  have historyLe :
      explicitFamilyHistoryPolynomialBudget small ≤
        explicitFamilyHistoryPolynomialBudget large :=
    explicitFamilyHistoryPolynomialBudget_mono
      smallLeLarge
  unfold explicitFamilyRepresentationPolynomialBudget
  exact
    Nat.add_le_add
      syntaxLe
      (Nat.add_le_add
        frontierLe
        (Nat.add_le_add
          provenanceLe
          (Nat.add_le_add
            certificateLe
            (Nat.add_le_add
              relationLe
              historyLe))))

/-- Concrete binary input size of the closed family member F(n). -/
def explicitFamilyInputBitSize
    (count : Nat) : Nat :=
  Cnf.binarySize
    (explicitStackedSymmetricFamily count)

/-- The family parameter n is bounded by the concrete binary input size of F(n). -/
theorem explicitFamilyIndex_le_inputBitSize
    (count : Nat) :
    count ≤
      explicitFamilyInputBitSize count := by
  have countLeTwice :
      count ≤ 2 * count := by
    calc
      count ≤ count + count :=
        Nat.le_add_right count count
      _ = 1 * count + count := by
        rw [Nat.one_mul]
      _ = Nat.succ 1 * count :=
        (Nat.succ_mul 1 count).symm
      _ = 2 * count :=
        rfl
  have formulaLength :
      (explicitStackedSymmetricFamily count).length =
        2 * count := by
    change
      (stackedSymmetricBlocks count count).length =
        2 * count
    exact
      stackedSymmetricBlocks_length
        count
        count
  have lengthLeSize :
      (explicitStackedSymmetricFamily count).length ≤
        Cnf.binarySize
          (explicitStackedSymmetricFamily count) :=
    Cnf.length_le_binarySize
      (explicitStackedSymmetricFamily count)
  unfold explicitFamilyInputBitSize
  exact
    Nat.le_trans
      countLeTwice
      (Nat.le_trans
        (Nat.le_of_eq formulaLength.symm)
        lengthLeSize)

/-- Polynomial envelope indexed by the actual encoded input size. -/
def explicitFamilyInputIndexedPolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyRepresentationPolynomialBudget
    (explicitFamilyInputBitSize count)

/--
The concrete representation-charged cost is polynomially bounded in the actual
binary input size of the corresponding F(n).
-/
theorem explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial
    (count : Nat) :
    explicitFamilyRepresentationChargedCost count ≤
      explicitFamilyInputIndexedPolynomialBudget count := by
  exact
    Nat.le_trans
      (explicitFamilyRepresentationChargedCost_le_polynomial
        count)
      (explicitFamilyRepresentationPolynomialBudget_mono
        (explicitFamilyIndex_le_inputBitSize
          count))

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.natMulLeMul
#print axioms ConstitutiveSearch.SAT.Cnf.length_le_binarySize
#print axioms ConstitutiveSearch.SAT.explicitFamilyFormulaPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyHistoryPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyStatePolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenancePolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificatePolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.explicitFamilyInputBitSize
#print axioms ConstitutiveSearch.SAT.explicitFamilyIndex_le_inputBitSize
#print axioms ConstitutiveSearch.SAT.explicitFamilyInputIndexedPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial
/- AXIOM_AUDIT_END -/
