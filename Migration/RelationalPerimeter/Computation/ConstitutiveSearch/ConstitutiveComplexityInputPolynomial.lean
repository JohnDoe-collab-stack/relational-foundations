import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityPolynomial

/-!
# Input-indexed polynomial constitutive complexity

Polynomial bounds relevant to complexity theory should be evaluated on the
concrete input-size coordinate carried by each profile, not merely on an
external family index.

This module defines that relative notion and proves it stable under sequential
profile composition.

If two phase families are polynomially bounded relative to their own inputBits,
then their composed family is polynomially bounded relative to the composed
inputBits = max(first.inputBits, second.inputBits).
-/

namespace ConstitutiveSearch

namespace CostPolynomial

/-- Cost-polynomial evaluation is monotone in the nonnegative input variable. -/
theorem eval_mono
    (polynomial : CostPolynomial)
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    polynomial.eval small ≤
      polynomial.eval large := by
  induction polynomial with
  | constant value =>
      exact Nat.le_refl value
  | input =>
      exact smallLeLarge
  | add left right leftIH rightIH =>
      exact
        Nat.add_le_add
          leftIH
          rightIH
  | mul left right leftIH rightIH =>
      exact
        PolynomiallyBounded.natMulLeMul
          leftIH
          rightIH

end CostPolynomial

/--
A cost is polynomially bounded relative to a separately supplied input-size
function.
-/
def InputPolynomiallyBounded
    (inputBits cost : Nat → Nat) : Prop :=
  ∃ envelope : CostPolynomial,
    ∀ n : Nat,
      cost n ≤
        envelope.eval
          (inputBits n)

namespace InputPolynomiallyBounded

/-- The input-size function is bounded by the polynomial X itself. -/
theorem self
    (inputBits : Nat → Nat) :
    InputPolynomiallyBounded
      inputBits
      inputBits :=
  ⟨CostPolynomial.input,
    fun _ =>
      Nat.le_refl _⟩

/-- Constant coordinates are input-indexed polynomially bounded. -/
theorem constant
    (inputBits : Nat → Nat)
    (value : Nat) :
    InputPolynomiallyBounded
      inputBits
      (fun _ => value) :=
  ⟨CostPolynomial.constant value,
    fun _ =>
      Nat.le_refl _⟩


/--
Applying one fixed cost polynomial to an input-polynomially bounded quantity
preserves input-polynomial boundedness by syntactic substitution.
-/
theorem apply_polynomial
    {inputBits cost : Nat → Nat}
    (bounded :
      InputPolynomiallyBounded
        inputBits
        cost)
    (polynomial : CostPolynomial) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        polynomial.eval (cost n)) := by
  rcases bounded with
    ⟨envelope, costLe⟩
  refine
    ⟨CostPolynomial.substitute
        polynomial
        envelope,
      ?_⟩
  intro n
  rw [CostPolynomial.eval_substitute]
  exact
    polynomial.eval_mono
      (costLe n)

/--
Additive coordinates remain polynomially bounded when phase input sizes are
merged by maximum.
-/
theorem add_under_max
    {leftInput rightInput leftCost rightCost :
      Nat → Nat}
    (leftBounded :
      InputPolynomiallyBounded
        leftInput
        leftCost)
    (rightBounded :
      InputPolynomiallyBounded
        rightInput
        rightCost) :
    InputPolynomiallyBounded
      (fun n =>
        Nat.max
          (leftInput n)
          (rightInput n))
      (fun n =>
        leftCost n +
          rightCost n) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  refine
    ⟨CostPolynomial.add
        leftEnvelope
        rightEnvelope,
      ?_⟩
  intro n
  have leftAtMax :
      leftCost n ≤
        leftEnvelope.eval
          (Nat.max
            (leftInput n)
            (rightInput n)) :=
    Nat.le_trans
      (leftLe n)
      (leftEnvelope.eval_mono
          (Constructive.nat_le_max_left
          (leftInput n)
          (rightInput n)))
  have rightAtMax :
      rightCost n ≤
        rightEnvelope.eval
          (Nat.max
            (leftInput n)
            (rightInput n)) :=
    Nat.le_trans
      (rightLe n)
      (rightEnvelope.eval_mono
        (Constructive.nat_le_max_right
          (leftInput n)
          (rightInput n)))
  exact
    Nat.add_le_add
      leftAtMax
      rightAtMax

/--
Maximum coordinates remain polynomially bounded after input-size merging.
The sum of the two polynomial envelopes is a safe polynomial envelope for max.
-/
theorem max_under_max
    {leftInput rightInput leftCost rightCost :
      Nat → Nat}
    (leftBounded :
      InputPolynomiallyBounded
        leftInput
        leftCost)
    (rightBounded :
      InputPolynomiallyBounded
        rightInput
        rightCost) :
    InputPolynomiallyBounded
      (fun n =>
        Nat.max
          (leftInput n)
          (rightInput n))
      (fun n =>
        Nat.max
          (leftCost n)
          (rightCost n)) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  refine
    ⟨CostPolynomial.add
        leftEnvelope
        rightEnvelope,
      ?_⟩
  intro n
  exact
    Constructive.nat_max_le
      (leftCost n)
      (rightCost n)
      ((CostPolynomial.add
        leftEnvelope
        rightEnvelope).eval
          (Nat.max
            (leftInput n)
            (rightInput n)))
      (Nat.le_trans
        (Nat.le_trans
          (leftLe n)
          (leftEnvelope.eval_mono
            (Constructive.nat_le_max_left
              (leftInput n)
              (rightInput n))))
        (Nat.le_add_right
          (leftEnvelope.eval
            (Nat.max
              (leftInput n)
              (rightInput n)))
          (rightEnvelope.eval
            (Nat.max
              (leftInput n)
              (rightInput n)))))
      (Nat.le_trans
        (Nat.le_trans
          (rightLe n)
          (rightEnvelope.eval_mono
            (Constructive.nat_le_max_right
              (leftInput n)
              (rightInput n))))
        (Nat.le_add_left
          (rightEnvelope.eval
            (Nat.max
              (leftInput n)
              (rightInput n)))
          (leftEnvelope.eval
            (Nat.max
              (leftInput n)
              (rightInput n)))))

end InputPolynomiallyBounded

/--
Every non-input coordinate of a profile family is polynomially bounded by the
profile family's own concrete inputBits coordinate.
-/
structure ConstitutiveProfileFamilyInputPolynomiallyBounded
    (profile : Nat → ConstitutiveComplexityProfile) : Prop where
  depth :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).depth)
  width :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).maxFrontierWidth)
  syntaxUnits :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.syntaxUnits)
  frontierSlots :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.frontierSlots)
  provenance :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.provenanceUnits)
  certificates :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.certificateAtoms)
  relationFind :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.relationFindCalls)
  closurePrimitive :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.closurePrimitiveQueries)
  closureCandidates :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.closureCompositionCandidates)
  terminal :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events.terminalChecks)
  representationCharge :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).representationCharge)

namespace ConstitutiveProfileFamilyInputPolynomiallyBounded

/--
Sequential profile composition preserves polynomial bounds in the concrete
combined input-size coordinate.
-/
theorem compose
    {first second :
      Nat → ConstitutiveComplexityProfile}
    (firstBounded :
      ConstitutiveProfileFamilyInputPolynomiallyBounded
        first)
    (secondBounded :
      ConstitutiveProfileFamilyInputPolynomiallyBounded
        second) :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      (fun n =>
        ConstitutiveComplexityProfile.compose
          (first n)
          (second n)) :=
  { depth := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).depth +
              (second n).depth)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.depth
          secondBounded.depth
    width := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            Nat.max
              (first n).maxFrontierWidth
              (second n).maxFrontierWidth)
      exact
        InputPolynomiallyBounded.max_under_max
          firstBounded.width
          secondBounded.width
    syntaxUnits := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.syntaxUnits +
              (second n).events.syntaxUnits)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.syntaxUnits
          secondBounded.syntaxUnits
    frontierSlots := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.frontierSlots +
              (second n).events.frontierSlots)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.frontierSlots
          secondBounded.frontierSlots
    provenance := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.provenanceUnits +
              (second n).events.provenanceUnits)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.provenance
          secondBounded.provenance
    certificates := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.certificateAtoms +
              (second n).events.certificateAtoms)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.certificates
          secondBounded.certificates
    relationFind := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.relationFindCalls +
              (second n).events.relationFindCalls)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.relationFind
          secondBounded.relationFind
    closurePrimitive := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.closurePrimitiveQueries +
              (second n).events.closurePrimitiveQueries)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.closurePrimitive
          secondBounded.closurePrimitive
    closureCandidates := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.closureCompositionCandidates +
              (second n).events.closureCompositionCandidates)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.closureCandidates
          secondBounded.closureCandidates
    terminal := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).events.terminalChecks +
              (second n).events.terminalChecks)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.terminal
          secondBounded.terminal
    representationCharge := by
      change
        InputPolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
          (fun n =>
            (first n).representationCharge +
              (second n).representationCharge)
      exact
        InputPolynomiallyBounded.add_under_max
          firstBounded.representationCharge
          secondBounded.representationCharge }

end ConstitutiveProfileFamilyInputPolynomiallyBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.CostPolynomial.eval_mono
#print axioms ConstitutiveSearch.InputPolynomiallyBounded
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.self
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.constant
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.apply_polynomial
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.add_under_max
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.max_under_max
#print axioms ConstitutiveSearch.ConstitutiveProfileFamilyInputPolynomiallyBounded
#print axioms ConstitutiveSearch.ConstitutiveProfileFamilyInputPolynomiallyBounded.compose
/- AXIOM_AUDIT_END -/
