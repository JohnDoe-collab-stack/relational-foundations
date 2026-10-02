/-!
# Polynomial cost envelopes

The constitutive complexity development now has explicit input-indexed cost
functions.  This module gives a minimal internal notion of polynomial envelope
without importing an external polynomial library.

A cost polynomial is finite syntax generated from:
* natural constants;
* the input-size variable;
* addition;
* multiplication.

A cost function is PolynomiallyBounded when it is pointwise below the
evaluation of one such finite expression.

This notion is intentionally representation-agnostic.  It says nothing about
which machine model produced the cost function.
-/

namespace ConstitutiveSearch

/-- Finite polynomial syntax over one natural input-size variable. -/
inductive CostPolynomial where
  | constant : Nat → CostPolynomial
  | input : CostPolynomial
  | add : CostPolynomial → CostPolynomial → CostPolynomial
  | mul : CostPolynomial → CostPolynomial → CostPolynomial

namespace CostPolynomial

/-- Evaluate a finite cost polynomial at one concrete input size. -/
def eval : CostPolynomial → Nat → Nat
  | .constant value, _ =>
      value
  | .input, inputBits =>
      inputBits
  | .add left right, inputBits =>
      left.eval inputBits +
        right.eval inputBits
  | .mul left right, inputBits =>
      left.eval inputBits *
        right.eval inputBits

/-- Structural degree of the cost-polynomial syntax. -/
def degree : CostPolynomial → Nat
  | .constant _ =>
      0
  | .input =>
      1
  | .add left right =>
      Nat.max left.degree right.degree
  | .mul left right =>
      left.degree + right.degree


/-- Substitute one cost polynomial for the input variable of another. -/
def substitute
    (outer inner : CostPolynomial) :
    CostPolynomial :=
  match outer with
  | .constant value =>
      .constant value
  | .input =>
      inner
  | .add left right =>
      .add
        (substitute left inner)
        (substitute right inner)
  | .mul left right =>
      .mul
        (substitute left inner)
        (substitute right inner)

/-- Evaluation of polynomial substitution is ordinary function composition. -/
theorem eval_substitute :
    ∀ (outer inner : CostPolynomial) (inputBits : Nat),
      (substitute outer inner).eval inputBits =
        outer.eval (inner.eval inputBits)
  | .constant _value, _inner, _inputBits =>
      rfl
  | .input, _inner, _inputBits =>
      rfl
  | .add left right, inner, inputBits => by
      change
        (substitute left inner).eval inputBits +
            (substitute right inner).eval inputBits =
          left.eval (inner.eval inputBits) +
            right.eval (inner.eval inputBits)
      rw [
        eval_substitute left inner inputBits,
        eval_substitute right inner inputBits
      ]
  | .mul left right, inner, inputBits => by
      change
        (substitute left inner).eval inputBits *
            (substitute right inner).eval inputBits =
          left.eval (inner.eval inputBits) *
            right.eval (inner.eval inputBits)
      rw [
        eval_substitute left inner inputBits,
        eval_substitute right inner inputBits
      ]

end CostPolynomial

/-- Pointwise domination of a cost function by one finite cost polynomial. -/
def PolynomiallyBounded
    (cost : Nat → Nat) : Prop :=
  ∃ envelope : CostPolynomial,
    ∀ inputBits : Nat,
      cost inputBits ≤
        envelope.eval inputBits

namespace PolynomiallyBounded

/-- Any explicit polynomial evaluation is polynomially bounded by itself. -/
theorem exact
    (polynomial : CostPolynomial) :
    PolynomiallyBounded
      (fun inputBits =>
        polynomial.eval inputBits) :=
  ⟨polynomial,
    fun _ =>
      Nat.le_refl _⟩

/-- Constant cost functions are polynomially bounded. -/
theorem constant
    (value : Nat) :
    PolynomiallyBounded
      (fun _inputBits => value) :=
  ⟨CostPolynomial.constant value,
    fun _ =>
      Nat.le_refl _⟩

/-- The identity input-size cost is polynomially bounded. -/
theorem input :
    PolynomiallyBounded
      (fun inputBits => inputBits) :=
  ⟨CostPolynomial.input,
    fun _ =>
      Nat.le_refl _⟩

/-- Generic natural-product monotonicity used by multiplicative envelopes. -/
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
          Nat.mul_comm
            leftSmall
            rightSmall
      _ ≤
        rightSmall * leftLarge :=
          Nat.mul_le_mul_left
            rightSmall
            leftLe
      _ =
        leftLarge * rightSmall :=
          Nat.mul_comm
            rightSmall
            leftLarge
  have second :
      leftLarge * rightSmall ≤
        leftLarge * rightLarge :=
    Nat.mul_le_mul_left
      leftLarge
      rightLe
  exact
    Nat.le_trans
      first
      second

/-- Polynomial domination is closed under pointwise addition. -/
theorem add
    {left right : Nat → Nat}
    (leftBounded :
      PolynomiallyBounded left)
    (rightBounded :
      PolynomiallyBounded right) :
    PolynomiallyBounded
      (fun inputBits =>
        left inputBits +
          right inputBits) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  exact
    ⟨CostPolynomial.add
        leftEnvelope
        rightEnvelope,
      fun inputBits =>
        Nat.add_le_add
          (leftLe inputBits)
          (rightLe inputBits)⟩

/-- Polynomial domination is closed under pointwise multiplication. -/
theorem mul
    {left right : Nat → Nat}
    (leftBounded :
      PolynomiallyBounded left)
    (rightBounded :
      PolynomiallyBounded right) :
    PolynomiallyBounded
      (fun inputBits =>
        left inputBits *
          right inputBits) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  exact
    ⟨CostPolynomial.mul
        leftEnvelope
        rightEnvelope,
      fun inputBits =>
        natMulLeMul
          (leftLe inputBits)
          (rightLe inputBits)⟩

end PolynomiallyBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.CostPolynomial
#print axioms ConstitutiveSearch.CostPolynomial.eval
#print axioms ConstitutiveSearch.CostPolynomial.degree
#print axioms ConstitutiveSearch.CostPolynomial.substitute
#print axioms ConstitutiveSearch.CostPolynomial.eval_substitute
#print axioms ConstitutiveSearch.PolynomiallyBounded
#print axioms ConstitutiveSearch.PolynomiallyBounded.exact
#print axioms ConstitutiveSearch.PolynomiallyBounded.constant
#print axioms ConstitutiveSearch.PolynomiallyBounded.input
#print axioms ConstitutiveSearch.PolynomiallyBounded.natMulLeMul
#print axioms ConstitutiveSearch.PolynomiallyBounded.add
#print axioms ConstitutiveSearch.PolynomiallyBounded.mul
/- AXIOM_AUDIT_END -/
