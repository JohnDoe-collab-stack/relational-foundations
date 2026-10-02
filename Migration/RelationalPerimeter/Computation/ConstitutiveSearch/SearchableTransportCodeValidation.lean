import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCodeValidationCore
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Quantitative envelope for searchable transport-code validation

The executable validator and its semantic correctness live in
`SearchableTransportCodeValidationCore`. This facade adds only the later
input-polynomial accounting layer.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Primitive-query validation cost for a dependent code family. -/
def searchableCodeValidationPrimitiveBudget
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (n : Nat) : Nat :=
  (validateSearchableCode
    (primitive n)
    (code n)).primitiveQueries

/--
If constituted code size is input-polynomial, executable `SearchableBy`
validation cost is input-polynomial with the same envelope.
-/
theorem searchableCodeValidationPrimitiveBudget_inputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (inputBits : Nat → Nat)
    (codeSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (code n).size)) :
    InputPolynomiallyBounded
      inputBits
      (searchableCodeValidationPrimitiveBudget
        primitive
        code) := by
  rcases codeSizeBounded with
    ⟨envelope, codeLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  change
    (validateSearchableCode
        (primitive n)
        (code n)).primitiveQueries ≤
      envelope.eval
        (inputBits n)
  rw [validateSearchableCode_primitiveQueries]
  exact codeLe n

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.searchableCodeValidationPrimitiveBudget
#print axioms ConstitutiveSearch.searchableCodeValidationPrimitiveBudget_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
