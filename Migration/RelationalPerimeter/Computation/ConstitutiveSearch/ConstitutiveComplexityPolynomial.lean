import RelationalPerimeter.Computation.ConstitutiveSearch.PolynomialCostEnvelope
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityComposition

/-!
# Polynomially bounded families of constitutive complexity profiles

A single constitutive profile is multidimensional.  For asymptotic reasoning we
therefore require polynomial envelopes component by component rather than
collapsing the profile into one scalar.

This module packages polynomial bounds for:
* concrete input-size coordinate;
* constitutive depth;
* maximal frontier width;
* every ComplexityCounts event coordinate;
* aggregate representation charge.

Sequential composition preserves this property.
-/

namespace ConstitutiveSearch

/-- Pointwise maximum of polynomially bounded costs is polynomially bounded. -/
theorem polynomiallyBounded_max
    {left right : Nat → Nat}
    (leftBounded :
      PolynomiallyBounded left)
    (rightBounded :
      PolynomiallyBounded right) :
    PolynomiallyBounded
      (fun inputBits =>
        Nat.max
          (left inputBits)
          (right inputBits)) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  refine
    ⟨CostPolynomial.add
        leftEnvelope
        rightEnvelope,
      ?_⟩
  intro inputBits
  exact
    Constructive.nat_max_le
      (left inputBits)
      (right inputBits)
      ((CostPolynomial.add
        leftEnvelope
        rightEnvelope).eval inputBits)
      (Nat.le_trans
        (leftLe inputBits)
        (Nat.le_add_right
          (leftEnvelope.eval inputBits)
          (rightEnvelope.eval inputBits)))
      (Nat.le_trans
        (rightLe inputBits)
        (Nat.le_add_left
          (rightEnvelope.eval inputBits)
          (leftEnvelope.eval inputBits)))

/--
Polynomial asymptotic envelope for every coordinate of a profile family.
-/
structure ConstitutiveProfileFamilyPolynomiallyBounded
    (profile : Nat → ConstitutiveComplexityProfile) : Prop where
  inputBits :
    PolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
  depth :
    PolynomiallyBounded
      (fun n =>
        (profile n).depth)
  width :
    PolynomiallyBounded
      (fun n =>
        (profile n).maxFrontierWidth)
  syntaxUnits :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.syntaxUnits)
  frontierSlots :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.frontierSlots)
  provenance :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.provenanceUnits)
  certificates :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.certificateAtoms)
  relationFind :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.relationFindCalls)
  closurePrimitive :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.closurePrimitiveQueries)
  closureCandidates :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.closureCompositionCandidates)
  terminal :
    PolynomiallyBounded
      (fun n =>
        (profile n).events.terminalChecks)
  representationCharge :
    PolynomiallyBounded
      (fun n =>
        (profile n).representationCharge)

namespace ConstitutiveProfileFamilyPolynomiallyBounded

/--
Sequential composition of two polynomially bounded profile families remains
polynomially bounded in every constitutive dimension.
-/
theorem compose
    {first second :
      Nat → ConstitutiveComplexityProfile}
    (firstBounded :
      ConstitutiveProfileFamilyPolynomiallyBounded
        first)
    (secondBounded :
      ConstitutiveProfileFamilyPolynomiallyBounded
        second) :
    ConstitutiveProfileFamilyPolynomiallyBounded
      (fun n =>
        ConstitutiveComplexityProfile.compose
          (first n)
          (second n)) :=
  { inputBits := by
      change
        PolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).inputBits
              (second n).inputBits)
      exact
        polynomiallyBounded_max
          firstBounded.inputBits
          secondBounded.inputBits
    depth := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).depth +
              (second n).depth)
      exact
        PolynomiallyBounded.add
          firstBounded.depth
          secondBounded.depth
    width := by
      change
        PolynomiallyBounded
          (fun n =>
            Nat.max
              (first n).maxFrontierWidth
              (second n).maxFrontierWidth)
      exact
        polynomiallyBounded_max
          firstBounded.width
          secondBounded.width
    syntaxUnits := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.syntaxUnits +
              (second n).events.syntaxUnits)
      exact
        PolynomiallyBounded.add
          firstBounded.syntaxUnits
          secondBounded.syntaxUnits
    frontierSlots := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.frontierSlots +
              (second n).events.frontierSlots)
      exact
        PolynomiallyBounded.add
          firstBounded.frontierSlots
          secondBounded.frontierSlots
    provenance := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.provenanceUnits +
              (second n).events.provenanceUnits)
      exact
        PolynomiallyBounded.add
          firstBounded.provenance
          secondBounded.provenance
    certificates := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.certificateAtoms +
              (second n).events.certificateAtoms)
      exact
        PolynomiallyBounded.add
          firstBounded.certificates
          secondBounded.certificates
    relationFind := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.relationFindCalls +
              (second n).events.relationFindCalls)
      exact
        PolynomiallyBounded.add
          firstBounded.relationFind
          secondBounded.relationFind
    closurePrimitive := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.closurePrimitiveQueries +
              (second n).events.closurePrimitiveQueries)
      exact
        PolynomiallyBounded.add
          firstBounded.closurePrimitive
          secondBounded.closurePrimitive
    closureCandidates := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.closureCompositionCandidates +
              (second n).events.closureCompositionCandidates)
      exact
        PolynomiallyBounded.add
          firstBounded.closureCandidates
          secondBounded.closureCandidates
    terminal := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).events.terminalChecks +
              (second n).events.terminalChecks)
      exact
        PolynomiallyBounded.add
          firstBounded.terminal
          secondBounded.terminal
    representationCharge := by
      change
        PolynomiallyBounded
          (fun n =>
            (first n).representationCharge +
              (second n).representationCharge)
      exact
        PolynomiallyBounded.add
          firstBounded.representationCharge
          secondBounded.representationCharge }

end ConstitutiveProfileFamilyPolynomiallyBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.polynomiallyBounded_max
#print axioms ConstitutiveSearch.ConstitutiveProfileFamilyPolynomiallyBounded
#print axioms ConstitutiveSearch.ConstitutiveProfileFamilyPolynomiallyBounded.compose
/- AXIOM_AUDIT_END -/
