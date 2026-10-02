import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityProfile
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

/-!
# Sequential composition of constitutive complexity profiles

A constitutive execution is naturally assembled from phases.  This module
defines the corresponding profile-level composition without collapsing the
multidimensional structure.

Sequential composition:
* keeps the larger concrete input-size index;
* adds constitutive depth;
* keeps the larger frontier-width bound;
* adds event vectors componentwise;
* adds representation charges.

Each phase is pointwise bounded by the composed profile.
-/

namespace ConstitutiveSearch

namespace ConstitutiveComplexityProfile

/-- Sequential composition of two already-accounted constitutive phases. -/
def compose
    (first second : ConstitutiveComplexityProfile) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      Nat.max first.inputBits second.inputBits
    depth :=
      first.depth + second.depth
    maxFrontierWidth :=
      Nat.max
        first.maxFrontierWidth
        second.maxFrontierWidth
    events :=
      ComplexityCounts.add
        first.events
        second.events
    representationCharge :=
      first.representationCharge +
        second.representationCharge }

/-- The first phase is pointwise bounded by the sequentially composed profile. -/
theorem left_boundedBy_compose
    (first second : ConstitutiveComplexityProfile) :
    first.BoundedBy
      (compose first second) :=
  { inputBitsLe :=
      Constructive.nat_le_max_left
        first.inputBits
        second.inputBits
    depthLe :=
      Nat.le_add_right
        first.depth
        second.depth
    widthLe :=
      Constructive.nat_le_max_left
        first.maxFrontierWidth
        second.maxFrontierWidth
    syntaxLe :=
      Nat.le_add_right
        first.events.syntaxUnits
        second.events.syntaxUnits
    frontierSlotsLe :=
      Nat.le_add_right
        first.events.frontierSlots
        second.events.frontierSlots
    provenanceLe :=
      Nat.le_add_right
        first.events.provenanceUnits
        second.events.provenanceUnits
    certificateLe :=
      Nat.le_add_right
        first.events.certificateAtoms
        second.events.certificateAtoms
    relationFindLe :=
      Nat.le_add_right
        first.events.relationFindCalls
        second.events.relationFindCalls
    closurePrimitiveLe :=
      Nat.le_add_right
        first.events.closurePrimitiveQueries
        second.events.closurePrimitiveQueries
    closureCandidateLe :=
      Nat.le_add_right
        first.events.closureCompositionCandidates
        second.events.closureCompositionCandidates
    terminalLe :=
      Nat.le_add_right
        first.events.terminalChecks
        second.events.terminalChecks
    representationChargeLe :=
      Nat.le_add_right
        first.representationCharge
        second.representationCharge }

/-- The second phase is pointwise bounded by the sequentially composed profile. -/
theorem right_boundedBy_compose
    (first second : ConstitutiveComplexityProfile) :
    second.BoundedBy
      (compose first second) :=
  { inputBitsLe :=
      Constructive.nat_le_max_right
        first.inputBits
        second.inputBits
    depthLe :=
      Nat.le_add_left
        second.depth
        first.depth
    widthLe :=
      Constructive.nat_le_max_right
        first.maxFrontierWidth
        second.maxFrontierWidth
    syntaxLe :=
      Nat.le_add_left
        second.events.syntaxUnits
        first.events.syntaxUnits
    frontierSlotsLe :=
      Nat.le_add_left
        second.events.frontierSlots
        first.events.frontierSlots
    provenanceLe :=
      Nat.le_add_left
        second.events.provenanceUnits
        first.events.provenanceUnits
    certificateLe :=
      Nat.le_add_left
        second.events.certificateAtoms
        first.events.certificateAtoms
    relationFindLe :=
      Nat.le_add_left
        second.events.relationFindCalls
        first.events.relationFindCalls
    closurePrimitiveLe :=
      Nat.le_add_left
        second.events.closurePrimitiveQueries
        first.events.closurePrimitiveQueries
    closureCandidateLe :=
      Nat.le_add_left
        second.events.closureCompositionCandidates
        first.events.closureCompositionCandidates
    terminalLe :=
      Nat.le_add_left
        second.events.terminalChecks
        first.events.terminalChecks
    representationChargeLe :=
      Nat.le_add_left
        second.representationCharge
        first.representationCharge }

/-- Composition exposes the componentwise-added event vector definitionally. -/
theorem compose_events
    (first second : ConstitutiveComplexityProfile) :
    (compose first second).events =
      ComplexityCounts.add
        first.events
        second.events := by
  rfl

/-- Composition exposes additive representation charge definitionally. -/
theorem compose_representationCharge
    (first second : ConstitutiveComplexityProfile) :
    (compose first second).representationCharge =
      first.representationCharge +
        second.representationCharge := by
  rfl

end ConstitutiveComplexityProfile

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.compose
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.left_boundedBy_compose
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.right_boundedBy_compose
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.compose_events
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.compose_representationCharge
/- AXIOM_AUDIT_END -/
