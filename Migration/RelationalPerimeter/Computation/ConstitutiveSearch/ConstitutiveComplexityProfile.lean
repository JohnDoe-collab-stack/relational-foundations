import RelationalPerimeter.Computation.ConstitutiveSearch.MachineCostInterface
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

/-!
# Multidimensional constitutive complexity profiles

The existing complexity layer already distinguishes certified event counts from
their representation charges and from any later machine-cost model.

This module packages the quantitative dimensions that have emerged from the
constitutive-search development without collapsing them into one scalar:

* concrete binary input size;
* constitutive trajectory depth;
* maximal frontier width;
* the full certified ComplexityCounts event vector;
* aggregate representation charge.

Machine cost is intentionally absent from the profile.  It may only be related
later through MachineCostInterface and an explicit RepresentationMachineBridge.
-/

namespace ConstitutiveSearch

/-- Quantitative profile of one announced constitutive-search execution. -/
structure ConstitutiveComplexityProfile where
  inputBits : Nat
  depth : Nat
  maxFrontierWidth : Nat
  events : ComplexityCounts
  representationCharge : Nat

namespace ComplexityCounts

/-- Componentwise addition of event profiles from sequentially accounted phases. -/
def add
    (left right : ComplexityCounts) :
    ComplexityCounts :=
  { syntaxUnits :=
      left.syntaxUnits + right.syntaxUnits
    frontierSlots :=
      left.frontierSlots + right.frontierSlots
    provenanceUnits :=
      left.provenanceUnits + right.provenanceUnits
    certificateAtoms :=
      left.certificateAtoms + right.certificateAtoms
    relationFindCalls :=
      left.relationFindCalls + right.relationFindCalls
    closurePrimitiveQueries :=
      left.closurePrimitiveQueries +
        right.closurePrimitiveQueries
    closureCompositionCandidates :=
      left.closureCompositionCandidates +
        right.closureCompositionCandidates
    terminalChecks :=
      left.terminalChecks + right.terminalChecks }

/-- Zero event profile. -/
def zero : ComplexityCounts :=
  { syntaxUnits := 0
    frontierSlots := 0
    provenanceUnits := 0
    certificateAtoms := 0
    relationFindCalls := 0
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 0 }

theorem zero_add
    (counts : ComplexityCounts) :
    add zero counts = counts := by
  cases counts with
  | mk syntaxCount frontier provenance certificate relation primitive candidate terminal =>
      unfold add zero
      rw [
        Nat.zero_add syntaxCount,
        Nat.zero_add frontier,
        Nat.zero_add provenance,
        Nat.zero_add certificate,
        Nat.zero_add relation,
        Nat.zero_add primitive,
        Nat.zero_add candidate,
        Nat.zero_add terminal
      ]

theorem add_zero
    (counts : ComplexityCounts) :
    add counts zero = counts := by
  cases counts with
  | mk syntaxCount frontier provenance certificate relation primitive candidate terminal =>
      cases Nat.add_zero syntaxCount
      cases Nat.add_zero frontier
      cases Nat.add_zero provenance
      cases Nat.add_zero certificate
      cases Nat.add_zero relation
      cases Nat.add_zero primitive
      cases Nat.add_zero candidate
      cases Nat.add_zero terminal
      rfl

end ComplexityCounts

/--
Evidence that the scalar representation charge of a profile is exactly the
charge induced by one declared representation-level AtomicCosts assignment.
-/
def RepresentationConsistent
    (profile : ConstitutiveComplexityProfile)
    (representation : AtomicCosts) : Prop :=
  profile.representationCharge =
    chargedCost profile.events representation

/--
Pointwise comparison of two multidimensional profiles.

This is deliberately stronger than comparing only one aggregate scalar.
-/
structure ConstitutiveComplexityProfile.BoundedBy
    (profile envelope : ConstitutiveComplexityProfile) : Prop where
  inputBitsLe :
    profile.inputBits ≤ envelope.inputBits
  depthLe :
    profile.depth ≤ envelope.depth
  widthLe :
    profile.maxFrontierWidth ≤
      envelope.maxFrontierWidth
  syntaxLe :
    profile.events.syntaxUnits ≤
      envelope.events.syntaxUnits
  frontierSlotsLe :
    profile.events.frontierSlots ≤
      envelope.events.frontierSlots
  provenanceLe :
    profile.events.provenanceUnits ≤
      envelope.events.provenanceUnits
  certificateLe :
    profile.events.certificateAtoms ≤
      envelope.events.certificateAtoms
  relationFindLe :
    profile.events.relationFindCalls ≤
      envelope.events.relationFindCalls
  closurePrimitiveLe :
    profile.events.closurePrimitiveQueries ≤
      envelope.events.closurePrimitiveQueries
  closureCandidateLe :
    profile.events.closureCompositionCandidates ≤
      envelope.events.closureCompositionCandidates
  terminalLe :
    profile.events.terminalChecks ≤
      envelope.events.terminalChecks
  representationChargeLe :
    profile.representationCharge ≤
      envelope.representationCharge

namespace ConstitutiveComplexityProfile.BoundedBy

theorem refl
    (profile : ConstitutiveComplexityProfile) :
    profile.BoundedBy profile :=
  { inputBitsLe := Nat.le_refl _
    depthLe := Nat.le_refl _
    widthLe := Nat.le_refl _
    syntaxLe := Nat.le_refl _
    frontierSlotsLe := Nat.le_refl _
    provenanceLe := Nat.le_refl _
    certificateLe := Nat.le_refl _
    relationFindLe := Nat.le_refl _
    closurePrimitiveLe := Nat.le_refl _
    closureCandidateLe := Nat.le_refl _
    terminalLe := Nat.le_refl _
    representationChargeLe := Nat.le_refl _ }

theorem trans
    {first second third :
      ConstitutiveComplexityProfile}
    (firstSecond : first.BoundedBy second)
    (secondThird : second.BoundedBy third) :
    first.BoundedBy third :=
  { inputBitsLe :=
      Nat.le_trans
        firstSecond.inputBitsLe
        secondThird.inputBitsLe
    depthLe :=
      Nat.le_trans
        firstSecond.depthLe
        secondThird.depthLe
    widthLe :=
      Nat.le_trans
        firstSecond.widthLe
        secondThird.widthLe
    syntaxLe :=
      Nat.le_trans
        firstSecond.syntaxLe
        secondThird.syntaxLe
    frontierSlotsLe :=
      Nat.le_trans
        firstSecond.frontierSlotsLe
        secondThird.frontierSlotsLe
    provenanceLe :=
      Nat.le_trans
        firstSecond.provenanceLe
        secondThird.provenanceLe
    certificateLe :=
      Nat.le_trans
        firstSecond.certificateLe
        secondThird.certificateLe
    relationFindLe :=
      Nat.le_trans
        firstSecond.relationFindLe
        secondThird.relationFindLe
    closurePrimitiveLe :=
      Nat.le_trans
        firstSecond.closurePrimitiveLe
        secondThird.closurePrimitiveLe
    closureCandidateLe :=
      Nat.le_trans
        firstSecond.closureCandidateLe
        secondThird.closureCandidateLe
    terminalLe :=
      Nat.le_trans
        firstSecond.terminalLe
        secondThird.terminalLe
    representationChargeLe :=
      Nat.le_trans
        firstSecond.representationChargeLe
        secondThird.representationChargeLe }

end ConstitutiveComplexityProfile.BoundedBy

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile
#print axioms ConstitutiveSearch.ComplexityCounts.add
#print axioms ConstitutiveSearch.ComplexityCounts.zero
#print axioms ConstitutiveSearch.ComplexityCounts.zero_add
#print axioms ConstitutiveSearch.ComplexityCounts.add_zero
#print axioms ConstitutiveSearch.RepresentationConsistent
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.BoundedBy
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.BoundedBy.refl
#print axioms ConstitutiveSearch.ConstitutiveComplexityProfile.BoundedBy.trans
/- AXIOM_AUDIT_END -/
