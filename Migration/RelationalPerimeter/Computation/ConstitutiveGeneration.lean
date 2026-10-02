import RelationalFoundations.ConstitutiveGeneration
import StrongPerimetralTurning

/-!
# Constitutive generation for computation

This module exposes exactly the structural material that the computation reads
from the relational perimeter.  Starting from the canonical perimeter, it
iterates the actual free generator and records the exact old/fresh split of
occurrences at every successor step.

No concrete realization, comparison between representations, acceptance
criterion, search relation, or operational decision occurs in this layer.
-/

namespace ConstitutiveSearch
namespace ConstitutiveGeneration

open StrongPerimetralTurning

universe uState uStep

/-- Formation depth is read structurally from a freely constituted state. -/
def formationDepth
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {difference : BoundaryDifferenceCode P cursor} :
    FreeConstitutionCore P cursor difference → Nat
  | .root => 0
  | .formed previous _ => formationDepth previous + 1

/-- The depth carried by a positive constitution. -/
def positiveDepth
    {P : CircularPresentation}
    (state : PositiveConstitution P) : Nat :=
  formationDepth state.2.1.2

@[simp] theorem positiveDepth_canonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    positiveDepth (canonicalTarget source) = positiveDepth source + 1 :=
  rfl

/-- Iterate the actual free producer from the canonical perimeter. -/
def iteratedHistory (P : CircularPresentation) : Nat → RootedGeneratedHistory P :=
  RelationalFoundations.ConstitutiveGeneration.iterate (perimeterDeployment P) (fun state => generate state)
@[simp] theorem iteratedHistory_zero
    (P : CircularPresentation) :
    iteratedHistory P 0 = perimeterDeployment P :=
  rfl

@[simp] theorem iteratedHistory_one
    (P : CircularPresentation) :
    iteratedHistory P 1 = oneStepAfterPerimeter P :=
  rfl

/-- Appending one step adds exactly one occurrence. -/
abbrev appendExactlyOneOccurrenceTransport :=
  @RelationalFoundations.ConstitutiveGeneration.appendExactlyOneOccurrenceTransport
/-- Every generated successor continuation contains exactly its new step. -/
def successorContinuationExactlyOne
    (P : CircularPresentation)
    (n : Nat) :
    History.ExactlyOne
      (History.extend History.root
        (generate (iteratedHistory P n).endpoint).2) :=
  .single (generate (iteratedHistory P n).endpoint).2

/--
The successor occurrence carrier is exactly the old carrier plus the newly
generated occurrence.
-/
def successorOccurrenceSplit
    (P : CircularPresentation)
    (n : Nat) :
    RelationalFoundations.ExactTransport
      (History.Occurrence (iteratedHistory P n).history ⊕ Unit)
      (History.Occurrence (iteratedHistory P (n + 1)).history) :=
  appendExactlyOneOccurrenceTransport
    (iteratedHistory P n).history
    (successorContinuationExactlyOne P n)

@[simp] theorem successorOccurrenceSplit_old
    (P : CircularPresentation)
    (n : Nat)
    (occurrence : History.Occurrence (iteratedHistory P n).history) :
    (successorOccurrenceSplit P n).forward (.inl occurrence) =
      History.Occurrence.earlier occurrence :=
  rfl

@[simp] theorem successorOccurrenceSplit_fresh
    (P : CircularPresentation)
    (n : Nat) :
    (successorOccurrenceSplit P n).forward (.inr ()) =
      History.Occurrence.last :=
  rfl

end ConstitutiveGeneration
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutiveGeneration.positiveDepth_canonicalTarget
#print axioms ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory
#print axioms ConstitutiveSearch.ConstitutiveGeneration.appendExactlyOneOccurrenceTransport
#print axioms ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit
#print axioms ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit_old
#print axioms ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit_fresh
/- AXIOM_AUDIT_END -/
