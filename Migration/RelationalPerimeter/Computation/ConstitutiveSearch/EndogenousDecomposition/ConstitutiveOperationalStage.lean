import RelationalPerimeter.Computation.ConstitutiveGeneration
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GrowingDiscoveryFamily

/-!
# Constitutive stages and their operational execution

This module begins a new isolated integration layer for `endogenous operational decomposition`.

The dependency order is explicit:

1. `iteratedHistory` constructs the constitutive history;
2. `positiveDepth` reads the produced endpoint;
3. only then is an operational SAT search state built from that readout.

A `GeneratedStep` remains constitutive data.  Nothing in this module converts a
generated step into a transport or assumes that an operational relation exists.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open ConstitutiveGeneration
open SAT

/-- The actual circular history obtained after `depth` calls to the producer. -/
def constitutedHistory (depth : Nat) :
    RootedGeneratedHistory examplePresentation :=
  iteratedHistory examplePresentation depth

/-- The endpoint produced by the actual constitutive history. -/
def constitutedEndpoint (depth : Nat) :
    PositiveConstitution examplePresentation :=
  (constitutedHistory depth).endpoint

/--
Operational index read from the endpoint already produced by constitution.
It is not the external depth parameter copied into the operational layer.
-/
def constitutedOperationalIndex (depth : Nat) : Nat :=
  positiveDepth (constitutedEndpoint depth)

/--
The search family uses a spaced index derived from the constituted readout.
Spacing prevents the anchor of one accepted local problem from becoming the
selected variable of the next problem.  It is computed from constitution and
is not an independently supplied search parameter.
-/
def constitutedSearchIndex (depth : Nat) : Nat :=
  2 * constitutedOperationalIndex depth

/-- The endpoint readout advances exactly when the real producer advances. -/
theorem constitutedOperationalIndex_succ (depth : Nat) :
    constitutedOperationalIndex (depth + 1) =
      constitutedOperationalIndex depth + 1 := by
  exact
    positiveDepth_canonicalTarget
      (constitutedEndpoint depth)

/-- Consequently, operational indices of successive constituted stages differ. -/
theorem constitutedOperationalIndex_succ_ne (depth : Nat) :
    constitutedOperationalIndex (depth + 1) ≠
      constitutedOperationalIndex depth := by
  rw [constitutedOperationalIndex_succ]
  exact Nat.ne_of_gt (Nat.lt_succ_self _)

/-- The canonical perimeter starts at depth three and advances once per generation. -/
theorem constitutedOperationalIndex_exact (depth : Nat) :
    constitutedOperationalIndex depth = depth + 3 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [constitutedOperationalIndex_succ, inductionHypothesis]

theorem constitutedSearchIndex_succ (depth : Nat) :
    constitutedSearchIndex (depth + 1) = constitutedSearchIndex depth + 2 := by
  unfold constitutedSearchIndex
  rw [constitutedOperationalIndex_succ]
  exact Nat.mul_add 2 (constitutedOperationalIndex depth) 1

theorem constitutedSearchIndex_exact (depth : Nat) :
    constitutedSearchIndex depth = 2 * (depth + 3) := by
  unfold constitutedSearchIndex
  rw [constitutedOperationalIndex_exact]

theorem constitutedSearchIndex_linear (depth : Nat) :
    constitutedSearchIndex depth = 2 * depth + 6 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [constitutedSearchIndex_succ, inductionHypothesis]
      rw [Nat.mul_add]

theorem constitutedSearchIndex_next_add_five (depth : Nat) :
    constitutedSearchIndex (depth + 1) + 5 = 2 * depth + 13 := by
  rw [constitutedSearchIndex_succ, constitutedSearchIndex_linear]

theorem constitutedSearchIndex_next_add_two (depth : Nat) :
    constitutedSearchIndex (depth + 1) + 2 = 2 * depth + 10 := by
  rw [constitutedSearchIndex_succ, constitutedSearchIndex_linear]

/--
One fully constructed stage. Constitution, structural readout, and operational
root remain separate fields connected by exact equations.
-/
structure ConstitutiveOperationalStage (depth : Nat) where
  history : RootedGeneratedHistory examplePresentation
  historyExact : history = constitutedHistory depth
  operationalIndex : Nat
  operationalIndexExact :
    operationalIndex = positiveDepth history.endpoint
  searchIndex : Nat
  searchIndexExact : searchIndex = 2 * operationalIndex
  operationalRoot :
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula searchIndex)
  operationalRootExact :
    operationalRoot = distinctGrowingDiscoveryRoot searchIndex

/-- Canonical construction of a stage, with no independently supplied target. -/
def constructStage (depth : Nat) : ConstitutiveOperationalStage depth :=
  { history := constitutedHistory depth
    historyExact := rfl
    operationalIndex := constitutedOperationalIndex depth
    operationalIndexExact := rfl
    searchIndex := constitutedSearchIndex depth
    searchIndexExact := rfl
    operationalRoot :=
      distinctGrowingDiscoveryRoot (constitutedSearchIndex depth)
    operationalRootExact := rfl }

/-- The operational index of the canonical stage is read from its constitution. -/
theorem constructStage_operationalIndex (depth : Nat) :
    (constructStage depth).operationalIndex =
      positiveDepth (constructStage depth).history.endpoint :=
  (constructStage depth).operationalIndexExact

/-- The operational root of the canonical stage is the executable growing root. -/
theorem constructStage_operationalRoot (depth : Nat) :
    (constructStage depth).operationalRoot =
      distinctGrowingDiscoveryRoot
        (constructStage depth).searchIndex :=
  (constructStage depth).operationalRootExact

theorem constructStage_searchIndex (depth : Nat) :
    (constructStage depth).searchIndex =
      2 * (constructStage depth).operationalIndex :=
  (constructStage depth).searchIndexExact

/--
The constitutive transition between canonical successive stages is the actual
`GeneratedStep` returned by the producer.  It carries no operational relation.
-/
structure CanonicalStageGeneration (depth : Nat) where
  target : PositiveConstitution examplePresentation
  targetExact : target = (constructStage (depth + 1)).history.endpoint
  generated :
    GeneratedStep
      (constructStage depth).history.endpoint
      target
  generateCalls : Nat
  generatedSteps : Nat
  provenanceUnits : Nat
  certificatesProduced : Nat

/-- Produce the next constitutive stage and its genuine generation witness. -/
def generateCanonicalStage (depth : Nat) :
    CanonicalStageGeneration depth :=
  let produced := generate (constitutedHistory depth).endpoint
  { target := produced.1
    targetExact := rfl
    generated := produced.2
    generateCalls := 1
    generatedSteps := 1
    provenanceUnits := 1
    certificatesProduced := 1 }

/-- Generate directly from the supplied previously produced endpoint. -/
def generateCanonicalStageFromSource {depth : Nat}
    (source : PositiveConstitution examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    CanonicalStageGeneration depth :=
  let produced := generate source
  { target := produced.1
    targetExact := by cases sourceExact; rfl
    generated := by rw [← sourceExact]; exact produced.2
    generateCalls := 1
    generatedSteps := 1
    provenanceUnits := 1
    certificatesProduced := 1 }

theorem generateCanonicalStageFromSource_exact {depth : Nat}
    (source : PositiveConstitution examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    generateCanonicalStageFromSource source sourceExact = generateCanonicalStage depth := by
  cases sourceExact
  rfl

theorem generateCanonicalStage_index_advances (depth : Nat) :
    (constructStage (depth + 1)).operationalIndex =
      (constructStage depth).operationalIndex + 1 :=
  constitutedOperationalIndex_succ depth

theorem generateCanonicalStage_searchIndex_advances (depth : Nat) :
    (constructStage (depth + 1)).searchIndex =
      (constructStage depth).searchIndex + 2 :=
  constitutedSearchIndex_succ depth

/-- Old occurrences are embedded exactly by the real successor construction. -/
theorem constitutedOldOccurrence_persists
    (depth : Nat)
    (occurrence : History.Occurrence (constitutedHistory depth).history) :
    (successorOccurrenceSplit examplePresentation depth).forward (.inl occurrence) =
      History.Occurrence.earlier occurrence :=
  successorOccurrenceSplit_old examplePresentation depth occurrence

/-- Preserve the actual precedence relation between old occurrences. -/
theorem constitutedOccurrence_order_preserved
    (depth : Nat)
    {first second : History.Occurrence (constitutedHistory depth).history}
    (before : History.OccurrencePrecedes first second) :
    History.OccurrencePrecedes
      ((successorOccurrenceSplit examplePresentation depth).forward (.inl first))
      ((successorOccurrenceSplit examplePresentation depth).forward (.inl second)) := by
  rw [constitutedOldOccurrence_persists, constitutedOldOccurrence_persists]
  exact History.OccurrencePrecedes.earlier_earlier before

theorem constitutedFreshOccurrence_isLast (depth : Nat) :
    (successorOccurrenceSplit examplePresentation depth).forward (.inr ()) =
      History.Occurrence.last :=
  successorOccurrenceSplit_fresh examplePresentation depth

/-- Old and freshly produced occurrences remain constructively distinct. -/
theorem constitutedOldOccurrence_ne_fresh
    (depth : Nat)
    (occurrence : History.Occurrence (constitutedHistory depth).history) :
    History.Occurrence.earlier occurrence ≠
      (History.Occurrence.last :
        History.Occurrence (constitutedHistory (depth + 1)).history) := by
  intro impossible
  cases impossible

/-- Closed constitutive evidence reused by the operational resolution layer. -/
structure ConstitutiveStageEvidence (depth : Nat) : Type 2 where
  stage : ConstitutiveOperationalStage depth
  stageExact : stage = constructStage depth
  generation : CanonicalStageGeneration depth
  generationExact : generation = generateCanonicalStage depth
  oldOccurrencePersists :
    ∀ occurrence : History.Occurrence (constitutedHistory depth).history,
      (successorOccurrenceSplit examplePresentation depth).forward (.inl occurrence) =
        History.Occurrence.earlier occurrence
  oldOccurrenceOrderPreserved :
    ∀ {first second : History.Occurrence (constitutedHistory depth).history},
      History.OccurrencePrecedes first second →
      History.OccurrencePrecedes
        ((successorOccurrenceSplit examplePresentation depth).forward (.inl first))
        ((successorOccurrenceSplit examplePresentation depth).forward (.inl second))
  freshOccurrenceIsLast :
    (successorOccurrenceSplit examplePresentation depth).forward (.inr ()) =
      History.Occurrence.last
  oldFreshDistinct :
    ∀ occurrence : History.Occurrence (constitutedHistory depth).history,
      History.Occurrence.earlier occurrence ≠
        (History.Occurrence.last :
          History.Occurrence (constitutedHistory (depth + 1)).history)
  provenancePersists :
    PreservesProvenance
      (constructStage depth).history.endpoint
      (constructStage (depth + 1)).history.endpoint
  residualDifferenceRemainsFresh :
    FreshBoundaryDifference (constructStage depth).history.endpoint

def constitutiveStageEvidence
    (depth : Nat) : ConstitutiveStageEvidence depth :=
  { stage := constructStage depth
    stageExact := rfl
    generation := generateCanonicalStage depth
    generationExact := rfl
    oldOccurrencePersists := constitutedOldOccurrence_persists depth
    oldOccurrenceOrderPreserved := constitutedOccurrence_order_preserved depth
    freshOccurrenceIsLast := constitutedFreshOccurrence_isLast depth
    oldFreshDistinct := constitutedOldOccurrence_ne_fresh depth
    provenancePersists :=
      (generateCanonicalStage depth).generated.preservesProvenance
    residualDifferenceRemainsFresh :=
      (generateCanonicalStage depth).generated.laws.freshBoundaryDifference }

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CanonicalStageGeneration
#print axioms ConstitutiveSearch.EndogenousDecomposition.generateCanonicalStageFromSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.generateCanonicalStageFromSource_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedOperationalIndex_succ
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedOperationalIndex_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedSearchIndex_succ
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedSearchIndex_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedSearchIndex_linear
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedSearchIndex_next_add_five
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedSearchIndex_next_add_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.generateCanonicalStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.generateCanonicalStage_index_advances
#print axioms ConstitutiveSearch.EndogenousDecomposition.generateCanonicalStage_searchIndex_advances
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedOldOccurrence_persists
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedOccurrence_order_preserved
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedFreshOccurrence_isLast
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutedOldOccurrence_ne_fresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveStageEvidence
/- AXIOM_AUDIT_END -/
