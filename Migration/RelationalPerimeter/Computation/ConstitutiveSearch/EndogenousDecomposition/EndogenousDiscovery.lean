import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredDiscovery
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GrowingDiscoveryBenchmark

/-!
# Endogenous discovery after constitution

Discovery is run only after `constructStage` has produced the constitutive
history and the operational root read from its produced endpoint. The selected
variable and relation are outputs of the executable run.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open ConstitutiveGeneration

/-- Execute candidate extraction and exploration on the realized stage. -/
def stageDiscoveryRun (depth : Nat) :
    EndogenousDiscoveryRun (constructStage depth).operationalRoot :=
  runEndogenousFlipDiscovery (constructStage depth).operationalRoot

/-- The candidate list is the output of executable extraction at this stage. -/
def stageExtractedCandidates (depth : Nat) : List Var :=
  (stageDiscoveryRun depth).candidates

/-- Exploration trace emitted by the same recursion that attempts candidates. -/
structure RecordedDiscoveryOutcome
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  produced? : Option (Sigma (ProducedFlipCandidate state))
  testedCandidates : List Var
  attempts : Nat
  candidateConstructions : Nat
  variableComparisonUnits : Nat
  formulaComparisonLiteralVisits : Nat
  historyComparisonDecisionVisits : Nat
  relationQueries : Nat
  comparisonWork : ComparisonWork
  constructionWork : ComparisonWork

def RecordedDiscoveryOutcome.discovered? {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (outcome : RecordedDiscoveryOutcome state) : Option (EndogenousFlipDiscovery state) :=
  outcome.produced?.map (fun produced => ⟨produced.1, produced.2.discovery⟩)

/--
Legacy structural surface attached to an attempt. These fields are computed
from representation sizes, not from the comparison recursion. They must not
be interpreted as exact executed comparison visits. The actual comparator
work is recorded separately in `RecordedDiscoveryOutcome.comparisonWork`.
-/
structure CandidateAttemptWork where
  candidateConstructions : Nat
  variableComparisonUnits : Nat
  formulaComparisonLiteralVisits : Nat
  historyComparisonDecisionVisits : Nat
  relationQueries : Nat
  deriving DecidableEq, Repr

def candidateAttemptWork
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    CandidateAttemptWork :=
  let formulaVisits := Cnf.literalCount state.context.formula
  let historyVisits := state.context.decisions.length + 1
  { candidateConstructions := 2
    variableComparisonUnits := formulaVisits + historyVisits
    formulaComparisonLiteralVisits := formulaVisits
    historyComparisonDecisionVisits := historyVisits
    relationQueries := 1 }

/--
Explore candidates while retaining the exact tested prefix.  Each recursive
head invokes the real candidate attempt exactly once and emits its own charge.
-/
def exploreRecordedCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var → RecordedDiscoveryOutcome state
  | [] =>
      { produced? := none
        testedCandidates := []
        attempts := 0
        candidateConstructions := 0
        variableComparisonUnits := 0
        formulaComparisonLiteralVisits := 0
        historyComparisonDecisionVisits := 0
        relationQueries := 0
        comparisonWork := .zero
        constructionWork := .zero }
  | candidate :: rest =>
      let work := candidateAttemptWork state
      let measured := tryMeasuredCandidate state candidate
      match measured.produced? with
      | some candidateDiscovery =>
          { produced? := some ⟨candidate, candidateDiscovery⟩
            testedCandidates := [candidate]
            attempts := 1
            candidateConstructions := work.candidateConstructions
            variableComparisonUnits := work.variableComparisonUnits
            formulaComparisonLiteralVisits :=
              work.formulaComparisonLiteralVisits
            historyComparisonDecisionVisits :=
              work.historyComparisonDecisionVisits
            relationQueries := work.relationQueries
            comparisonWork := measured.freshnessWork.add measured.relationWork
            constructionWork := measured.constructionWork }
      | none =>
          let tail := exploreRecordedCandidates state rest
          { produced? := tail.produced?
            testedCandidates := candidate :: tail.testedCandidates
            attempts := tail.attempts + 1
            candidateConstructions :=
              tail.candidateConstructions + work.candidateConstructions
            variableComparisonUnits :=
              tail.variableComparisonUnits + work.variableComparisonUnits
            formulaComparisonLiteralVisits :=
              tail.formulaComparisonLiteralVisits +
                work.formulaComparisonLiteralVisits
            historyComparisonDecisionVisits :=
              tail.historyComparisonDecisionVisits +
                work.historyComparisonDecisionVisits
            relationQueries := tail.relationQueries + work.relationQueries
            comparisonWork :=
              (measured.freshnessWork.add measured.relationWork).add tail.comparisonWork
            constructionWork := measured.constructionWork.add tail.constructionWork }

/-- Extraction and recorded exploration are executed as one stage run. -/
structure RecordedStageDiscoveryRun
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  extraction : CandidateExtractionRun
  outcome : RecordedDiscoveryOutcome state

def runRecordedDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    RecordedStageDiscoveryRun state :=
  let extraction := runCandidateExtraction state
  { extraction := extraction
    outcome :=
      exploreRecordedCandidates
        state
        extraction.candidates }

def stageRecordedDiscoveryRun (depth : Nat) :
    RecordedStageDiscoveryRun (constructStage depth).operationalRoot :=
  runRecordedDiscovery (constructStage depth).operationalRoot

structure GeneratedDiscoveryBundle {depth : Nat} (generation : CanonicalStageGeneration depth) where
  recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot
  recordedExact : recorded = stageRecordedDiscoveryRun (depth + 1)
  realizationWork : ComparisonWork

/-- Search seed read from the target actually produced by constitutive generation. -/
def generatedSearchSeed {depth : Nat}
    (generation : CanonicalStageGeneration depth) : Nat :=
  2 * positiveDepth generation.target

theorem generatedSearchSeed_exact {depth : Nat}
    (generation : CanonicalStageGeneration depth) :
    generatedSearchSeed generation =
      (constructStage (depth + 1)).searchIndex := by
  unfold generatedSearchSeed
  rw [generation.targetExact]
  rfl

/-- Realization and extraction only.  The operational root is retained as data
so the same root produced from the causal search seed is used by extraction and
the later exploration pass. -/
structure GeneratedExtractionBundle {depth : Nat}
    (generation : CanonicalStageGeneration depth) where
  operationalRoot :
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
  operationalRootExact :
    operationalRoot = (constructStage (depth + 1)).operationalRoot
  extraction : CandidateExtractionRun
  extractionExact : extraction =
    (stageRecordedDiscoveryRun (depth + 1)).extraction
  realizationWork : ComparisonWork

/-- Build the next operational root from an explicitly supplied causal seed,
then transport only its index to the canonical type.  The root itself is not
reconstructed after the transport. -/
def measuredGeneratedExtractionFromSeed {depth : Nat}
    (generation : CanonicalStageGeneration depth)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    GeneratedExtractionBundle generation :=
  let realized := constructMeasuredOperationalRoot searchSeed
  let seedExact :
      searchSeed = (constructStage (depth + 1)).searchIndex :=
    Eq.trans searchSeedExact (generatedSearchSeed_exact generation)
  let indexed := Eq.rec
    (motive := fun index _ =>
      GeneratedStructuralBranchContext (distinctGrowingDiscoveryFormula index))
    realized.value
    seedExact
  have rootExact :
      indexed = (constructStage (depth + 1)).operationalRoot := by
    cases seedExact
    dsimp only [indexed]
    exact Eq.trans realized.valueExact
      (constructStage (depth + 1)).operationalRootExact.symm
  let extraction := runCandidateExtraction indexed
  { operationalRoot := indexed
    operationalRootExact := rootExact
    extraction := extraction
    extractionExact := by
      dsimp only [extraction]
      rw [rootExact]
      rfl
    realizationWork := realized.work }

def measuredGeneratedExtraction {depth : Nat}
    (generation : CanonicalStageGeneration depth) :
    GeneratedExtractionBundle generation :=
  measuredGeneratedExtractionFromSeed generation
    (generatedSearchSeed generation) rfl

theorem measuredGeneratedExtractionFromSeed_eq {depth : Nat}
    (generation : CanonicalStageGeneration depth)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    measuredGeneratedExtractionFromSeed generation searchSeed searchSeedExact =
      measuredGeneratedExtraction generation := by
  cases searchSeedExact
  rfl

/-- Build the operational formula from the produced state before discovery. -/
def measuredGeneratedDiscovery {depth : Nat}
    (generation : CanonicalStageGeneration depth) :
    GeneratedDiscoveryBundle generation :=
  let realized := constructMeasuredOperationalRoot (2 * positiveDepth generation.target)
  let measured := runRecordedDiscovery realized.value
  let recorded := Eq.rec (motive := fun state _ => RecordedStageDiscoveryRun state)
    measured realized.valueExact
  let indexed := Eq.rec (motive := fun target _ =>
    RecordedStageDiscoveryRun (distinctGrowingDiscoveryRoot (2 * positiveDepth target)))
    recorded generation.targetExact
  { recorded := indexed
    recordedExact := by
      cases generation with
      | mk target targetExact generated =>
        cases targetExact
        dsimp only [indexed, recorded, measured]
        cases realized with
        | mk value same work => cases same; rfl
    realizationWork := realized.work }

theorem measuredGeneratedExtraction_realizationWork_eq
    {depth : Nat} (generation : CanonicalStageGeneration depth) :
    (measuredGeneratedExtraction generation).realizationWork =
      (measuredGeneratedDiscovery generation).realizationWork := by
  rfl

def generatedRecordedDiscoveryRun {depth : Nat}
    (generation : CanonicalStageGeneration depth) :
    RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot :=
  (measuredGeneratedDiscovery generation).recorded

theorem generatedRecordedDiscoveryRun_exact {depth : Nat}
    (generation : CanonicalStageGeneration depth) :
    generatedRecordedDiscoveryRun generation = stageRecordedDiscoveryRun (depth + 1) :=
  (measuredGeneratedDiscovery generation).recordedExact

/-- Literal visits of the extractor are exactly the literal nodes traversed. -/
theorem extractClauseCandidateRun_literalVisits_exact
    (clause : Clause) :
    (extractClauseCandidateRun clause).stats.literalVisits = clause.length := by
  induction clause with
  | nil => rfl
  | cons literal rest inductionHypothesis =>
      change
        (extractClauseCandidateRun rest).stats.literalVisits + 1 =
          rest.length + 1
      exact congrArg (fun visits => visits + 1) inductionHypothesis

theorem extractCnfCandidateRun_literalVisits_exact
    (formula : Cnf) :
    (extractCnfCandidateRun formula).stats.literalVisits =
      Cnf.literalCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      change
        (extractClauseCandidateRun clause).stats.literalVisits +
            (extractCnfCandidateRun rest).stats.literalVisits =
          clause.length + Cnf.literalCount rest
      rw [
        extractClauseCandidateRun_literalVisits_exact,
        inductionHypothesis
      ]

theorem runCandidateExtraction_literalVisits_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runCandidateExtraction state).stats.literalVisits =
      Cnf.literalCount state.context.formula :=
  extractCnfCandidateRun_literalVisits_exact state.context.formula

theorem extractClauseCandidateRun_length_exact (clause : Clause) :
    (extractClauseCandidateRun clause).candidates.length =
      (extractClauseCandidateRun clause).stats.candidatesEmitted := by
  induction clause with
  | nil => rfl
  | cons literal rest inductionHypothesis =>
      change (extractClauseCandidateRun rest).candidates.length + 1 =
        (extractClauseCandidateRun rest).stats.candidatesEmitted + 1
      rw [inductionHypothesis]

theorem listLengthAppend {alpha : Type} : ∀ left right : List alpha,
    (left ++ right).length = left.length + right.length
  | [], right => (Nat.zero_add right.length).symm
  | head :: tail, right => by
      change (tail ++ right).length + 1 = (tail.length + 1) + right.length
      rw [listLengthAppend tail right]
      calc
        (tail.length + right.length) + 1 =
            tail.length + (right.length + 1) := Nat.add_assoc _ _ _
        _ = tail.length + (1 + right.length) :=
          congrArg (Nat.add tail.length) (Nat.add_comm right.length 1)
        _ = (tail.length + 1) + right.length := (Nat.add_assoc _ _ _).symm

theorem extractCnfCandidateRun_length_exact (formula : Cnf) :
    (extractCnfCandidateRun formula).candidates.length =
      (extractCnfCandidateRun formula).stats.candidatesEmitted := by
  induction formula with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      change
        ((extractClauseCandidateRun clause).candidates ++
          (extractCnfCandidateRun rest).candidates).length =
        (extractClauseCandidateRun clause).stats.candidatesEmitted +
          (extractCnfCandidateRun rest).stats.candidatesEmitted
      rw [listLengthAppend, extractClauseCandidateRun_length_exact,
        inductionHypothesis]

theorem runCandidateExtraction_length_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runCandidateExtraction state).candidates.length =
      (runCandidateExtraction state).stats.candidatesEmitted :=
  extractCnfCandidateRun_length_exact state.context.formula

/-- Recorded exploration returns the same discovery as the reference recursion. -/
theorem exploreRecordedCandidates_discovered
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidates : List Var) :
    (exploreRecordedCandidates state candidates).discovered? =
      (exploreStructuralCandidates state candidates).discovered? := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [exploreRecordedCandidates, exploreStructuralCandidates, ← tryMeasuredCandidate_exact]
      unfold MeasuredCandidateRun.result
      cases found : (tryMeasuredCandidate state candidate).produced? with
      | none =>
          exact inductionHypothesis
      | some candidateDiscovery =>
          rfl

/-- Recorded attempts equal the reference executable charge. -/
theorem exploreRecordedCandidates_attempts
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidates : List Var) :
    (exploreRecordedCandidates state candidates).attempts =
      (exploreStructuralCandidates state candidates).attempts := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [exploreRecordedCandidates, exploreStructuralCandidates, ← tryMeasuredCandidate_exact]
      unfold MeasuredCandidateRun.result
      cases found : (tryMeasuredCandidate state candidate).produced? with
      | none =>
          exact congrArg (fun value => value + 1) inductionHypothesis
      | some candidateDiscovery =>
          rfl

/-- The tested list and the attempt counter are produced by the same recursion. -/
theorem exploreRecordedCandidates_tested_length
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidates : List Var) :
    (exploreRecordedCandidates state candidates).testedCandidates.length =
      (exploreRecordedCandidates state candidates).attempts := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      unfold exploreRecordedCandidates
      dsimp only
      split
      · rfl
      · change
          (exploreRecordedCandidates state rest).testedCandidates.length + 1 =
            (exploreRecordedCandidates state rest).attempts + 1
        exact congrArg (fun value => value + 1) inductionHypothesis

/--
Closed forms for the legacy structural surface accumulated by the candidate
recursion. These equalities do not bound or identify the measured comparator
work and do not certify complete end-to-end accounting.
-/
theorem exploreRecordedCandidates_work_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidates : List Var) :
    let run := exploreRecordedCandidates state candidates
    run.candidateConstructions = 2 * run.attempts ∧
      run.variableComparisonUnits =
        (Cnf.literalCount state.context.formula +
          (state.context.decisions.length + 1)) * run.attempts ∧
      run.formulaComparisonLiteralVisits =
        Cnf.literalCount state.context.formula * run.attempts ∧
      run.historyComparisonDecisionVisits =
        (state.context.decisions.length + 1) * run.attempts ∧
      run.relationQueries = run.attempts := by
  have constructions :
      ∀ xs : List Var,
        (exploreRecordedCandidates state xs).candidateConstructions =
          2 * (exploreRecordedCandidates state xs).attempts := by
    intro xs
    induction xs with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        unfold exploreRecordedCandidates
        dsimp only
        split
        · rfl
        · change
            (exploreRecordedCandidates state rest).candidateConstructions + 2 =
              2 * ((exploreRecordedCandidates state rest).attempts + 1)
          rw [inductionHypothesis]
          rfl
  have variableUnits :
      ∀ xs : List Var,
        (exploreRecordedCandidates state xs).variableComparisonUnits =
          (Cnf.literalCount state.context.formula +
            (state.context.decisions.length + 1)) *
              (exploreRecordedCandidates state xs).attempts := by
    intro xs
    induction xs with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        unfold exploreRecordedCandidates
        dsimp only
        split
        · change
            Cnf.literalCount state.context.formula +
                (state.context.decisions.length + 1) =
              (Cnf.literalCount state.context.formula +
                (state.context.decisions.length + 1)) * 1
          exact
            (Nat.mul_one
              (Cnf.literalCount state.context.formula +
                (state.context.decisions.length + 1))).symm
        · change
            (exploreRecordedCandidates state rest).variableComparisonUnits +
                (Cnf.literalCount state.context.formula +
                  (state.context.decisions.length + 1)) =
              (Cnf.literalCount state.context.formula +
                (state.context.decisions.length + 1)) *
                  ((exploreRecordedCandidates state rest).attempts + 1)
          rw [inductionHypothesis]
          rfl
  have formulaVisits :
      ∀ xs : List Var,
        (exploreRecordedCandidates state xs).formulaComparisonLiteralVisits =
          Cnf.literalCount state.context.formula *
            (exploreRecordedCandidates state xs).attempts := by
    intro xs
    induction xs with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        unfold exploreRecordedCandidates
        dsimp only
        split
        · change
            Cnf.literalCount state.context.formula =
              Cnf.literalCount state.context.formula * 1
          exact
            (Nat.mul_one
              (Cnf.literalCount state.context.formula)).symm
        · change
            (exploreRecordedCandidates state rest).formulaComparisonLiteralVisits +
                Cnf.literalCount state.context.formula =
              Cnf.literalCount state.context.formula *
                ((exploreRecordedCandidates state rest).attempts + 1)
          rw [inductionHypothesis]
          rfl
  have historyVisits :
      ∀ xs : List Var,
        (exploreRecordedCandidates state xs).historyComparisonDecisionVisits =
          (state.context.decisions.length + 1) *
            (exploreRecordedCandidates state xs).attempts := by
    intro xs
    induction xs with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        unfold exploreRecordedCandidates
        dsimp only
        split
        · change
            state.context.decisions.length + 1 =
              (state.context.decisions.length + 1) * 1
          exact
            (Nat.mul_one
              (state.context.decisions.length + 1)).symm
        · change
            (exploreRecordedCandidates state rest).historyComparisonDecisionVisits +
                (state.context.decisions.length + 1) =
              (state.context.decisions.length + 1) *
                ((exploreRecordedCandidates state rest).attempts + 1)
          rw [inductionHypothesis]
          rfl
  have queries :
      ∀ xs : List Var,
        (exploreRecordedCandidates state xs).relationQueries =
          (exploreRecordedCandidates state xs).attempts := by
    intro xs
    induction xs with
    | nil => rfl
    | cons candidate rest inductionHypothesis =>
        unfold exploreRecordedCandidates
        dsimp only
        split
        · rfl
        · change
            (exploreRecordedCandidates state rest).relationQueries + 1 =
              (exploreRecordedCandidates state rest).attempts + 1
          exact congrArg (fun count => count + 1) inductionHypothesis
  exact
    ⟨constructions candidates,
      variableUnits candidates,
      formulaVisits candidates,
      historyVisits candidates,
      queries candidates⟩

theorem stageRecordedDiscovery_tested_length (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.testedCandidates.length =
      (stageRecordedDiscoveryRun depth).outcome.attempts :=
  exploreRecordedCandidates_tested_length
    (constructStage depth).operationalRoot
    (runCandidateExtraction
      (constructStage depth).operationalRoot).candidates

theorem stageRecordedDiscovery_work_exact (depth : Nat) :
    let run := stageRecordedDiscoveryRun depth
    run.outcome.candidateConstructions = 2 * run.outcome.attempts ∧
      run.outcome.variableComparisonUnits =
        (Cnf.literalCount
              (constructStage depth).operationalRoot.context.formula +
            ((constructStage depth).operationalRoot.context.decisions.length + 1)) *
          run.outcome.attempts ∧
      run.outcome.formulaComparisonLiteralVisits =
        Cnf.literalCount
            (constructStage depth).operationalRoot.context.formula *
          run.outcome.attempts ∧
      run.outcome.historyComparisonDecisionVisits =
        ((constructStage depth).operationalRoot.context.decisions.length + 1) *
          run.outcome.attempts ∧
      run.outcome.relationQueries = run.outcome.attempts :=
  exploreRecordedCandidates_work_exact
    (constructStage depth).operationalRoot
    (runCandidateExtraction
      (constructStage depth).operationalRoot).candidates

/-- Exact extraction order inherited from the growing discovery family. -/
theorem stageExtractedCandidates_exact (depth : Nat) :
    stageExtractedCandidates depth =
      distinctDecoyVariables ((constructStage depth).searchIndex + 1) ++
        [ growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex,
          growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex ] := by
  exact
    distinctGrowingDiscovery_candidates
      (constructStage depth).searchIndex

/-- Extraction work is produced by the recursive extraction run. -/
theorem stageExtractionStats_exact (depth : Nat) :
    (stageDiscoveryRun depth).extraction.stats.clauseVisits = 3 /\
      (stageDiscoveryRun depth).extraction.stats.literalVisits =
        (constructStage depth).searchIndex + 5 := by
  exact
    distinctGrowingDiscovery_extraction_stats
      (constructStage depth).searchIndex

theorem stageRecordedExtractionStats_exact (depth : Nat) :
    (stageRecordedDiscoveryRun depth).extraction.stats.clauseVisits = 3 ∧
      (stageRecordedDiscoveryRun depth).extraction.stats.literalVisits =
        (constructStage depth).searchIndex + 5 := by
  exact
    distinctGrowingDiscovery_extraction_stats
      (constructStage depth).searchIndex

theorem stageOperationalRoot_literalCount_exact (depth : Nat) :
    Cnf.literalCount
        (constructStage depth).operationalRoot.context.formula =
      (constructStage depth).searchIndex + 5 := by
  calc
    Cnf.literalCount
        (constructStage depth).operationalRoot.context.formula =
        (runCandidateExtraction
          (constructStage depth).operationalRoot).stats.literalVisits :=
      (runCandidateExtraction_literalVisits_exact
        (constructStage depth).operationalRoot).symm
    _ = (constructStage depth).searchIndex + 5 :=
      (stageRecordedExtractionStats_exact depth).2

theorem stageOperationalRoot_historyLength (depth : Nat) :
    (constructStage depth).operationalRoot.context.decisions.length = 0 :=
  rfl

/--
The executable run returns a discovered relation after rejecting the complete
constitutively indexed decoy prefix.
-/
theorem stageDiscovery_found_after_exact_attempts (depth : Nat) :
    ∃ discovery,
      (stageDiscoveryRun depth).outcome.discovered? = some discovery /\
      discovery.var =
        growingDiscoverySplitVar (constructStage depth).searchIndex /\
      (stageDiscoveryRun depth).outcome.attempts =
        (constructStage depth).searchIndex + 2 := by
  exact
    distinctGrowingDiscovery_found_after_exact_attempts
      (constructStage depth).searchIndex

theorem stageRecordedDiscovery_found_after_exact_attempts (depth : Nat) :
    ∃ discovery,
      (stageRecordedDiscoveryRun depth).outcome.discovered? = some discovery ∧
      discovery.var =
        growingDiscoverySplitVar (constructStage depth).searchIndex ∧
      (stageRecordedDiscoveryRun depth).outcome.attempts =
        (constructStage depth).searchIndex + 2 := by
  rcases stageDiscovery_found_after_exact_attempts depth with
    ⟨discovery, found, selected, attempts⟩
  refine ⟨discovery, ?_, selected, ?_⟩
  · exact
      Eq.trans
        (exploreRecordedCandidates_discovered
          (constructStage depth).operationalRoot
          (runCandidateExtraction
            (constructStage depth).operationalRoot).candidates)
        found
  · exact
      Eq.trans
        (exploreRecordedCandidates_attempts
          (constructStage depth).operationalRoot
          (runCandidateExtraction
            (constructStage depth).operationalRoot).candidates)
        attempts

theorem stageRecordedDiscovery_attempts_exact (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.attempts =
      (constructStage depth).searchIndex + 2 := by
  rcases stageRecordedDiscovery_found_after_exact_attempts depth with
    ⟨_discovery, _found, _selected, attempts⟩
  exact attempts

/-- Exact, run-derived comparison and construction work of the concrete stage. -/
theorem stageRecordedDiscovery_detailedWork_exact (depth : Nat) :
    let run := stageRecordedDiscoveryRun depth
    run.outcome.candidateConstructions =
        2 * ((constructStage depth).searchIndex + 2) ∧
      run.outcome.variableComparisonUnits =
        ((constructStage depth).searchIndex + 6) *
          ((constructStage depth).searchIndex + 2) ∧
      run.outcome.formulaComparisonLiteralVisits =
        ((constructStage depth).searchIndex + 5) *
          ((constructStage depth).searchIndex + 2) ∧
      run.outcome.historyComparisonDecisionVisits =
        (constructStage depth).searchIndex + 2 ∧
      run.outcome.relationQueries =
        (constructStage depth).searchIndex + 2 := by
  have work := stageRecordedDiscovery_work_exact depth
  dsimp only at work ⊢
  rw [
    stageRecordedDiscovery_attempts_exact,
    stageOperationalRoot_literalCount_exact,
    stageOperationalRoot_historyLength
  ] at work
  simpa [Nat.add_assoc] using work

theorem stageRecordedDiscovery_ne_none (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.discovered? ≠ none := by
  rcases stageRecordedDiscovery_found_after_exact_attempts depth with
    ⟨discovery, found, _selected, _attempts⟩
  rw [found]
  intro impossible
  cases impossible

theorem stageRecordedDiscovery_attempts_strict (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.attempts <
      (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts := by
  rw [
    stageRecordedDiscovery_attempts_exact,
    stageRecordedDiscovery_attempts_exact,
    generateCanonicalStage_searchIndex_advances
  ]
  exact
    Nat.lt_trans
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 2))
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 2 + 1))

/-- Discovery cannot be replaced by a constant failure on a canonical stage. -/
theorem stageDiscovery_ne_none (depth : Nat) :
    (stageDiscoveryRun depth).outcome.discovered? ≠ none := by
  rcases stageDiscovery_found_after_exact_attempts depth with
    ⟨discovery, found, _selected, _attempts⟩
  rw [found]
  intro impossible
  cases impossible

/-- The exact number of attempts is determined by the executed run. -/
theorem stageDiscovery_attempts_exact (depth : Nat) :
    (stageDiscoveryRun depth).outcome.attempts =
      (constructStage depth).searchIndex + 2 := by
  rcases stageDiscovery_found_after_exact_attempts depth with
    ⟨_discovery, _found, _selected, attempts⟩
  exact attempts

/-- Successive actual constitutive stages induce strictly growing discovery work. -/
theorem stageDiscovery_attempts_strict (depth : Nat) :
    (stageDiscoveryRun depth).outcome.attempts <
      (stageDiscoveryRun (depth + 1)).outcome.attempts := by
  rw [stageDiscovery_attempts_exact, stageDiscovery_attempts_exact]
  rw [generateCanonicalStage_searchIndex_advances]
  exact
    Nat.lt_trans
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 2))
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 2 + 1))

/-- Literal traversal, like candidate attempts, grows with constituted depth. -/
theorem stageExtractionLiteralVisits_strict (depth : Nat) :
    (stageDiscoveryRun depth).extraction.stats.literalVisits <
      (stageDiscoveryRun (depth + 1)).extraction.stats.literalVisits := by
  rw [
    (stageExtractionStats_exact depth).2,
    (stageExtractionStats_exact (depth + 1)).2,
    generateCanonicalStage_searchIndex_advances
  ]
  exact
    Nat.lt_trans
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 5))
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 5 + 1))

theorem stageRecordedExtractionLiteralVisits_strict (depth : Nat) :
    (stageRecordedDiscoveryRun depth).extraction.stats.literalVisits <
      (stageRecordedDiscoveryRun (depth + 1)).extraction.stats.literalVisits := by
  rw [
    (stageRecordedExtractionStats_exact depth).2,
    (stageRecordedExtractionStats_exact (depth + 1)).2,
    generateCanonicalStage_searchIndex_advances
  ]
  exact
    Nat.lt_trans
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 5))
      (Nat.lt_succ_self ((constructStage depth).searchIndex + 5 + 1))

/-- The charged structural formula-comparison surface grows strictly. -/
theorem stageRecordedFormulaComparisonVisits_strict (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.formulaComparisonLiteralVisits <
      (stageRecordedDiscoveryRun
        (depth + 1)).outcome.formulaComparisonLiteralVisits := by
  rw [
    (stageRecordedDiscovery_detailedWork_exact depth).2.2.1,
    (stageRecordedDiscovery_detailedWork_exact (depth + 1)).2.2.1,
    generateCanonicalStage_searchIndex_advances
  ]
  let index := (constructStage depth).searchIndex
  have rightStrict : index + 2 < index + 2 + 2 :=
    Nat.lt_trans
      (Nat.lt_succ_self (index + 2))
      (Nat.lt_succ_self (index + 2 + 1))
  have leftPositive : 0 < index + 5 :=
    Nat.lt_of_lt_of_le
      (Nat.zero_lt_succ index)
      (Nat.le_add_right (index + 1) 4)
  have first :
      (index + 5) * (index + 2) <
        (index + 5) * (index + 2 + 2) :=
    Nat.mul_lt_mul_of_pos_left rightStrict leftPositive
  have leftLe : index + 5 ≤ index + 2 + 5 :=
    Nat.add_le_add_right (Nat.le_add_right index 2) 5
  have second :
      (index + 5) * (index + 2 + 2) ≤
        (index + 2 + 5) * (index + 2 + 2) :=
    Nat.mul_le_mul_right (index + 2 + 2) leftLe
  exact Nat.lt_of_lt_of_le first second

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedSearchSeed
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedSearchSeed_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredGeneratedExtractionFromSeed
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredGeneratedExtractionFromSeed_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredGeneratedDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.runRecordedDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedRecordedDiscoveryRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedRecordedDiscoveryRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscoveryRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.exploreRecordedCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.exploreRecordedCandidates_work_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscoveryRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscovery_found_after_exact_attempts
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscovery_tested_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscovery_attempts_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscovery_ne_none
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageExtractionStats_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedExtractionStats_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageOperationalRoot_literalCount_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedDiscovery_detailedWork_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscovery_found_after_exact_attempts
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscovery_attempts_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageExtractionLiteralVisits_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedExtractionLiteralVisits_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRecordedFormulaComparisonVisits_strict
/- AXIOM_AUDIT_END -/
