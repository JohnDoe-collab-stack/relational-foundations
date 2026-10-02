import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredComparisonBounds
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredDiscovery
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.EndogenousDiscovery
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialHistory
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryExecution

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

def unaryDecisionSize (decision : StructuralBranchDecision) : Nat := decision.var + 3
def unaryHistorySize := unaryListSize unaryDecisionSize

theorem compareMeasuredBool_work (left right : Bool) :
    (compareMeasuredBool left right).work.total = 1 := by cases left <;> cases right <;> rfl

theorem compareMeasuredDecision_bound (left right : StructuralBranchDecision) :
    (compareMeasuredDecision left right).work.total ≤ unaryDecisionSize left := by
  unfold compareMeasuredDecision
  dsimp only
  split
  · change (compareUnary left.var right.var).work.visit.total ≤ left.var + 3
    rw [ComparisonWork.total_visit]
    exact Nat.le_trans (Nat.add_le_add_right (compareUnary_total_le _ _) 1) (Nat.le_succ _)
  · change ((compareUnary left.var right.var).work.add
      (compareMeasuredBool left.value right.value).work).visit.total ≤ left.var + 3
    rw [ComparisonWork.total_visit, ComparisonWork.total_add, compareMeasuredBool_work]
    exact Nat.add_le_add_right (Nat.add_le_add_right (compareUnary_total_le _ _) 1) 1

theorem compareMeasuredHistory_bound (left right : List StructuralBranchDecision) :
    (compareMeasuredHistory left right).work.total ≤ unaryHistorySize left :=
  compareMeasuredList_bound _ _ compareMeasuredDecision_bound left right

theorem flipMeasuredDecision_bound (selected : Var) (decision : StructuralBranchDecision) :
    (flipMeasuredDecision selected decision).work.total ≤ unaryDecisionSize decision := by
  unfold flipMeasuredDecision
  dsimp only
  split <;>
    change (compareUnary decision.var selected).work.visit.total ≤ decision.var + 3 <;>
    rw [ComparisonWork.total_visit] <;>
    exact Nat.le_trans (Nat.add_le_add_right (compareUnary_total_le _ _) 1) (Nat.le_succ _)

theorem flipMeasuredHistory_bound (selected : Var) (history : List StructuralBranchDecision) :
    (flipMeasuredHistory selected history).work.total ≤ unaryHistorySize history := by
  induction history with
  | nil => exact Nat.le_refl 1
  | cons decision rest ih =>
    change ((flipMeasuredDecision selected decision).work.add
      (flipMeasuredHistory selected rest).work).visit.total ≤ _
    rw [ComparisonWork.total_visit, ComparisonWork.total_add]
    exact Nat.add_le_add_right (Nat.add_le_add (flipMeasuredDecision_bound _ _) ih) 1

theorem branchResidual_unarySize_le (formula : Cnf) (selected : Var) (value : Bool) :
    unaryCnfSize (branchResidual formula selected value) ≤ unaryCnfSize formula := by
  induction formula with
  | nil => exact Nat.le_refl 1
  | cons clause rest ih =>
    cases hit : Clause.containsLiteral (Literal.forValue selected value) clause with
    | true =>
      rw [branchResidual_cons_hit clause rest selected value hit]
      exact Nat.le_trans ih (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _))
    | false =>
      rw [branchResidual_cons_miss clause rest selected value hit]
      exact Nat.add_le_add_right (Nat.add_le_add_left ih _) 1

/-- No primitive relation query is charged as constant formula/history work. -/
theorem searchMeasuredRelation_bound {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) :
    (searchMeasuredRelation selected source target).work.total ≤
      ((unaryCnfSize source.context.formula + unaryCnfSize target.context.formula) +
        unaryHistorySize source.context.decisions) + unaryHistorySize target.context.decisions := by
  unfold searchMeasuredRelation
  dsimp only
  split
  · change ((((flipMeasuredCnf selected source.context.formula).work.add
      (compareMeasuredCnf target.context.formula _).work).add .zero).add .zero).total ≤ _
    rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add]
    change (_ + 0) + 0 ≤ _
    rw [Nat.add_zero]
    exact Nat.le_trans
      (Nat.add_le_add (flipMeasuredCnf_bound _ _) (compareMeasuredCnf_bound _ _))
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  · split <;>
      change ((((flipMeasuredCnf selected source.context.formula).work.add
        (compareMeasuredCnf target.context.formula _).work).add
        (flipMeasuredHistory selected source.context.decisions).work).add
        (compareMeasuredHistory target.context.decisions _).work).total ≤ _ <;>
      rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add] <;>
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (flipMeasuredCnf_bound _ _) (compareMeasuredCnf_bound _ _))
          (flipMeasuredHistory_bound _ _))
        (compareMeasuredHistory_bound _ _)

theorem searchMeasuredRelationFromData_bound {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) :
    (searchMeasuredRelationFromData selected left right).work.total ≤
      ((unaryCnfSize source.context.formula + unaryCnfSize target.context.formula) +
        unaryHistorySize source.context.decisions) + unaryHistorySize target.context.decisions := by
  cases left with
  | mk source exactSource sourceWork =>
    cases exactSource
    cases right with
    | mk target exactTarget targetWork =>
      cases exactTarget
      exact searchMeasuredRelation_bound _ _ _

def rootCandidateWorkBound (formula : Cnf) (candidate : Var) : Nat :=
  (1 + ((unaryCnfSize formula + 1) + (unaryCnfSize formula + 1))) +
    (((unaryCnfSize formula + unaryCnfSize formula) + (candidate + 5)) + (candidate + 5))

/-- Bound all executed subprograms of an attempt, including the constructed children. -/
theorem rootCandidate_measured_bound (formula : Cnf) (candidate : Var) :
    let tried := tryMeasuredCandidate (GeneratedStructuralBranchContext.root formula) candidate
    ((tried.freshnessWork.add tried.constructionWork).add tried.relationWork).total ≤
      rootCandidateWorkBound formula candidate := by
  let state := GeneratedStructuralBranchContext.root formula
  let fresh : StructuralDecisionsAvoid candidate state.context.decisions := True.intro
  let left := constructMeasuredChild state candidate false fresh
  let right := constructMeasuredChild state candidate true fresh
  have relationBound : (searchMeasuredRelationFromData candidate left right).work.total ≤
      ((unaryCnfSize formula + unaryCnfSize formula) + (candidate + 5)) + (candidate + 5) := by
    have raw := searchMeasuredRelationFromData_bound candidate left right
    have sizes := Nat.add_le_add (branchResidual_unarySize_le formula candidate false)
      (branchResidual_unarySize_le formula candidate true)
    exact Nat.le_trans raw (Nat.add_le_add_right (Nat.add_le_add_right sizes _) _)
  have constructionBound : (left.work.add right.work).total ≤
      (unaryCnfSize formula + 1) + (unaryCnfSize formula + 1) := by
    rw [ComparisonWork.total_add]
    exact Nat.add_le_add (constructMeasuredChild_bound _ _ _ _) (constructMeasuredChild_bound _ _ _ _)
  dsimp only
  unfold tryMeasuredCandidate
  dsimp only [GeneratedStructuralBranchContext.root, structuralRootContext, checkMeasuredFreshness]
  split <;>
    change ((ComparisonWork.add ⟨1, 0⟩ (left.work.add right.work)).add
      (searchMeasuredRelationFromData candidate left right).work).total ≤ _ <;>
    rw [ComparisonWork.total_add, ComparisonWork.total_add] <;>
    exact Nat.add_le_add (Nat.add_le_add_left constructionBound 1) relationBound

theorem rootCandidateWorkBound_mono (formula : Cnf) {first second : Var}
    (before : first ≤ second) : rootCandidateWorkBound formula first ≤ rootCandidateWorkBound formula second :=
  Nat.add_le_add_left
    (Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_right before 5) _)
      (Nat.add_le_add_right before 5)) _

/-- The recursive explorer cannot spend more than one bounded attempt per candidate. -/
theorem recordedExploration_measured_bound (formula : Cnf) (candidates : List Var) (largest : Var)
    (bounded : ∀ candidate, candidate ∈ candidates → candidate ≤ largest) :
    let outcome := exploreRecordedCandidates (GeneratedStructuralBranchContext.root formula) candidates
    (outcome.comparisonWork.add outcome.constructionWork).total ≤
      candidates.length * rootCandidateWorkBound formula largest := by
  induction candidates with
  | nil => rw [List.length_nil, Nat.zero_mul]; exact Nat.le_refl 0
  | cons candidate rest ih =>
    let tried := tryMeasuredCandidate (GeneratedStructuralBranchContext.root formula) candidate
    have attempt : ((tried.freshnessWork.add tried.relationWork).add tried.constructionWork).total ≤
        rootCandidateWorkBound formula largest := by
      have raw := rootCandidate_measured_bound formula candidate
      dsimp only at raw
      rw [ComparisonWork.total_add, ComparisonWork.total_add] at raw ⊢
      have reordered : (tried.freshnessWork.total + tried.relationWork.total) + tried.constructionWork.total =
          (tried.freshnessWork.total + tried.constructionWork.total) + tried.relationWork.total := by
        rw [Nat.add_assoc, Nat.add_comm tried.relationWork.total tried.constructionWork.total, ← Nat.add_assoc]
      rw [reordered]
      exact Nat.le_trans raw (rootCandidateWorkBound_mono formula (bounded _ List.mem_cons_self))
    have tailBound := ih (fun value member => bounded value (List.mem_cons_of_mem candidate member))
    dsimp only
    rw [exploreRecordedCandidates]
    cases found : tried.produced? with
    | some produced =>
      change ((tried.freshnessWork.add tried.relationWork).add tried.constructionWork).total ≤ _
      rw [List.length_cons, Nat.succ_mul]
      exact Nat.le_trans attempt (Nat.le_add_left _ _)
    | none =>
      change (((tried.freshnessWork.add tried.relationWork).add
        (exploreRecordedCandidates _ rest).comparisonWork).add
        (tried.constructionWork.add (exploreRecordedCandidates _ rest).constructionWork)).total ≤ _
      rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add,
        ComparisonWork.total_add]
      rw [Nat.add_add_add_comm]
      have both := Nat.add_le_add attempt tailBound
      rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add] at both
      rw [List.length_cons, Nat.succ_mul]
      exact Nat.le_trans both (Nat.le_of_eq (Nat.add_comm _ _))

theorem candidateVariable_unarySize (literal : Literal) :
    literal.candidateVariable ≤ unaryLiteralSize literal := by
  cases literal <;> exact Nat.le_add_right _ 2

theorem clauseCandidates_size (clause : Clause) :
    clause.candidateVariables.length ≤ unaryClauseSize clause := by
  induction clause with
  | nil => exact Nat.zero_le 1
  | cons literal rest ih =>
    exact Nat.add_le_add_right (Nat.le_trans ih (Nat.le_add_left _ _)) 1

theorem clauseCandidate_label_bound (clause : Clause) (candidate : Var)
    (member : candidate ∈ clause.candidateVariables) : candidate ≤ unaryClauseSize clause := by
  induction clause with
  | nil => cases member
  | cons literal rest ih =>
    cases member with
    | head =>
      exact Nat.le_trans (candidateVariable_unarySize literal)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ 1))
    | tail _ tail =>
      exact Nat.le_trans (ih tail)
        (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ 1))

theorem append_length_constructive {α : Type} (first second : List α) :
    (first ++ second).length = first.length + second.length := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons head rest ih =>
    change (rest ++ second).length + 1 = (rest.length + 1) + second.length
    rw [ih, Nat.add_assoc, Nat.add_comm second.length 1, ← Nat.add_assoc]

theorem cnfCandidates_size (formula : Cnf) :
    formula.candidateVariables.length ≤ unaryCnfSize formula := by
  induction formula with
  | nil => exact Nat.zero_le 1
  | cons clause rest ih =>
    change (clause.candidateVariables ++ Cnf.candidateVariables rest).length ≤ _
    rw [append_length_constructive]
    exact Nat.le_trans (Nat.add_le_add (clauseCandidates_size clause) ih) (Nat.le_add_right _ 1)

theorem member_append_cases {α : Type} (first second : List α) (value : α)
    (member : value ∈ first ++ second) : value ∈ first ∨ value ∈ second := by
  induction first with
  | nil => exact Or.inr member
  | cons head rest ih =>
    cases member with
    | head => exact Or.inl (List.Mem.head rest)
    | tail _ tail =>
      cases ih tail with
      | inl left => exact Or.inl (List.Mem.tail head left)
      | inr right => exact Or.inr right

theorem cnfCandidate_label_bound (formula : Cnf) (candidate : Var)
    (member : candidate ∈ formula.candidateVariables) : candidate ≤ unaryCnfSize formula := by
  induction formula with
  | nil => cases member
  | cons clause rest ih =>
    cases member_append_cases _ _ candidate member with
    | inl head =>
      exact Nat.le_trans (clauseCandidate_label_bound clause candidate head)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ 1))
    | inr tail =>
      exact Nat.le_trans (ih tail)
        (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ 1))

/-- A closed quadratic envelope in the unary encoding of the actual CNF.
This bounds measured comparison and child construction, not the whole driver. -/
theorem rootDiscovery_measured_input_bound (formula : Cnf) :
    let run := runRecordedDiscovery (GeneratedStructuralBranchContext.root formula)
    (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      unaryCnfSize formula * rootCandidateWorkBound formula (unaryCnfSize formula) := by
  change ((exploreRecordedCandidates _ (extractCnfCandidateRun formula).candidates).comparisonWork.add
    (exploreRecordedCandidates _ (extractCnfCandidateRun formula).candidates).constructionWork).total ≤ _
  rw [extractCnfCandidateRun_candidates]
  exact Nat.le_trans
    (recordedExploration_measured_bound formula formula.candidateVariables (unaryCnfSize formula)
      (cnfCandidate_label_bound formula))
    (Nat.mul_le_mul_right _ (cnfCandidates_size formula))

theorem clauseExtraction_visits_bound (clause : Clause) :
    (extractClauseCandidateRun clause).stats.literalVisits ≤ unaryClauseSize clause := by
  induction clause with
  | nil => exact Nat.zero_le 1
  | cons literal rest ih =>
    exact Nat.add_le_add_right (Nat.le_trans ih (Nat.le_add_left _ _)) 1

/-- Counts emitted by extraction itself, including visits of empty clauses. -/
theorem cnfExtraction_visits_bound (formula : Cnf) :
    (extractCnfCandidateRun formula).stats.clauseVisits +
      (extractCnfCandidateRun formula).stats.literalVisits ≤ unaryCnfSize formula := by
  induction formula with
  | nil => exact Nat.zero_le 1
  | cons clause rest ih =>
    change ((extractCnfCandidateRun rest).stats.clauseVisits + 1) +
      ((extractClauseCandidateRun clause).stats.literalVisits +
        (extractCnfCandidateRun rest).stats.literalVisits) ≤ _
    have regroup : ∀ a b c : Nat, (a + 1) + (b + c) = (b + (a + c)) + 1 := by
      intro a b c
      rw [Nat.add_add_add_comm, Nat.add_comm a b, Nat.add_assoc b a,
        Nat.add_comm 1 c, ← Nat.add_assoc a c 1, ← Nat.add_assoc b (a + c) 1]
    rw [regroup]
    exact Nat.add_le_add_right (Nat.add_le_add (clauseExtraction_visits_bound clause) ih) 1

/-- Extraction visits plus measured exploration, without claiming driver overhead. -/
theorem rootDiscovery_with_extraction_bound (formula : Cnf) :
    let run := runRecordedDiscovery (GeneratedStructuralBranchContext.root formula)
    (run.extraction.stats.clauseVisits + run.extraction.stats.literalVisits) +
      (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      unaryCnfSize formula +
        unaryCnfSize formula * rootCandidateWorkBound formula (unaryCnfSize formula) :=
  Nat.add_le_add (cnfExtraction_visits_bound formula) (rootDiscovery_measured_input_bound formula)

/-- A polynomial expression in the size of the data actually searched. -/
def discoveryWorkEnvelope (size : Nat) : Nat :=
  size + size * ((1 + ((size + 1) + (size + 1))) +
    (((size + size) + (size + 5)) + (size + 5)))

theorem discoveryWorkEnvelope_mono {first second : Nat} (before : first ≤ second) :
    discoveryWorkEnvelope first ≤ discoveryWorkEnvelope second := by
  exact Nat.add_le_add before (Nat.mul_le_mul before
    (Nat.add_le_add
      (Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right before 1)
        (Nat.add_le_add_right before 1)) 1)
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add before before)
        (Nat.add_le_add_right before 5)) (Nat.add_le_add_right before 5))))

theorem distinctDecoy_unarySize_bound (count largest : Nat) (bounded : count ≤ largest) :
    unaryClauseSize (distinctDecoyClause count) ≤ count * (largest + 3) + 1 := by
  induction count with
  | zero => rw [Nat.zero_mul]; exact Nat.le_refl 1
  | succ count ih =>
    have before := Nat.le_trans (Nat.le_succ count) bounded
    have headBound := Nat.add_le_add_right before 3
    have tailBound := ih before
    change (count + 2) + unaryClauseSize (distinctDecoyClause count) + 1 ≤ _
    have both := Nat.add_le_add headBound tailBound
    calc
      _ = (count + 3) + unaryClauseSize (distinctDecoyClause count) := by
        rw [Nat.add_assoc (count + 2),
          Nat.add_comm (unaryClauseSize (distinctDecoyClause count)) 1,
          ← Nat.add_assoc (count + 2) 1]
      _ ≤ (largest + 3) + (count * (largest + 3) + 1) := both
      _ = (count + 1) * (largest + 3) + 1 := by
        rw [Nat.succ_mul, Nat.add_comm (count * (largest + 3)) (largest + 3)]
        exact (Nat.add_assoc _ _ _).symm

def growingFormulaSizeEnvelope (index : Nat) : Nat :=
  ((index + 1) * ((index + 1) + 3) + 1) +
    unaryCnfSize (symmetricBlockFamily (growingDiscoverySplitVar index)
      (growingDiscoveryAnchorVar index) []) + 1

theorem growingFormula_unarySize_bound (index : Nat) :
    unaryCnfSize (distinctGrowingDiscoveryFormula index) ≤ growingFormulaSizeEnvelope index :=
  Nat.add_le_add_right (Nat.add_le_add_right
    (distinctDecoy_unarySize_bound (index + 1) (index + 1) (Nat.le_refl _)) _) 1

/-- The concrete stage uses the envelope of its constituted search index. -/
theorem stageDiscovery_measured_bound (depth : Nat) :
    let run := stageRecordedDiscoveryRun depth
    (run.extraction.stats.clauseVisits + run.extraction.stats.literalVisits) +
      (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      discoveryWorkEnvelope (growingFormulaSizeEnvelope (constitutedSearchIndex depth)) :=
  Nat.le_trans (rootDiscovery_with_extraction_bound
    (distinctGrowingDiscoveryFormula (constitutedSearchIndex depth)))
    (discoveryWorkEnvelope_mono (growingFormula_unarySize_bound _))

theorem growingFormulaSizeEnvelope_mono {first second : Nat} (before : first ≤ second) :
    growingFormulaSizeEnvelope first ≤ growingFormulaSizeEnvelope second := by
  dsimp only [growingFormulaSizeEnvelope, unaryCnfSize, unaryClauseSize, unaryListSize,
    unaryLiteralSize, symmetricBlockFamily, symmetricPositiveClause, symmetricNegativeClause,
    growingDiscoverySplitVar, growingDiscoveryAnchorVar]
  repeat first
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | exact before
    | exact Nat.le_refl _

def stageDiscoveryWorkEnvelope (depth : Nat) : Nat :=
  discoveryWorkEnvelope (growingFormulaSizeEnvelope (2 * (depth + 3)))

theorem stageDiscoveryWorkEnvelope_mono {first second : Nat} (before : first ≤ second) :
    stageDiscoveryWorkEnvelope first ≤ stageDiscoveryWorkEnvelope second :=
  discoveryWorkEnvelope_mono (growingFormulaSizeEnvelope_mono
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right before 3)))

theorem retainedStageDiscovery_bound {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (run.discoveryRun.outcome.comparisonWork.add run.discoveryRun.outcome.constructionWork).total ≤
      stageDiscoveryWorkEnvelope (depth + 1) := by
  have bounded := stageDiscovery_measured_bound (depth + 1)
  dsimp only at bounded
  rw [constitutedSearchIndex_exact] at bounded
  exact Nat.le_trans run.discoveryWorkLeCanonical
    (Nat.le_trans (Nat.le_add_left _ _) bounded)

/-- Sum the actual recorded discovery work over a causally threaded history.
The bound applies to any inhabitant of this concrete stage API, not just a
separately recomputed reference history. -/
theorem historyDiscovery_measured_bound {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    (history.measuredComparisonWork.add history.measuredConstructionWork).total ≤
      count * stageDiscoveryWorkEnvelope (depth + count) := by
  induction history with
  | nil => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | @step depth count input head tail ih =>
    change ((head.discoveryRun.outcome.comparisonWork.add tail.measuredComparisonWork).add
      (head.discoveryRun.outcome.constructionWork.add tail.measuredConstructionWork)).total ≤ _
    rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add,
      Nat.add_add_add_comm]
    have headBound := Nat.le_trans (retainedStageDiscovery_bound head)
      (stageDiscoveryWorkEnvelope_mono (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth))
    have depthEq : (depth + 1) + count = depth + (count + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 count]
    rw [depthEq] at ih
    have both := Nat.add_le_add headBound ih
    rw [ComparisonWork.total_add, ComparisonWork.total_add] at both
    rw [Nat.succ_mul]
    exact Nat.le_trans both (Nat.le_of_eq (Nat.add_comm _ _))

theorem storedRootScheduleSearch_bound (formula : Cnf)
    (discovery : EndogenousFlipDiscovery (GeneratedStructuralBranchContext.root formula))
    (stored : StoredLocalSchedule discovery) :
    (searchMeasuredRelation stored.entry.var stored.entry.source stored.entry.target).work.total ≤
      ((unaryCnfSize formula + unaryCnfSize formula) + (discovery.var + 5)) + (discovery.var + 5) := by
  have raw := searchMeasuredRelation_bound stored.entry.var stored.entry.source stored.entry.target
  rw [stored.entryExact] at raw ⊢
  exact Nat.le_trans raw
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (branchResidual_unarySize_le formula discovery.var false)
        (branchResidual_unarySize_le formula discovery.var true)) _) _)

def stageRelationWorkEnvelope (depth : Nat) : Nat :=
  let index := 2 * (depth + 3)
  ((growingFormulaSizeEnvelope index + growingFormulaSizeEnvelope index) +
    (index + 7)) + (index + 7)

theorem stageRelationWorkEnvelope_mono {first second : Nat} (before : first ≤ second) :
    stageRelationWorkEnvelope first ≤ stageRelationWorkEnvelope second := by
  have indexBefore := Nat.mul_le_mul_left 2 (Nat.add_le_add_right before 3)
  have sizeBefore := growingFormulaSizeEnvelope_mono indexBefore
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add sizeBefore sizeBefore)
    (Nat.add_le_add_right indexBefore 7)) (Nat.add_le_add_right indexBefore 7)

theorem retainedStageRelation_bound {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (searchMeasuredRelation run.storedSchedule.entry.var run.storedSchedule.entry.source
      run.storedSchedule.entry.target).work.total ≤ stageRelationWorkEnvelope (depth + 1) := by
  have raw := storedRootScheduleSearch_bound
    (distinctGrowingDiscoveryFormula (constitutedSearchIndex (depth + 1))) run.discovery run.storedSchedule
  have varExact : run.discovery.var = stageSelectedVar (depth + 1) := by
    have same := sequentialStage_selected_exact run
    rw [run.scheduleExact] at same
    exact same
  erw [varExact] at raw
  have sizes := Nat.add_le_add (growingFormula_unarySize_bound (constitutedSearchIndex (depth + 1)))
    (growingFormula_unarySize_bound (constitutedSearchIndex (depth + 1)))
  have bound := Nat.le_trans raw (Nat.add_le_add_right (Nat.add_le_add_right sizes _) _)
  unfold stageSelectedVar growingDiscoverySplitVar at bound
  change _ ≤ ((growingFormulaSizeEnvelope (constitutedSearchIndex (depth + 1)) +
    growingFormulaSizeEnvelope (constitutedSearchIndex (depth + 1))) +
    (constitutedSearchIndex (depth + 1) + 7)) + (constitutedSearchIndex (depth + 1) + 7) at bound
  exact Nat.le_trans bound (Nat.le_of_eq (congrArg
    (fun index => ((growingFormulaSizeEnvelope index + growingFormulaSizeEnvelope index) +
      (index + 7)) + (index + 7)) (constitutedSearchIndex_exact (depth + 1))))

theorem retainedStageValidationExecution_bound {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (run.measuredValidation.search.work.add run.measuredExecution.search.work).total ≤
      stageRelationWorkEnvelope (depth + 1) + stageRelationWorkEnvelope (depth + 1) := by
  rw [ComparisonWork.total_add, run.measuredValidation.searchExact, run.measuredExecution.searchExact]
  exact Nat.add_le_add (retainedStageRelation_bound run) (retainedStageRelation_bound run)

theorem historyValidationExecution_measured_bound {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    (history.measuredValidationWork.add history.measuredExecutionWork).total ≤
      count * (stageRelationWorkEnvelope (depth + count) + stageRelationWorkEnvelope (depth + count)) := by
  induction history with
  | nil => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | @step depth count input head tail ih =>
    change ((head.measuredValidation.search.work.add tail.measuredValidationWork).add
      (head.measuredExecution.search.work.add tail.measuredExecutionWork)).total ≤ _
    rw [ComparisonWork.total_add, ComparisonWork.total_add, ComparisonWork.total_add,
      Nat.add_add_add_comm]
    have later := stageRelationWorkEnvelope_mono
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
    have headBound := Nat.le_trans (retainedStageValidationExecution_bound head) (Nat.add_le_add later later)
    have depthEq : (depth + 1) + count = depth + (count + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 count]
    rw [depthEq] at ih
    have both := Nat.add_le_add headBound ih
    rw [ComparisonWork.total_add, ComparisonWork.total_add] at both
    rw [Nat.succ_mul]
    exact Nat.le_trans both (Nat.le_of_eq (Nat.add_comm _ _))

/-- Syntactic polynomial witnesses: these do not merely name arbitrary envelopes. -/
def growingFormulaSizePolynomial (x : CostPolynomial) : CostPolynomial :=
  let one : CostPolynomial := .constant 1
  let clause : CostPolynomial := .add (.add (.add x (.constant 4))
    (.add (.add (.add x (.constant 5)) one) one)) one
  let block : CostPolynomial := .add (.add clause (.add (.add clause one) one)) one
  .add (.add (.add (.mul (.add x one) (.add (.add x one) (.constant 3))) one) block) one

theorem growingFormulaSizePolynomial_eval (x : CostPolynomial) (input : Nat) :
    (growingFormulaSizePolynomial x).eval input = growingFormulaSizeEnvelope (x.eval input) := rfl

def discoveryEnvelopePolynomial (x : CostPolynomial) : CostPolynomial :=
  let one : CostPolynomial := .constant 1
  let five : CostPolynomial := .constant 5
  .add x (.mul x (.add (.add one (.add (.add x one) (.add x one)))
    (.add (.add (.add x x) (.add x five)) (.add x five))))

theorem discoveryEnvelopePolynomial_eval (x : CostPolynomial) (input : Nat) :
    (discoveryEnvelopePolynomial x).eval input = discoveryWorkEnvelope (x.eval input) := rfl

def stageDiscoveryPolynomial (depth : CostPolynomial) : CostPolynomial :=
  discoveryEnvelopePolynomial (growingFormulaSizePolynomial (.mul (.constant 2) (.add depth (.constant 3))))

theorem stageDiscoveryPolynomial_eval (depth : CostPolynomial) (input : Nat) :
    (stageDiscoveryPolynomial depth).eval input = stageDiscoveryWorkEnvelope (depth.eval input) := rfl

def stageRelationPolynomial (depth : CostPolynomial) : CostPolynomial :=
  let index : CostPolynomial := .mul (.constant 2) (.add depth (.constant 3))
  let size := growingFormulaSizePolynomial index
  .add (.add (.add size size) (.add index (.constant 7))) (.add index (.constant 7))

theorem stageRelationPolynomial_eval (depth : CostPolynomial) (input : Nat) :
    (stageRelationPolynomial depth).eval input = stageRelationWorkEnvelope (depth.eval input) := rfl

def stageRealizationWork (depth : Nat) : Nat := 2 * (2 * (depth + 3) + 1) + 16

theorem generatedRealizationWork_exact {depth : Nat} (generation : CanonicalStageGeneration depth) :
    (measuredGeneratedDiscovery generation).realizationWork.total = stageRealizationWork (depth + 1) := by
  change (constructMeasuredOperationalRoot
    (2 * ConstitutiveGeneration.positiveDepth generation.target)).work.total = _
  rw [constructMeasuredOperationalRoot_work, generation.targetExact]
  change 2 * (2 * constitutedOperationalIndex (depth + 1) + 1) + 16 = _
  rw [constitutedOperationalIndex_exact]
  rfl

theorem stageRealizationWork_mono {first second : Nat} (before : first ≤ second) :
    stageRealizationWork first ≤ stageRealizationWork second :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right before 3)) 1)) 16

theorem generatedHistoryRealizationWork_bound {depth count : Nat}
    (generated : CanonicalGeneratedHistory depth count) (input : SequentialAssignment depth) :
    (discoverGeneratedHistoryTransportPath generated input).realizationWork.total ≤
      count * stageRealizationWork (depth + count) := by
  induction generated with
  | nil => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | @step depth count generation tail ih =>
    rw [discoverGeneratedHistoryTransportPath]
    dsimp only
    split
    · rename_i failed
      rw [(measuredGeneratedDiscovery generation).recordedExact] at failed
      exact False.elim (stageRecordedDiscovery_ne_none _ failed)
    · rename_i discovery found
      erw [executeRecorded_eq_reference]
      let next := ((executeSequentialStage depth input).withGeneration generation).next
      have tailExact := discoverGeneratedHistoryTransportPath_exact tail next
      dsimp only at tailExact ⊢
      rw [tailExact.1]
      change ((measuredGeneratedDiscovery generation).realizationWork.add
        (discoverGeneratedHistoryTransportPath tail next).realizationWork).total ≤ _
      rw [ComparisonWork.total_add, generatedRealizationWork_exact]
      have headBound := stageRealizationWork_mono
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
      have tailBound := ih next
      have depthEq : depth + 1 + count = depth + (count + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 count]
      rw [depthEq] at tailBound
      rw [Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add headBound tailBound) (Nat.le_of_eq (Nat.add_comm _ _))

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredBool_work
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredDecision_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredHistory_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredDecision_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredHistory_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.branchResidual_unarySize_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelation_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelationFromData_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.rootCandidate_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.rootCandidateWorkBound_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.recordedExploration_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.candidateVariable_unarySize
#print axioms ConstitutiveSearch.EndogenousDecomposition.clauseCandidates_size
#print axioms ConstitutiveSearch.EndogenousDecomposition.clauseCandidate_label_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.cnfCandidates_size
#print axioms ConstitutiveSearch.EndogenousDecomposition.append_length_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.member_append_cases
#print axioms ConstitutiveSearch.EndogenousDecomposition.cnfCandidate_label_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.rootDiscovery_measured_input_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.clauseExtraction_visits_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.cnfExtraction_visits_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.rootDiscovery_with_extraction_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryWorkEnvelope_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.distinctDecoy_unarySize_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.growingFormula_unarySize_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscovery_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.growingFormulaSizeEnvelope_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscoveryWorkEnvelope_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedStageDiscovery_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyDiscovery_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.storedRootScheduleSearch_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRelationWorkEnvelope_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedStageRelation_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedStageValidationExecution_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.historyValidationExecution_measured_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.growingFormulaSizePolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryEnvelopePolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageDiscoveryPolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRelationPolynomial_eval
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedRealizationWork_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageRealizationWork_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.generatedHistoryRealizationWork_bound
/- AXIOM_AUDIT_END -/
