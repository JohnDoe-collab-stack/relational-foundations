import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFullStep
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredGeneration
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.IntegratedProjection

set_option linter.defProp false
set_option linter.unusedVariables false

/-!
# Constitutive feedback into the next discovery

This layer refines the already executed sequential history.  It does not
replace `GeneratedStep` by an operational relation.  Instead, it threads the
assignment returned by the executed code together with the ordered AND
decisions and their provenance.  The next candidate list is produced only
after that transmitted state has been inspected.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Executed scan of the transmitted determinations.  `available = false`
means that the variable governing the next local relation was already fixed. -/
structure TransmittedDecisionInspection where
  available : Bool
  visits : Nat

def inspectTransmittedDecisions (selected : Var) :
    (decisions : List StructuralBranchDecision) →
      TransmittedDecisionInspection
  | decisions =>
      ⟨structuralDecisionsAvoidCheck selected decisions, decisions.length⟩

theorem inspectTransmittedDecisions_head_selected
    (selected : Var) (value : Bool) (rest : List StructuralBranchDecision) :
    (inspectTransmittedDecisions selected
      (⟨selected, value⟩ :: rest)).available = false := by
  dsimp only [inspectTransmittedDecisions]
  rw [structuralDecisionsAvoidCheck]
  rw [if_pos rfl]

theorem structuralDecisionsAvoidCheck_true_of_avoid
    (selected : Var) (decisions : List StructuralBranchDecision)
    (avoid : StructuralDecisionsAvoid selected decisions) :
    structuralDecisionsAvoidCheck selected decisions = true := by
  induction decisions with
  | nil => rfl
  | cons decision rest inductionHypothesis =>
      rw [structuralDecisionsAvoidCheck]
      rw [if_neg avoid.1]
      exact inductionHypothesis avoid.2

theorem structuralDecisionsAvoid_of_check_true
    (selected : Var) (decisions : List StructuralBranchDecision)
    (checked : structuralDecisionsAvoidCheck selected decisions = true) :
    StructuralDecisionsAvoid selected decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      rw [structuralDecisionsAvoidCheck] at checked
      split at checked
      · contradiction
      · constructor
        · assumption
        · exact inductionHypothesis checked

theorem structuralDecisionsAvoid_member_ne
    (selected : Var) (decisions : List StructuralBranchDecision)
    (avoid : StructuralDecisionsAvoid selected decisions)
    (decision : StructuralBranchDecision)
    (member : decision ∈ decisions) : decision.var ≠ selected := by
  induction decisions with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      cases member with
      | head => exact avoid.1
      | tail _ prior => exact inductionHypothesis avoid.2 prior

theorem inspectTransmittedDecisions_available_of_all_lt
    (selected : Var) (decisions : List StructuralBranchDecision)
    (before : ∀ decision, decision ∈ decisions → decision.var < selected) :
    (inspectTransmittedDecisions selected decisions).available = true := by
  apply structuralDecisionsAvoidCheck_true_of_avoid
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · exact Nat.ne_of_lt (before decision (List.Mem.head rest))
      · apply inductionHypothesis
        intro prior member
        exact before prior (List.Mem.tail decision member)

theorem inspectTransmittedDecisions_visits_of_all_ne
    (selected : Var) (decisions : List StructuralBranchDecision)
    (_different : ∀ decision, decision ∈ decisions → decision.var ≠ selected) :
    (inspectTransmittedDecisions selected decisions).visits = decisions.length := by
  rfl

/-- The state transmitted between stages.  `assignment.reader` is the reader
produced by the preceding transport interpreter.  Decisions and provenance are
stored newest first, so their exact common order remains computational data. -/
structure ThreadedConstitutiveState (depth : Nat)
    (assignment : SequentialAssignment depth) where
  threadedAssignment : SequentialAssignment depth
  threadedAssignmentExact : threadedAssignment = assignment
  generation : CanonicalStageGeneration depth
  searchSeed : Nat
  searchSeedExact : searchSeed = generatedSearchSeed generation
  decisions : List StructuralBranchDecision
  provenance : List Var
  provenanceExact : provenance = decisions.map (fun decision => decision.var)
  decisionsHold : StructuralDecisionsHold assignment.assignment decisions

/-- Freshness is a success invariant of the canonical family, not part of the
general validity of a transmitted state.  Separating it permits valid states
whose history has already determined the next variable. -/
def ThreadedStateFreshForNext {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) : Prop :=
  ∀ decision, decision ∈ state.decisions →
    decision.var < stageSelectedVar (depth + 1)

/- The initial operational state consumes the endpoint actually produced by
the measured initialization run.  This keeps initialization and feedback on
one data path instead of reconstructing an extensionally equal source. -/
def initializationEndpointExact {depth : Nat}
    (initialization : ConstitutiveInitializationRun depth) :
    initialization.history.endpoint =
      (constructStage depth).history.endpoint :=
  congrArg (fun history => history.endpoint) initialization.historyExact

def initialThreadedConstitutiveStateFromInitialization {depth : Nat}
    (initialization : ConstitutiveInitializationRun depth) :
    ThreadedConstitutiveState depth (initialSequentialAssignment depth) :=
  let generation :=
    generateCanonicalStageFromSource initialization.history.endpoint
      (initializationEndpointExact initialization)
  { threadedAssignment := initialSequentialAssignment depth
    threadedAssignmentExact := rfl
    generation := generation
    searchSeed := generatedSearchSeed generation
    searchSeedExact := rfl
    decisions := []
    provenance := []
    provenanceExact := rfl
    decisionsHold := True.intro }

def initialThreadedConstitutiveState (depth : Nat) :
    ThreadedConstitutiveState depth (initialSequentialAssignment depth) :=
  initialThreadedConstitutiveStateFromInitialization
    (initializeConstitutiveHistory depth)

theorem initialThreadedConstitutiveStateFromInitialization_generation_exact
    {depth : Nat} (initialization : ConstitutiveInitializationRun depth) :
    (initialThreadedConstitutiveStateFromInitialization initialization).generation =
      generateCanonicalStage depth := by
  change generateCanonicalStageFromSource initialization.history.endpoint
      (initializationEndpointExact initialization) = generateCanonicalStage depth
  exact generateCanonicalStageFromSource_exact _ _

theorem initialThreadedConstitutiveState_generation_exact (depth : Nat) :
    (initialThreadedConstitutiveState depth).generation =
      generateCanonicalStage depth :=
  initialThreadedConstitutiveStateFromInitialization_generation_exact _

theorem initialThreadedConstitutiveStateFromInitialization_fresh {depth : Nat}
    (initialization : ConstitutiveInitializationRun depth) :
    ThreadedStateFreshForNext
      (initialThreadedConstitutiveStateFromInitialization initialization) := by
  intro _ impossible
  cases impossible

theorem initialThreadedConstitutiveState_fresh (depth : Nat) :
    ThreadedStateFreshForNext (initialThreadedConstitutiveState depth) := by
  exact initialThreadedConstitutiveStateFromInitialization_fresh _

theorem structuralDecisionsAvoid_of_all_lt
    (selected : Var) (decisions : List StructuralBranchDecision)
    (before : ∀ decision, decision ∈ decisions → decision.var < selected) :
    StructuralDecisionsAvoid selected decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · exact Nat.ne_of_lt (before decision (List.Mem.head rest))
      · apply inductionHypothesis
        intro prior member
        exact before prior (List.Mem.tail decision member)

theorem ThreadedConstitutiveState.decisionsAvoidNext
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions := by
  exact structuralDecisionsAvoid_of_all_lt _ _ fresh

/-- One executable comparison of a candidate with the transmitted AND
history.  The visit count is emitted by the same short-circuiting recursion. -/
structure CandidateHistoryCompatibilityRun
    (candidate : Var) (decisions : List StructuralBranchDecision) where
  compatible : Bool
  visits : Nat

def inspectCandidateHistory (candidate : Var) :
    (decisions : List StructuralBranchDecision) →
      CandidateHistoryCompatibilityRun candidate decisions
  | [] => ⟨true, 0⟩
  | decision :: rest =>
      if decision.var = candidate then ⟨false, 1⟩
      else
        let tail := inspectCandidateHistory candidate rest
        ⟨tail.compatible, tail.visits + 1⟩

/-- Executable, stable filtering of extracted candidates by the actual
transmitted decisions.  Both retained and rejected candidates remain in the
trace, while only retained candidates enter exploration. -/
structure CandidateHistoryFilterRun
    (decisions : List StructuralBranchDecision) (candidates : List Var) where
  retained : List Var
  rejected : List Var
  trace : List (Var × Bool)
  visits : Nat

def filterCandidatesByHistory (decisions : List StructuralBranchDecision) :
    (candidates : List Var) → CandidateHistoryFilterRun decisions candidates
  | [] => ⟨[], [], [], 0⟩
  | candidate :: rest =>
      let checked := inspectCandidateHistory candidate decisions
      let tail := filterCandidatesByHistory decisions rest
      if checked.compatible then
        ⟨candidate :: tail.retained, tail.rejected,
          (candidate, true) :: tail.trace, checked.visits + tail.visits⟩
      else
        ⟨tail.retained, candidate :: tail.rejected,
          (candidate, false) :: tail.trace, checked.visits + tail.visits⟩

theorem inspectCandidateHistory_compatible (candidate : Var)
    (decisions : List StructuralBranchDecision) :
    (inspectCandidateHistory candidate decisions).compatible =
      structuralDecisionsAvoidCheck candidate decisions := by
  induction decisions with
  | nil => rfl
  | cons decision rest inductionHypothesis =>
      rw [inspectCandidateHistory, structuralDecisionsAvoidCheck]
      split
      · rfl
      · exact inductionHypothesis

theorem filterCandidatesByHistory_retained (decisions : List StructuralBranchDecision)
    (candidates : List Var) :
    (filterCandidatesByHistory decisions candidates).retained =
      candidates.filter (fun candidate => structuralDecisionsAvoidCheck candidate decisions) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [filterCandidatesByHistory]
      cases checked : (inspectCandidateHistory candidate decisions).compatible with
      | false =>
          have predicateFalse :
              structuralDecisionsAvoidCheck candidate decisions = false := by
            rw [← inspectCandidateHistory_compatible]
            exact checked
          rw [List.filter, predicateFalse]
          exact inductionHypothesis
      | true =>
          have predicateTrue :
              structuralDecisionsAvoidCheck candidate decisions = true := by
            rw [← inspectCandidateHistory_compatible]
            exact checked
          rw [List.filter, predicateTrue]
          exact congrArg (List.cons candidate) inductionHypothesis

theorem filterCandidatesByHistory_retained_length_le
    (decisions : List StructuralBranchDecision) :
    ∀ candidates,
      (filterCandidatesByHistory decisions candidates).retained.length ≤
        candidates.length
  | [] => Nat.le_refl 0
  | candidate :: rest => by
      rw [filterCandidatesByHistory]
      split
      · exact Nat.succ_le_succ
          (filterCandidatesByHistory_retained_length_le decisions rest)
      · exact Nat.le_trans
          (filterCandidatesByHistory_retained_length_le decisions rest)
          (Nat.le_succ _)

theorem exploreRecordedCandidates_attempts_le_length
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    ∀ candidates,
      (exploreRecordedCandidates state candidates).attempts ≤ candidates.length
  | [] => Nat.le_refl 0
  | candidate :: rest => by
      rw [exploreRecordedCandidates]
      split
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · exact Nat.succ_le_succ
          (exploreRecordedCandidates_attempts_le_length state rest)

theorem extractClauseCandidateRun_length (clause : Clause) :
    (extractClauseCandidateRun clause).candidates.length =
      (extractClauseCandidateRun clause).stats.candidatesEmitted := by
  induction clause with
  | nil => rfl
  | cons literal rest inductionHypothesis =>
      change Nat.succ (extractClauseCandidateRun rest).candidates.length =
        (extractClauseCandidateRun rest).stats.candidatesEmitted + 1
      rw [inductionHypothesis]

theorem listLengthAppendConstructive {alpha : Type} :
    ∀ (left right : List alpha),
      (left ++ right).length = left.length + right.length := by
  have zeroAdd : ∀ n : Nat, 0 + n = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n inductionHypothesis =>
        change Nat.succ (0 + n) = Nat.succ n
        exact congrArg Nat.succ inductionHypothesis
  have succAdd : ∀ a b : Nat, Nat.succ a + b = Nat.succ (a + b) := by
    intro a b
    induction b with
    | zero => rfl
    | succ b inductionHypothesis =>
        change Nat.succ (Nat.succ a + b) =
          Nat.succ (Nat.succ (a + b))
        exact congrArg Nat.succ inductionHypothesis
  intro left right
  induction left with
  | nil =>
      change right.length = 0 + right.length
      exact (zeroAdd right.length).symm
  | cons head tail inductionHypothesis =>
      change Nat.succ (tail ++ right).length =
        Nat.succ tail.length + right.length
      exact Eq.trans
        (congrArg Nat.succ inductionHypothesis)
        (succAdd tail.length right.length).symm

theorem extractCnfCandidateRun_length (formula : Cnf) :
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
      rw [listLengthAppendConstructive, extractClauseCandidateRun_length,
        inductionHypothesis]

theorem runCandidateExtraction_length {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runCandidateExtraction state).candidates.length =
      (runCandidateExtraction state).stats.candidatesEmitted :=
  extractCnfCandidateRun_length state.context.formula

theorem memberOfFilter_original {alpha : Type} (predicate : alpha → Bool)
    (value : alpha) : ∀ values : List alpha,
    value ∈ values.filter predicate → value ∈ values
  | [], member => member
  | head :: tail, member => by
      rw [List.filter] at member
      split at member
      · cases member with
        | head => exact List.Mem.head tail
        | tail _ prior =>
            exact List.Mem.tail _ (memberOfFilter_original predicate value tail prior)
      · exact List.Mem.tail _ (memberOfFilter_original predicate value tail member)

theorem memberOfFilter_predicate {alpha : Type} (predicate : alpha → Bool)
    (value : alpha) : ∀ values : List alpha,
    value ∈ values.filter predicate → predicate value = true
  | [], member => nomatch member
  | head :: tail, member => by
      rw [List.filter] at member
      split at member
      · rename_i accepted
        cases member with
        | head => exact accepted
        | tail _ prior => exact memberOfFilter_predicate predicate value tail prior
      · exact memberOfFilter_predicate predicate value tail member

theorem memberOfFilter_of_original_and_predicate {alpha : Type}
    (predicate : alpha → Bool) (value : alpha) :
    ∀ values : List alpha, value ∈ values → predicate value = true →
      value ∈ values.filter predicate
  | [], member, _ => by cases member
  | head :: tail, member, accepted => by
      rw [List.filter]
      cases member with
      | head =>
          rw [accepted]
          exact List.Mem.head _
      | tail _ prior =>
          split
          · exact List.Mem.tail _
              (memberOfFilter_of_original_and_predicate predicate value tail
                prior accepted)
          · exact memberOfFilter_of_original_and_predicate predicate value tail
              prior accepted

theorem inspectCandidateHistory_visits_le (candidate : Var) :
    ∀ decisions : List StructuralBranchDecision,
      (inspectCandidateHistory candidate decisions).visits ≤ decisions.length
  | [] => Nat.le_refl 0
  | decision :: rest => by
      rw [inspectCandidateHistory]
      split
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · dsimp only
        exact Nat.succ_le_succ (inspectCandidateHistory_visits_le candidate rest)

theorem filterCandidatesByHistory_visits_le
    (decisions : List StructuralBranchDecision) :
    ∀ candidates : List Var,
      (filterCandidatesByHistory decisions candidates).visits ≤
        candidates.length * decisions.length
  | [] => Nat.zero_le _
  | candidate :: rest => by
      rw [filterCandidatesByHistory]
      split <;>
        simpa [Nat.succ_mul, Nat.add_comm] using
          (Nat.add_le_add
            (inspectCandidateHistory_visits_le candidate decisions)
            (filterCandidatesByHistory_visits_le decisions rest))

/-- Executable freshness check against the material variable provenance. -/
def provenanceAvoidCheck (candidate : Var) : List Var → Bool
  | [] => true
  | prior :: rest =>
      if prior = candidate then false
      else provenanceAvoidCheck candidate rest

/-- One executable comparison of a candidate with the material provenance
index transmitted by the preceding stages. -/
structure CandidateProvenanceCompatibilityRun
    (candidate : Var) (provenance : List Var) where
  compatible : Bool
  visits : Nat

def inspectCandidateProvenance (candidate : Var) :
    (provenance : List Var) →
      CandidateProvenanceCompatibilityRun candidate provenance
  | [] => ⟨true, 0⟩
  | prior :: rest =>
      if prior = candidate then ⟨false, 1⟩
      else
        let tail := inspectCandidateProvenance candidate rest
        ⟨tail.compatible, tail.visits + 1⟩

theorem inspectCandidateProvenance_compatible
    (candidate : Var) (provenance : List Var) :
    (inspectCandidateProvenance candidate provenance).compatible =
      provenanceAvoidCheck candidate provenance := by
  induction provenance with
  | nil => rfl
  | cons prior rest inductionHypothesis =>
      rw [inspectCandidateProvenance, provenanceAvoidCheck]
      split
      · rfl
      · exact inductionHypothesis

/-- The material provenance is exactly the variable projection of the richer
executed decision history, so both executable freshness predicates agree. -/
theorem provenanceAvoidCheck_decisions
    (candidate : Var) :
    ∀ decisions : List StructuralBranchDecision,
      provenanceAvoidCheck candidate
          (decisions.map (fun decision => decision.var)) =
        structuralDecisionsAvoidCheck candidate decisions
  | [] => rfl
  | decision :: rest => by
      by_cases same : decision.var = candidate
      · rw [List.map, provenanceAvoidCheck, structuralDecisionsAvoidCheck,
          if_pos same, if_pos same]
      · rw [List.map, provenanceAvoidCheck, structuralDecisionsAvoidCheck,
          if_neg same, if_neg same]
        exact provenanceAvoidCheck_decisions candidate rest

theorem inspectCandidateProvenance_map_compatible
    (candidate : Var) (decisions : List StructuralBranchDecision) :
    (inspectCandidateProvenance candidate
        (decisions.map (fun decision => decision.var))).compatible =
      (inspectCandidateHistory candidate decisions).compatible := by
  rw [inspectCandidateProvenance_compatible,
    provenanceAvoidCheck_decisions, inspectCandidateHistory_compatible]

theorem inspectCandidateProvenance_map_visits
    (candidate : Var) :
    ∀ decisions : List StructuralBranchDecision,
      (inspectCandidateProvenance candidate
          (decisions.map (fun decision => decision.var))).visits =
        (inspectCandidateHistory candidate decisions).visits
  | [] => rfl
  | decision :: rest => by
      by_cases same : decision.var = candidate
      · rw [List.map, inspectCandidateProvenance, inspectCandidateHistory,
          if_pos same, if_pos same]
      · rw [List.map, inspectCandidateProvenance, inspectCandidateHistory,
          if_neg same, if_neg same]
        exact congrArg (fun visits => visits + 1)
          (inspectCandidateProvenance_map_visits candidate rest)

/-- Stable candidate filtering driven directly by the material provenance
resource.  Its trace and visit count are emitted by the same recursion. -/
structure CandidateProvenanceFilterRun
    (provenance : List Var) (candidates : List Var) where
  retained : List Var
  rejected : List Var
  trace : List (Var × Bool)
  visits : Nat

def filterCandidatesByProvenance (provenance : List Var) :
    (candidates : List Var) →
      CandidateProvenanceFilterRun provenance candidates
  | [] => ⟨[], [], [], 0⟩
  | candidate :: rest =>
      let checked := inspectCandidateProvenance candidate provenance
      let tail := filterCandidatesByProvenance provenance rest
      if checked.compatible then
        ⟨candidate :: tail.retained, tail.rejected,
          (candidate, true) :: tail.trace, checked.visits + tail.visits⟩
      else
        ⟨tail.retained, candidate :: tail.rejected,
          (candidate, false) :: tail.trace, checked.visits + tail.visits⟩

theorem filterCandidatesByProvenance_retained
    (provenance : List Var) (candidates : List Var) :
    (filterCandidatesByProvenance provenance candidates).retained =
      candidates.filter (fun candidate =>
        provenanceAvoidCheck candidate provenance) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [filterCandidatesByProvenance]
      cases checked :
          (inspectCandidateProvenance candidate provenance).compatible with
      | false =>
          have predicateFalse :
              provenanceAvoidCheck candidate provenance = false := by
            rw [← inspectCandidateProvenance_compatible]
            exact checked
          rw [List.filter, predicateFalse]
          exact inductionHypothesis
      | true =>
          have predicateTrue :
              provenanceAvoidCheck candidate provenance = true := by
            rw [← inspectCandidateProvenance_compatible]
            exact checked
          rw [List.filter, predicateTrue]
          exact congrArg (List.cons candidate) inductionHypothesis

theorem inspectCandidateProvenance_visits_le (candidate : Var) :
    ∀ provenance : List Var,
      (inspectCandidateProvenance candidate provenance).visits ≤
        provenance.length
  | [] => Nat.le_refl 0
  | prior :: rest => by
      rw [inspectCandidateProvenance]
      split
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · dsimp only
        exact Nat.succ_le_succ
          (inspectCandidateProvenance_visits_le candidate rest)

theorem listMapLengthConstructive {alpha beta : Type}
    (map : alpha → beta) :
    ∀ values : List alpha, (values.map map).length = values.length
  | [] => rfl
  | _head :: rest =>
      congrArg Nat.succ (listMapLengthConstructive map rest)

theorem filterCandidatesByProvenance_visits_le
    (provenance : List Var) :
    ∀ candidates : List Var,
      (filterCandidatesByProvenance provenance candidates).visits ≤
        candidates.length * provenance.length
  | [] => Nat.zero_le _
  | candidate :: rest => by
      rw [filterCandidatesByProvenance]
      split <;>
        simpa [Nat.succ_mul, Nat.add_comm] using
          (Nat.add_le_add
            (inspectCandidateProvenance_visits_le candidate provenance)
            (filterCandidatesByProvenance_visits_le provenance rest))

/-- Replacing the richer history scan by its material variable provenance
changes neither admissibility nor trace nor exact executed filtering work. -/
theorem filterCandidatesByProvenance_matches_history
    (decisions : List StructuralBranchDecision)
    (candidates : List Var) :
    let provenance := decisions.map (fun decision => decision.var)
    let byProvenance := filterCandidatesByProvenance provenance candidates
    let byHistory := filterCandidatesByHistory decisions candidates
    byProvenance.retained = byHistory.retained ∧
      byProvenance.rejected = byHistory.rejected ∧
      byProvenance.trace = byHistory.trace ∧
      byProvenance.visits = byHistory.visits := by
  dsimp only
  induction candidates with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons candidate rest inductionHypothesis =>
      have compatible :=
        inspectCandidateProvenance_map_compatible candidate decisions
      have visits :=
        inspectCandidateProvenance_map_visits candidate decisions
      rw [filterCandidatesByProvenance, filterCandidatesByHistory]
      cases provenanceAccepted :
          (inspectCandidateProvenance candidate
            (decisions.map (fun decision => decision.var))).compatible with
      | false =>
          have historyRejected :
              (inspectCandidateHistory candidate decisions).compatible = false := by
            rw [← compatible]
            exact provenanceAccepted
          rw [historyRejected]
          repeat rw [if_neg (by decide : false ≠ true)]
          exact
            ⟨inductionHypothesis.1,
              congrArg (List.cons candidate) inductionHypothesis.2.1,
              congrArg (List.cons (candidate, false)) inductionHypothesis.2.2.1,
              by rw [visits, inductionHypothesis.2.2.2]⟩
      | true =>
          have historyAccepted :
              (inspectCandidateHistory candidate decisions).compatible = true := by
            rw [← compatible]
            exact provenanceAccepted
          rw [historyAccepted]
          repeat rw [if_pos (by decide : true = true)]
          exact
            ⟨congrArg (List.cons candidate) inductionHypothesis.1,
              inductionHypothesis.2.1,
              congrArg (List.cons (candidate, true)) inductionHypothesis.2.2.1,
              by rw [visits, inductionHypothesis.2.2.2]⟩

theorem filterCandidatesByProvenance_retained_decisions
    (decisions : List StructuralBranchDecision)
    (candidates : List Var) :
    (filterCandidatesByProvenance
      (decisions.map (fun decision => decision.var)) candidates).retained =
      candidates.filter (fun candidate =>
        structuralDecisionsAvoidCheck candidate decisions) := by
  exact Eq.trans
    (filterCandidatesByProvenance_matches_history decisions candidates).1
    (filterCandidatesByHistory_retained decisions candidates)

theorem filterCandidatesByProvenance_retained_length_le
    (provenance : List Var) :
    ∀ candidates : List Var,
      (filterCandidatesByProvenance provenance candidates).retained.length ≤
        candidates.length
  | [] => Nat.le_refl 0
  | candidate :: rest => by
      rw [filterCandidatesByProvenance]
      split
      · exact Nat.succ_le_succ
          (filterCandidatesByProvenance_retained_length_le provenance rest)
      · exact Nat.le_trans
          (filterCandidatesByProvenance_retained_length_le provenance rest)
          (Nat.le_succ _)

theorem provenanceAvoidCheck_head_selected
    (selected : Var) (rest : List Var) :
    provenanceAvoidCheck selected (selected :: rest) = false := by
  rw [provenanceAvoidCheck, if_pos rfl]

theorem structuralDecisionsAvoidCheck_false_witness
    (candidate : Var) : ∀ decisions : List StructuralBranchDecision,
      structuralDecisionsAvoidCheck candidate decisions = false →
      ∃ decision, decision ∈ decisions ∧ decision.var = candidate
  | [], impossible => by cases impossible
  | decision :: rest, failed => by
      rw [structuralDecisionsAvoidCheck] at failed
      split at failed
      · exact ⟨decision, List.Mem.head rest, by assumption⟩
      · rcases structuralDecisionsAvoidCheck_false_witness candidate rest failed with
          ⟨witness, member, same⟩
        exact ⟨witness, List.Mem.tail decision member, same⟩

theorem listMemAppendCases {alpha : Type} (value : alpha) :
    ∀ left right : List alpha, value ∈ left ++ right → value ∈ left ∨ value ∈ right
  | [], right, member => Or.inr member
  | head :: tail, right, member => by
      cases member with
      | head => exact Or.inl (List.Mem.head tail)
      | tail _ prior =>
          rcases listMemAppendCases value tail right prior with inLeft | inRight
          · exact Or.inl (List.Mem.tail head inLeft)
          · exact Or.inr inRight

theorem optionEqNoneOfMapEqNone {alpha beta : Type} (map : alpha → beta) :
    ∀ value : Option alpha, value.map map = none → value = none
  | none, _ => rfl
  | some value, impossible => by cases impossible

theorem stageExtracted_lt_selected_is_decoy (depth : Nat) (candidate : Var)
    (member : candidate ∈ stageExtractedCandidates depth)
    (below : candidate < stageSelectedVar depth) :
    candidate ∈ distinctDecoyVariables ((constructStage depth).searchIndex + 1) := by
  have memberExact : candidate ∈
      distinctDecoyVariables ((constructStage depth).searchIndex + 1) ++
        [growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex,
          growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex] :=
    Eq.mp (congrArg (fun candidates => candidate ∈ candidates)
      (stageExtractedCandidates_exact depth)) member
  rcases listMemAppendCases candidate _ _ memberExact with decoy | tail
  · exact decoy
  · cases tail with
    | head =>
        exact False.elim (Nat.lt_irrefl _ below)
    | tail _ tail => cases tail with
      | head =>
          change stageAnchorVar depth < stageSelectedVar depth at below
          have same := stageAnchorVar_eq_selected_succ depth
          cases same
          exact False.elim (Nat.not_lt_of_ge (Nat.le_succ _) below)
      | tail _ tail => cases tail with
        | head =>
            exact False.elim (Nat.lt_irrefl _ below)
        | tail _ tail => cases tail with
          | head =>
              change stageAnchorVar depth < stageSelectedVar depth at below
              have same := stageAnchorVar_eq_selected_succ depth
              cases same
              exact False.elim (Nat.not_lt_of_ge (Nat.le_succ _) below)
          | tail _ impossible => cases impossible

theorem exploreRecordedCandidates_filter_failed
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (decisions : List StructuralBranchDecision) :
    ∀ candidates : List Var,
      (∀ candidate, candidate ∈ candidates →
        structuralDecisionsAvoidCheck candidate decisions = false →
        (tryMeasuredCandidate state candidate).produced? = none) →
      (exploreRecordedCandidates state
        (candidates.filter (fun candidate =>
          structuralDecisionsAvoidCheck candidate decisions))).discovered? =
      (exploreRecordedCandidates state candidates).discovered?
  | [], _allFailed => rfl
  | candidate :: rest, allFailed => by
      have tailFailed : ∀ prior, prior ∈ rest →
          structuralDecisionsAvoidCheck prior decisions = false →
          (tryMeasuredCandidate state prior).produced? = none := by
        intro prior member rejected
        exact allFailed prior (List.Mem.tail candidate member) rejected
      rw [List.filter]
      split
      · unfold exploreRecordedCandidates
        dsimp only
        split
        · rfl
        · exact exploreRecordedCandidates_filter_failed state decisions rest tailFailed
      · have headFailed := allFailed candidate (List.Mem.head rest) (by assumption)
        rw [exploreRecordedCandidates]
        dsimp only
        rw [headFailed]
        exact exploreRecordedCandidates_filter_failed state decisions rest tailFailed

theorem exploreRecordedCandidates_filter_work_le
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (decisions : List StructuralBranchDecision) :
    ∀ candidates : List Var,
      (∀ candidate, candidate ∈ candidates →
        structuralDecisionsAvoidCheck candidate decisions = false →
        (tryMeasuredCandidate state candidate).produced? = none) →
      let filtered := exploreRecordedCandidates state
        (candidates.filter (fun candidate =>
          structuralDecisionsAvoidCheck candidate decisions))
      let original := exploreRecordedCandidates state candidates
      filtered.comparisonWork.total ≤ original.comparisonWork.total ∧
        filtered.constructionWork.total ≤ original.constructionWork.total
  | [], _allFailed => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | candidate :: rest, allFailed => by
      have tailFailed : ∀ prior, prior ∈ rest →
          structuralDecisionsAvoidCheck prior decisions = false →
          (tryMeasuredCandidate state prior).produced? = none := by
        intro prior member rejected
        exact allFailed prior (List.Mem.tail candidate member) rejected
      have tailBound := exploreRecordedCandidates_filter_work_le
        state decisions rest tailFailed
      rw [List.filter]
      split
      · cases found : (tryMeasuredCandidate state candidate).produced? with
        | some produced =>
            simp only [exploreRecordedCandidates, found]
            exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        | none =>
            simp only [exploreRecordedCandidates, found]
            constructor
            · let headWork := (tryMeasuredCandidate state candidate).freshnessWork.add
                  (tryMeasuredCandidate state candidate).relationWork
              let filteredWork := (exploreRecordedCandidates state
                (rest.filter (fun prior =>
                  structuralDecisionsAvoidCheck prior decisions))).comparisonWork
              let originalWork := (exploreRecordedCandidates state rest).comparisonWork
              have base : headWork.total + filteredWork.total ≤
                  headWork.total + originalWork.total := Nat.add_le_add_left tailBound.1 _
              apply Eq.mpr (congrArg
                (fun left => left ≤ (headWork.add originalWork).total)
                (ComparisonWork.total_add headWork filteredWork))
              apply Eq.mpr (congrArg
                (fun right => headWork.total + filteredWork.total ≤ right)
                (ComparisonWork.total_add headWork originalWork))
              exact base
            · let headWork := (tryMeasuredCandidate state candidate).constructionWork
              let filteredWork := (exploreRecordedCandidates state
                (rest.filter (fun prior =>
                  structuralDecisionsAvoidCheck prior decisions))).constructionWork
              let originalWork := (exploreRecordedCandidates state rest).constructionWork
              have base : headWork.total + filteredWork.total ≤
                  headWork.total + originalWork.total := Nat.add_le_add_left tailBound.2 _
              apply Eq.mpr (congrArg
                (fun left => left ≤ (headWork.add originalWork).total)
                (ComparisonWork.total_add headWork filteredWork))
              apply Eq.mpr (congrArg
                (fun right => headWork.total + filteredWork.total ≤ right)
                (ComparisonWork.total_add headWork originalWork))
              exact base
      · have headFailed := allFailed candidate (List.Mem.head rest) (by assumption)
        rw [exploreRecordedCandidates]
        dsimp only
        rw [headFailed]
        constructor
        · rw [ComparisonWork.total_add]
          exact Nat.le_trans tailBound.1 (Nat.le_add_left _ _)
        · rw [ComparisonWork.total_add]
          exact Nat.le_trans tailBound.2 (Nat.le_add_left _ _)

theorem exploreRecordedCandidates_filter_total_le
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (decisions : List StructuralBranchDecision)
    (candidates : List Var)
    (allFailed : ∀ candidate, candidate ∈ candidates →
      structuralDecisionsAvoidCheck candidate decisions = false →
      (tryMeasuredCandidate state candidate).produced? = none) :
    let filtered := exploreRecordedCandidates state
      (candidates.filter (fun candidate =>
        structuralDecisionsAvoidCheck candidate decisions))
    let original := exploreRecordedCandidates state candidates
    (filtered.comparisonWork.add filtered.constructionWork).total ≤
      (original.comparisonWork.add original.constructionWork).total := by
  have bounds := exploreRecordedCandidates_filter_work_le
    state decisions candidates allFailed
  dsimp only
  rw [ComparisonWork.total_add, ComparisonWork.total_add]
  exact Nat.add_le_add bounds.1 bounds.2

theorem exploreRecordedCandidates_none_of_all_failed
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    ∀ candidates : List Var,
      (∀ candidate, candidate ∈ candidates →
        (tryMeasuredCandidate state candidate).produced? = none) →
      (exploreRecordedCandidates state candidates).discovered? = none
  | [], _allFailed => rfl
  | candidate :: rest, allFailed => by
      rw [exploreRecordedCandidates]
      dsimp only
      rw [allFailed candidate (List.Mem.head rest)]
      apply exploreRecordedCandidates_none_of_all_failed state rest
      intro prior member
      exact allFailed prior (List.Mem.tail candidate member)

theorem stageExtracted_classification (depth : Nat) (candidate : Var)
    (member : candidate ∈ stageExtractedCandidates depth) :
    candidate ∈ distinctDecoyVariables ((constructStage depth).searchIndex + 1) ∨
      candidate = stageSelectedVar depth ∨ candidate = stageAnchorVar depth := by
  have memberExact : candidate ∈
      distinctDecoyVariables ((constructStage depth).searchIndex + 1) ++
        [growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex,
          growingDiscoverySplitVar (constructStage depth).searchIndex,
          growingDiscoveryAnchorVar (constructStage depth).searchIndex] :=
    Eq.mp (congrArg (fun candidates => candidate ∈ candidates)
      (stageExtractedCandidates_exact depth)) member
  rcases listMemAppendCases candidate _ _ memberExact with decoy | tail
  · exact Or.inl decoy
  · cases tail with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ tail => cases tail with
      | head => exact Or.inr (Or.inr rfl)
      | tail _ tail => cases tail with
        | head => exact Or.inr (Or.inl rfl)
        | tail _ tail => cases tail with
          | head => exact Or.inr (Or.inr rfl)
          | tail _ impossible => cases impossible

/-- Single executable engine used both by the active threaded state and by
the same-projection separator.  It realizes and extracts once, filters each
candidate against the material provenance transmitted by prior stages, then
performs the unique exploration pass. -/
structure FeedbackDiscoveryFromDataRun (depth : Nat)
    (generation : CanonicalStageGeneration depth)
    (provenance : List Var) where
  generated : GeneratedExtractionBundle generation
  generatedExact : generated = measuredGeneratedExtraction generation
  filtering : CandidateProvenanceFilterRun provenance generated.extraction.candidates
  filteringExact : filtering =
    filterCandidatesByProvenance provenance generated.extraction.candidates
  candidates : List Var
  candidatesExact : candidates = filtering.retained
  outcome : RecordedDiscoveryOutcome (constructStage (depth + 1)).operationalRoot
  outcomeExact : outcome = exploreRecordedCandidates
    (constructStage (depth + 1)).operationalRoot candidates

theorem exploreRecordedCandidates_transport_exact
    {rootFormula : Cnf}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (same : source = target)
    (candidates : List Var) :
    Eq.rec (motive := fun state _ => RecordedDiscoveryOutcome state)
        (exploreRecordedCandidates source candidates)
        same =
      exploreRecordedCandidates target candidates := by
  cases same
  rfl

def runFeedbackDiscoveryFromData (depth : Nat)
    (generation : CanonicalStageGeneration depth)
    (provenance : List Var)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    FeedbackDiscoveryFromDataRun depth generation provenance :=
  let generated :=
    measuredGeneratedExtractionFromSeed generation searchSeed searchSeedExact
  let filtering :=
    filterCandidatesByProvenance provenance generated.extraction.candidates
  let candidates := filtering.retained
  let producedOutcome :=
    exploreRecordedCandidates generated.operationalRoot candidates
  let outcome := Eq.rec
    (motive := fun state _ => RecordedDiscoveryOutcome state)
    producedOutcome
    generated.operationalRootExact
  { generated := generated
    generatedExact :=
      measuredGeneratedExtractionFromSeed_eq generation searchSeed searchSeedExact
    filtering := filtering
    filteringExact := rfl
    candidates := candidates
    candidatesExact := rfl
    outcome := outcome
    outcomeExact :=
      exploreRecordedCandidates_transport_exact
        generated.operationalRootExact candidates }

/-- Discovery executed from a generated target after consuming the material
provenance index transmitted by prior stages. The richer executed decisions remain
in the state for value-sensitive semantics; candidate availability consumes
only the variable provenance it actually needs. -/
structure ThreadedNextDiscoveryRun (depth : Nat)
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) where
  generated : GeneratedExtractionBundle state.generation
  generatedFromSearchSeed :
    generated =
      measuredGeneratedExtractionFromSeed
        state.generation state.searchSeed state.searchSeedExact
  generatedExact : generated = measuredGeneratedExtraction state.generation
  filtering :
    CandidateProvenanceFilterRun state.provenance generated.extraction.candidates
  filteringExact : filtering =
    filterCandidatesByProvenance state.provenance generated.extraction.candidates
  candidates : List Var
  candidatesExact : candidates = filtering.retained
  outcome : RecordedDiscoveryOutcome (constructStage (depth + 1)).operationalRoot
  outcomeExact : outcome =
    exploreRecordedCandidates (constructStage (depth + 1)).operationalRoot candidates

def runThreadedNextDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    ThreadedNextDiscoveryRun depth state :=
  let core :=
    runFeedbackDiscoveryFromData depth state.generation state.provenance
      state.searchSeed state.searchSeedExact
  { generated := core.generated
    generatedFromSearchSeed := by
      unfold core runFeedbackDiscoveryFromData
      rfl
    generatedExact := core.generatedExact
    filtering := core.filtering
    filteringExact := core.filteringExact
    candidates := core.candidates
    candidatesExact := core.candidatesExact
    outcome := core.outcome
    outcomeExact := core.outcomeExact }

def ThreadedNextDiscoveryRun.asRecorded {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
  (run : ThreadedNextDiscoveryRun depth state) :
    RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot :=
  { extraction := run.generated.extraction
    outcome := run.outcome }

theorem threadedRemovedCandidatesFail {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    ∀ candidate,
      candidate ∈ (stageRecordedDiscoveryRun (depth + 1)).extraction.candidates →
      provenanceAvoidCheck candidate state.provenance = false →
      (tryMeasuredCandidate
        (constructStage (depth + 1)).operationalRoot candidate).produced? = none := by
  intro candidate member rejected
  have rejectedDecisions :
      structuralDecisionsAvoidCheck candidate state.decisions = false := by
    rw [← provenanceAvoidCheck_decisions candidate state.decisions]
    rw [← state.provenanceExact]
    exact rejected
  rcases structuralDecisionsAvoidCheck_false_witness
    candidate state.decisions rejectedDecisions with
      ⟨decision, decisionMember, same⟩
  have below : candidate < stageSelectedVar (depth + 1) := by
    cases same
    exact fresh decision decisionMember
  have extractedMember : candidate ∈ stageExtractedCandidates (depth + 1) := member
  have decoy := stageExtracted_lt_selected_is_decoy
    (depth + 1) candidate extractedMember below
  have unmeasuredNone := distinctGrowingDiscoveryDecoyCandidate_none
    (constructStage (depth + 1)).searchIndex candidate decoy
  let measured := tryMeasuredCandidate
    (constructStage (depth + 1)).operationalRoot candidate
  have resultNone : measured.result = none := by
    exact Eq.trans (tryMeasuredCandidate_exact _ _) unmeasuredNone
  change measured.produced?.map (fun produced => produced.discovery) = none at resultNone
  exact optionEqNoneOfMapEqNone (fun produced => produced.discovery)
    measured.produced? resultNone

theorem runThreadedNextDiscovery_discovered_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (runThreadedNextDiscovery state).outcome.discovered? =
      (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? := by
  let candidates :=
    (stageRecordedDiscoveryRun (depth + 1)).extraction.candidates
  have removedFail := threadedRemovedCandidatesFail state fresh
  have removedFailDecisions :
      ∀ candidate, candidate ∈ candidates →
        structuralDecisionsAvoidCheck candidate state.decisions = false →
        (tryMeasuredCandidate
          (constructStage (depth + 1)).operationalRoot candidate).produced? = none := by
    intro candidate member rejected
    apply removedFail candidate member
    rw [state.provenanceExact, provenanceAvoidCheck_decisions]
    exact rejected
  have preserved := exploreRecordedCandidates_filter_failed
    (constructStage (depth + 1)).operationalRoot state.decisions candidates
      removedFailDecisions
  let run := runThreadedNextDiscovery state
  change run.outcome.discovered? =
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered?
  rw [run.outcomeExact]
  rw [run.candidatesExact, run.filteringExact, run.generatedExact]
  rw [state.provenanceExact]
  rw [filterCandidatesByProvenance_retained_decisions]
  rw [(measuredGeneratedExtraction state.generation).extractionExact]
  exact preserved

theorem runThreadedNextDiscovery_work_le_canonical {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    let run := runThreadedNextDiscovery state
    (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total := by
  let candidates :=
    (stageRecordedDiscoveryRun (depth + 1)).extraction.candidates
  have removedFail := threadedRemovedCandidatesFail state fresh
  have removedFailDecisions :
      ∀ candidate, candidate ∈ candidates →
        structuralDecisionsAvoidCheck candidate state.decisions = false →
        (tryMeasuredCandidate
          (constructStage (depth + 1)).operationalRoot candidate).produced? = none := by
    intro candidate member rejected
    apply removedFail candidate member
    rw [state.provenanceExact, provenanceAvoidCheck_decisions]
    exact rejected
  have bounded := exploreRecordedCandidates_filter_total_le
    (constructStage (depth + 1)).operationalRoot state.decisions candidates
      removedFailDecisions
  let run := runThreadedNextDiscovery state
  change
    (run.outcome.comparisonWork.add run.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total
  rw [run.outcomeExact]
  rw [run.candidatesExact, run.filteringExact, run.generatedExact]
  rw [state.provenanceExact]
  rw [filterCandidatesByProvenance_retained_decisions]
  rw [(measuredGeneratedExtraction state.generation).extractionExact]
  exact bounded

theorem runThreadedNextDiscovery_found {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (runThreadedNextDiscovery state).outcome.discovered? ≠ none := by
  rw [runThreadedNextDiscovery_discovered_exact state fresh]
  exact stageRecordedDiscovery_ne_none (depth + 1)

/-- Recursive append producer for chronological provenance. -/
structure ProvenanceAppendRun (history : List Var) (next : Var) where
  output : List Var
  outputExact : output = history ++ [next]
  visits : Nat
  visitsExact : visits = history.length + 1

def appendProvenanceMeasured (next : Var) :
    (history : List Var) → ProvenanceAppendRun history next
  | [] => ⟨[next], rfl, 1, rfl⟩
  | head :: tail =>
      let suffix := appendProvenanceMeasured next tail
      { output := head :: suffix.output
        outputExact := by rw [suffix.outputExact]; rfl
        visits := suffix.visits + 1
        visitsExact := by rw [suffix.visitsExact]; rfl }

/-- Constant-time producer for newest-first provenance. -/
structure ProvenancePrependRun (history : List Var) (next : Var) where
  output : List Var
  outputExact : output = next :: history
  visits : Nat
  visitsExact : visits = 1

def prependProvenanceMeasured (next : Var) (history : List Var) :
    ProvenancePrependRun history next :=
  ⟨next :: history, rfl, 1, rfl⟩

theorem structuralDecisionsHold_transport
    (before after : Assignment) (decisions : List StructuralBranchDecision)
    (held : StructuralDecisionsHold before decisions)
    (preserved : ∀ decision, decision ∈ decisions →
      after decision.var = before decision.var) :
    StructuralDecisionsHold after decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · rw [preserved decision (List.Mem.head rest)]
        exact held.1
      · apply inductionHypothesis
        · exact held.2
        · intro prior member
          exact preserved prior (List.Mem.tail decision member)

theorem stageNext_preserves_threadedDecisions {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    StructuralDecisionsHold stage.next.assignment state.decisions := by
  apply structuralDecisionsHold_transport
    assignment.assignment stage.next.assignment state.decisions state.decisionsHold
  intro decision member
  have different : decision.var ≠ stageSelectedVar (depth + 1) :=
    structuralDecisionsAvoid_member_ne _ _ avoid decision member
  rw [sequentialStage_next_from_input, Assignment.flipAt_other]
  rw [sequentialStage_selected_exact]
  exact different

/-- The useful variable of one stage is exactly the search index that will
parameterize the following stage. -/
theorem stageSelectedVar_eq_nextSearchIndex (depth : Nat) :
    stageSelectedVar depth = (constructStage (depth + 1)).searchIndex := by
  unfold stageSelectedVar growingDiscoverySplitVar
  rw [generateCanonicalStage_searchIndex_advances]

/-- Read the newest decision variable from the state actually produced by the
executed local transport. The empty case is unreachable for a valid execution and
is discharged extensionally by the exactness theorem below. -/
def executedProducedSearchSeed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) : Var :=
  match stage.execution.producedState.context.decisions with
  | [] => 0
  | decision :: _ => decision.var

theorem executedProducedSearchSeed_eq_scheduleEntry {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedProducedSearchSeed stage = stage.schedule.entry.var := by
  unfold executedProducedSearchSeed
  rw [stage.execution.producedStateExact]
  rw [stage.scheduleExact]
  rfl

theorem executedProducedSearchSeed_eq_nextSearchIndex {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedProducedSearchSeed stage =
      (constructStage ((depth + 1) + 1)).searchIndex := by
  rw [executedProducedSearchSeed_eq_scheduleEntry,
    sequentialStage_selected_exact]
  exact stageSelectedVar_eq_nextSearchIndex (depth + 1)

/-- The branch determination is formed from the bit returned by the executed
transport.  Its canonical `true` value is a theorem about that execution,
not the datum used to construct the determination. -/
def executedBranchDecision {depth : Nat} {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) : StructuralBranchDecision :=
  ⟨stageSelectedVar (depth + 1),
    stage.application.output.1 (stageSelectedVar (depth + 1))⟩

theorem executedBranchDecision_eq_selected_true {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedBranchDecision stage =
      ⟨stageSelectedVar (depth + 1), true⟩ := by
  unfold executedBranchDecision
  have selected :
      stage.schedule.entry.var = stageSelectedVar (depth + 1) :=
    sequentialStage_selected_exact stage
  rw [← selected, stage.output_selected]

/-- Instrumented realization of the complete next state.  It consumes the
actual generated target, the executed continuation and the accumulated decision
history; the next discovery is then computed from the returned state. -/
structure NextOperationalStateRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) where
  provenanceRun : ProvenancePrependRun state.provenance stage.schedule.entry.var
  next : ThreadedConstitutiveState (depth + 1) stage.next
  assignmentFromExecution : next.threadedAssignment.assignment = stage.next.assignment
  searchSeedFromProducedState :
    next.searchSeed = executedProducedSearchSeed stage
  generationFromProducedTarget :
    next.generation =
      generateCanonicalStageFromSource state.generation.target state.generation.targetExact
  decisionsFromExecutedOutput :
    next.decisions = executedBranchDecision stage :: state.decisions
  decisionsFromExecution :
    next.decisions =
      ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions
  provenanceFromScheduledOperation :
    next.provenance = stage.schedule.entry.var :: state.provenance
  provenanceFromExecution :
    next.provenance = stageSelectedVar (depth + 1) :: state.provenance
  decisionAccumulationWork : Nat
  decisionAccumulationWorkExact : decisionAccumulationWork = 1
  provenanceWork : Nat
  provenanceWorkExact : provenanceWork = provenanceRun.visits

def realizeNextOperationalState {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    NextOperationalStateRun state stage := by
  let provenanceRun :=
    prependProvenanceMeasured stage.schedule.entry.var state.provenance
  let nextGeneration :=
    generateCanonicalStageFromSource state.generation.target state.generation.targetExact
  let executedDecision := executedBranchDecision stage
  have executedDecisionHolds :
      stage.next.assignment executedDecision.var = executedDecision.value := by
    unfold executedDecision executedBranchDecision
    exact congrArg
      (fun produced => produced (stageSelectedVar (depth + 1)))
      stage.nextAssignmentExact
  have oldHold : StructuralDecisionsHold stage.next.assignment state.decisions :=
    stageNext_preserves_threadedDecisions state stage avoid
  let next : ThreadedConstitutiveState (depth + 1) stage.next :=
    { threadedAssignment := stage.next
      threadedAssignmentExact := rfl
      generation := nextGeneration
      searchSeed := executedProducedSearchSeed stage
      searchSeedExact := by
        calc
          executedProducedSearchSeed stage =
              (constructStage ((depth + 1) + 1)).searchIndex :=
            executedProducedSearchSeed_eq_nextSearchIndex stage
          _ = generatedSearchSeed nextGeneration :=
            (generatedSearchSeed_exact nextGeneration).symm
      decisions := executedDecision :: state.decisions
      provenance := provenanceRun.output
      provenanceExact := by
        rw [provenanceRun.outputExact, state.provenanceExact]
        unfold executedDecision executedBranchDecision
        rw [List.map, sequentialStage_selected_exact]
      decisionsHold := ⟨executedDecisionHolds, oldHold⟩ }
  exact
    { provenanceRun := provenanceRun
      next := next
      assignmentFromExecution := rfl
      searchSeedFromProducedState := rfl
      generationFromProducedTarget := rfl
      decisionsFromExecutedOutput := rfl
      decisionsFromExecution := by
        change executedDecision :: state.decisions =
          ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions
        exact congrArg (fun decision => decision :: state.decisions)
          (executedBranchDecision_eq_selected_true stage)
      provenanceFromScheduledOperation := provenanceRun.outputExact
      provenanceFromExecution := by
        calc
          next.provenance =
              stage.schedule.entry.var :: state.provenance :=
            provenanceRun.outputExact
          _ = stageSelectedVar (depth + 1) :: state.provenance := by
            rw [sequentialStage_selected_exact]
      decisionAccumulationWork := 1
      decisionAccumulationWorkExact := rfl
      provenanceWork := provenanceRun.visits
      provenanceWorkExact := rfl }

theorem ThreadedNextDiscoveryRun.extractionExact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ThreadedNextDiscoveryRun depth state) :
    run.asRecorded.extraction =
      (stageRecordedDiscoveryRun (depth + 1)).extraction := by
  unfold ThreadedNextDiscoveryRun.asRecorded
  rw [run.generatedExact]
  exact (measuredGeneratedExtraction state.generation).extractionExact

/-- One stage built only after the discovery stored here has returned `some`.
The builder receives no preconstructed `SequentialStageRun`. -/
structure ThreadedConstitutiveStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) where
  discoveryRun : ThreadedNextDiscoveryRun depth state
  discoveryRunExact : discoveryRun = runThreadedNextDiscovery state
  discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot
  discoveryFound : discoveryRun.outcome.discovered? = some discovery
  recordedDiscoveryFound : discoveryRun.asRecorded.outcome.discovered? = some discovery
  discoveryExact :
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery
  discoveryWorkLeCanonical :
    (discoveryRun.outcome.comparisonWork.add
      discoveryRun.outcome.constructionWork).total ≤
    ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
      (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total
  stageFromDiscovery :
    stage = executeSequentialStageFromActiveRecorded depth assignment state.generation
      discoveryRun.asRecorded
      discoveryRun.extractionExact
      discovery recordedDiscoveryFound discoveryExact discoveryWorkLeCanonical
  relationFromTransmittedState :
    discoveryRun.outcome.discovered? = some stage.discovery
  returnedCodeFromThatRelation : stage.execution.code = stage.schedule.entry.code
  executedOutputFromThatCode :
    stage.application.output =
      (stage.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
          stage.schedule.entry.var)).map stage.sourceContinuation
  nextRun : NextOperationalStateRun state stage

/-- The provenance produced by one executed stage is consumed directly by
the next discovery's candidate filter.  The same material list determines both
the retained candidate domain and the charged filtering visits. -/
theorem ThreadedConstitutiveStageRun.nextDiscoveryConsumesProducedProvenance
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    nextDiscovery.candidates =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).retained ∧
      nextDiscovery.filtering.visits =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).visits := by
  let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
  constructor
  · rw [nextDiscovery.candidatesExact, nextDiscovery.filteringExact,
      run.nextRun.provenanceFromScheduledOperation]
  · rw [nextDiscovery.filteringExact,
      run.nextRun.provenanceFromScheduledOperation]

/-- The search root consumed by the next discovery is built from the seed
read from the state actually produced by the preceding transport execution. -/
theorem ThreadedConstitutiveStageRun.nextDiscoveryConsumesRetainedSearchSeed
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    run.nextRun.next.searchSeed = executedProducedSearchSeed stage ∧
      nextDiscovery.generated =
        measuredGeneratedExtractionFromSeed
          run.nextRun.next.generation
          run.nextRun.next.searchSeed
          run.nextRun.next.searchSeedExact := by
  let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
  exact
    ⟨run.nextRun.searchSeedFromProducedState,
      nextDiscovery.generatedFromSearchSeed⟩

structure ConstructedThreadedStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) where
  stage : SequentialStageRun depth assignment
  run : ThreadedConstitutiveStageRun state stage

def buildThreadedConstitutiveStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery)
    (canonicalFound :
      (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical :
      (discoveryRun.outcome.comparisonWork.add
        discoveryRun.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    ConstructedThreadedStageRun state := by
  have recordedFound :
      discoveryRun.asRecorded.outcome.discovered? = some discovery := found
  let stage := executeSequentialStageFromActiveRecorded depth assignment state.generation
    discoveryRun.asRecorded
    discoveryRun.extractionExact discovery recordedFound canonicalFound workLeCanonical
  exact
    { stage := stage
      run :=
        { discoveryRun := discoveryRun
          discoveryRunExact := discoveryRunExact
          discovery := discovery
          discoveryFound := found
          recordedDiscoveryFound := recordedFound
          discoveryWorkLeCanonical := workLeCanonical
          stageFromDiscovery := rfl
          discoveryExact := canonicalFound
          relationFromTransmittedState := by
            change discoveryRun.asRecorded.outcome.discovered? = some stage.discovery
            exact stage.discoveryRunFound
          returnedCodeFromThatRelation := executedDiscoverySchedule_code stage.execution
          executedOutputFromThatCode := stage.application.outputExact
          nextRun := realizeNextOperationalState state stage avoid } }

/-- Failure-aware active stage builder.  The `none` branch constructs no
stage, code, or next state. -/
def executeThreadedConstitutiveStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    Option (ConstructedThreadedStageRun state) := by
  let discoveryRun := runThreadedNextDiscovery state
  exact match found : discoveryRun.outcome.discovered? with
  | none => none
  | some discovery =>
      some (buildThreadedConstitutiveStage state discoveryRun rfl discovery found
        (by rw [← runThreadedNextDiscovery_discovered_exact state fresh]; exact found)
        (runThreadedNextDiscovery_work_le_canonical state fresh)
        (state.decisionsAvoidNext fresh))

theorem NextOperationalStateRun.fresh {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : NextOperationalStateRun state stage)
    (fresh : ThreadedStateFreshForNext state) :
    ThreadedStateFreshForNext run.next := by
  intro decision member
  rw [run.decisionsFromExecution] at member
  cases member with
  | head =>
      rw [stageSelectedVar_succ]
      exact Nat.lt_add_of_pos_right (by decide)
  | tail _ prior =>
      exact Nat.lt_trans (fresh decision prior)
        (by rw [stageSelectedVar_succ]; exact Nat.lt_add_of_pos_right (by decide))

theorem NextOperationalStateRun.generationCanonical {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : NextOperationalStateRun state stage) :
    run.next.generation = generateCanonicalStage (depth + 1) := by
  rw [run.generationFromProducedTarget]
  exact generateCanonicalStageFromSource_exact _ _

/-- The active history is produced directly from the current state.  Its tail
is indexed by exactly the state produced by its head. -/
inductive ConstitutiveExecutionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment) :
      ConstitutiveExecutionHistory (count := 0) state
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      (head : SequentialStageRun depth assignment)
      (headRun : ThreadedConstitutiveStageRun state head)
      (tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next) :
      ConstitutiveExecutionHistory (count := count + 1) state

/-- A failed discovery cannot coexist with a stage whose construction records
that same discovery as found.  No freshness hypothesis is needed: the result
follows from the data dependency carried by `ThreadedConstitutiveStageRun`. -/
theorem failedDiscovery_noStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (stage : SequentialStageRun depth assignment)
    (run : ThreadedConstitutiveStageRun state stage) : False := by
  have found :
      (runThreadedNextDiscovery state).outcome.discovered? = some run.discovery :=
    run.discoveryRunExact ▸ run.discoveryFound
  have impossible := Eq.trans failed.symm found
  nomatch impossible

/-- Consequently, failure leaves no packaged stage and no produced next state. -/
theorem failedDiscovery_noConstructedStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (built : ConstructedThreadedStageRun state) : False :=
  failedDiscovery_noStageRun state failed built.stage built.run

/-- Any authoritative history rooted at a state whose discovery failed is
necessarily empty. -/
theorem failedDiscovery_historyCount_eq_zero :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state →
      (runThreadedNextDiscovery state).outcome.discovered? = none → count = 0 := by
  intro depth count assignment state history
  induction history with
  | nil _ => intro _; rfl
  | step head headRun _ _ =>
      intro failed
      exact False.elim (failedDiscovery_noStageRun _ failed head headRun)

/-- A failed discovery therefore admits no positive-length authoritative
history: no stage, no next state, and no later discovery can descend from it. -/
theorem failedDiscovery_noPositiveHistory {depth count : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (history : ConstitutiveExecutionHistory (count := count + 1) state) : False :=
  Nat.noConfusion (failedDiscovery_historyCount_eq_zero history failed)

def ConstitutiveExecutionHistory.toSequentialHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state →
      SequentialHistory depth assignment count
  | _, _, _, _, .nil _ => .nil _ _
  | _, _, _, _, .step head headRun tailRun =>
      .step head tailRun.toSequentialHistory

/-- Generated stages are projected from the heads actually executed by the
authoritative recursion. -/
def ConstitutiveExecutionHistory.toGeneratedHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state →
      CanonicalGeneratedHistory depth count
  | _, _, _, _, .nil _ => .nil _
  | _, _, _, _, .step head _ tailRun =>
      .step head.generation tailRun.toGeneratedHistory

theorem ConstitutiveExecutionHistory.toGeneratedHistory_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state)
    (generationCanonical : state.generation = generateCanonicalStage depth) :
    run.toGeneratedHistory = produceCanonicalGeneratedHistory depth count := by
  induction run with
  | nil => rfl
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have headGeneration : head.generation = generateCanonicalStage depth := by
        exact Eq.trans
          (congrArg SequentialStageRun.generation headRun.stageFromDiscovery)
          generationCanonical
      have tailGeneration := headRun.nextRun.generationCanonical
      change CanonicalGeneratedHistory.step head.generation tailRun.toGeneratedHistory = _
      exact Eq.trans
        (congrArg (fun generation =>
          CanonicalGeneratedHistory.step generation tailRun.toGeneratedHistory)
          headGeneration)
        (congrArg (CanonicalGeneratedHistory.step (generateCanonicalStage depth))
          (inductionHypothesis tailGeneration))

structure ConstitutiveProductionStats where
  generateCalls : Nat
  appendedSteps : Nat
  provenanceUnits : Nat
  certificatesProduced : Nat
  deriving DecidableEq, Repr

def ConstitutiveProductionStats.zero : ConstitutiveProductionStats := ⟨0, 0, 0, 0⟩

def ConstitutiveProductionStats.addGeneration (stats : ConstitutiveProductionStats)
    {depth : Nat} (generation : CanonicalStageGeneration depth) :
    ConstitutiveProductionStats :=
  ⟨stats.generateCalls + generation.generateCalls,
    stats.appendedSteps + generation.generatedSteps,
    stats.provenanceUnits + generation.provenanceUnits,
    stats.certificatesProduced + generation.certificatesProduced⟩

def ConstitutiveExecutionHistory.productionStats :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state → ConstitutiveProductionStats
  | _, _, _, _, .nil _ => .zero
  | _, _, _, _, .step head _ tailRun =>
      tailRun.productionStats.addGeneration head.generation

def ConstitutiveExecutionHistory.toProductionRun
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state)
    (generationCanonical : state.generation = generateCanonicalStage depth) :
    ConstitutiveProductionRun depth count :=
  { history := run.toGeneratedHistory
    historyExact := run.toGeneratedHistory_exact generationCanonical
    generateCalls := run.productionStats.generateCalls
    appendedSteps := run.productionStats.appendedSteps
    provenanceUnits := run.productionStats.provenanceUnits
    certificatesProduced := run.productionStats.certificatesProduced }

def ConstitutiveExecutionHistory.toDiscoveryTraversal :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (run : ConstitutiveExecutionHistory (count := count) state) →
      GeneratedHistoryTraversalResult depth assignment count
  | _, _, _, _, .nil _ =>
      { execution? := some (.nil _ _)
        discoveryRuns := 0
        successfulDiscoveries := 0
        failureDepth? := none
        realizationWork := .zero }
  | _, _, _, _, .step head headRun tailRun =>
      let tail := tailRun.toDiscoveryTraversal
      { execution? := some (.step head tailRun.toSequentialHistory)
        discoveryRuns := tail.discoveryRuns + 1
        successfulDiscoveries := tail.successfulDiscoveries + 1
        failureDepth? := none
        realizationWork :=
          headRun.discoveryRun.generated.realizationWork.add tail.realizationWork }

theorem ConstitutiveExecutionHistory.toDiscoveryTraversal_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    let traversal := run.toDiscoveryTraversal
    traversal.execution? = some run.toSequentialHistory ∧
      traversal.discoveryRuns = count ∧
      traversal.successfulDiscoveries = count ∧
      traversal.failureDepth? = none := by
  induction run with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | step head headRun tailRun inductionHypothesis =>
      exact
        ⟨rfl,
          congrArg (fun value => value + 1) inductionHypothesis.2.1,
          congrArg (fun value => value + 1) inductionHypothesis.2.2.1,
          rfl⟩

def ConstitutiveExecutionHistory.toAcceptedHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (run : ConstitutiveExecutionHistory (count := count) state) →
      AcceptedSequentialHistory run.toSequentialHistory
  | _, _, _, _, .nil _ => .nil _ _
  | _, _, _, _, .step head _ tailRun =>
      .step head tailRun.toSequentialHistory tailRun.toAcceptedHistory

/-- The material producer counters are projections of the same recursive
execution that generated and executed the stages. -/
theorem ConstitutiveExecutionHistory.productionStats_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state)
    (generationCanonical : state.generation = generateCanonicalStage depth) :
    run.productionStats.generateCalls = count ∧
      run.productionStats.appendedSteps = count ∧
      run.productionStats.provenanceUnits = count ∧
      run.productionStats.certificatesProduced = count := by
  induction run with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have headGeneration : head.generation = generateCanonicalStage depth :=
        Eq.trans (congrArg SequentialStageRun.generation headRun.stageFromDiscovery)
          generationCanonical
      have tailExact := inductionHypothesis headRun.nextRun.generationCanonical
      dsimp only [ConstitutiveExecutionHistory.productionStats,
        ConstitutiveProductionStats.addGeneration]
      rw [tailExact.1, tailExact.2.1, tailExact.2.2.1, tailExact.2.2.2,
        headGeneration]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- Stage-local unit counters and generation counters folded from the unique
causal run. -/
theorem ConstitutiveExecutionHistory.coreStats_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state)
    (generationCanonical : state.generation = generateCanonicalStage depth) :
    let stats := run.toSequentialHistory.stats
    stats.generateCalls = count ∧
      stats.generatedSteps = count ∧
      stats.provenanceUnits = count ∧
      stats.generationCertificates = count ∧
      stats.scheduleAtoms = count ∧
      stats.validationPrimitiveQueries = count ∧
      stats.executionPrimitiveQueries = count ∧
      stats.compositionCandidates = 0 ∧
      stats.appliedCodeAtoms = count := by
  induction run with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have headGeneration : head.generation = generateCanonicalStage depth :=
        Eq.trans (congrArg SequentialStageRun.generation headRun.stageFromDiscovery)
          generationCanonical
      have tailExact := inductionHypothesis headRun.nextRun.generationCanonical
      have generationExact :
          head.stats.generateCalls = 1 ∧
            head.stats.generatedSteps = 1 ∧
            head.stats.provenanceUnits = 1 ∧
            head.stats.generationCertificates = 1 := by
        dsimp only [SequentialStageRun.stats]
        rw [headGeneration]
        exact ⟨rfl, rfl, rfl, rfl⟩
      have localExact := head.localStats
      dsimp only [ConstitutiveExecutionHistory.toSequentialHistory,
        SequentialHistory.stats, SequentialHistoryStats.addStage]
      rw [tailExact.1, tailExact.2.1, tailExact.2.2.1, tailExact.2.2.2.1,
        tailExact.2.2.2.2.1, tailExact.2.2.2.2.2.1,
        tailExact.2.2.2.2.2.2.1, tailExact.2.2.2.2.2.2.2.1,
        tailExact.2.2.2.2.2.2.2.2,
        generationExact.1, generationExact.2.1,
        generationExact.2.2.1, generationExact.2.2.2,
        localExact.1, localExact.2.1, localExact.2.2.1,
        localExact.2.2.2.1, localExact.2.2.2.2]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ConstitutiveExecutionHistory.controlStats_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    let stats := run.toSequentialHistory.stats
    stats.extractedCandidates = stats.extractionLiteralVisits ∧
      stats.discoveryAttempts ≤ stats.extractedCandidates ∧
      stats.validatedAtoms = count := by
  induction run with
  | nil => exact ⟨rfl, Nat.le_refl 0, rfl⟩
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have headExtraction :
          head.stats.extractedCandidates = head.stats.extractionLiteralVisits := by
        change head.discoveryRun.extraction.stats.candidatesEmitted =
          head.discoveryRun.extraction.stats.literalVisits
        rw [head.extractionExact]
        exact runCandidateExtraction_candidatesEmitted _
      have activeOutcome :
          head.discoveryRun.outcome = headRun.discoveryRun.outcome := by
        calc
          head.discoveryRun.outcome =
              (executeSequentialStageFromActiveRecorded _ _ _
                headRun.discoveryRun.asRecorded
                headRun.discoveryRun.extractionExact headRun.discovery
                headRun.recordedDiscoveryFound headRun.discoveryExact
                headRun.discoveryWorkLeCanonical).discoveryRun.outcome :=
            congrArg (fun stage => stage.discoveryRun.outcome)
              headRun.stageFromDiscovery
          _ = headRun.discoveryRun.outcome := rfl
      have activeExtraction :
          head.discoveryRun.extraction =
            headRun.discoveryRun.generated.extraction := by
        calc
          head.discoveryRun.extraction =
              (executeSequentialStageFromActiveRecorded _ _ _
                headRun.discoveryRun.asRecorded
                headRun.discoveryRun.extractionExact headRun.discovery
                headRun.recordedDiscoveryFound headRun.discoveryExact
                headRun.discoveryWorkLeCanonical).discoveryRun.extraction :=
            congrArg (fun stage => stage.discoveryRun.extraction)
              headRun.stageFromDiscovery
          _ = headRun.discoveryRun.generated.extraction := rfl
      have headAttempts :
          head.stats.discoveryAttempts ≤ head.stats.extractedCandidates := by
        change head.discoveryRun.outcome.attempts ≤
          head.discoveryRun.extraction.stats.candidatesEmitted
        rw [activeOutcome, activeExtraction]
        have attempted := exploreRecordedCandidates_attempts_le_length
          (constructStage (depth + 1)).operationalRoot
          headRun.discoveryRun.candidates
        rw [← headRun.discoveryRun.outcomeExact] at attempted
        have retained := filterCandidatesByProvenance_retained_length_le
          state.provenance headRun.discoveryRun.generated.extraction.candidates
        rw [← headRun.discoveryRun.filteringExact,
          ← headRun.discoveryRun.candidatesExact] at retained
        have emitted :
            headRun.discoveryRun.generated.extraction.candidates.length =
              headRun.discoveryRun.generated.extraction.stats.candidatesEmitted := by
          rw [headRun.discoveryRun.generated.extractionExact]
          exact runCandidateExtraction_length _
        exact Nat.le_trans attempted (Nat.le_trans retained (Nat.le_of_eq emitted))
      have headValidated : head.stats.validatedAtoms = 1 := by
        change head.validated.run.validatedAtoms = 1
        rw [head.validated.runExact]
        exact runDiscoveryScheduleValidation_validatedAtoms _
      dsimp only [ConstitutiveExecutionHistory.toSequentialHistory,
        SequentialHistory.stats, SequentialHistoryStats.addStage]
      constructor
      · rw [inductionHypothesis.1, headExtraction]
      · constructor
        · exact Nat.add_le_add inductionHypothesis.2.1 headAttempts
        · rw [inductionHypothesis.2.2, headValidated]

theorem ConstitutiveExecutionHistory.continuationApplications_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.stats.continuationApplications = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      have headExact : head.stats.continuationApplications = 1 := by
        change head.application.continuationApplications = 1
        exact Eq.trans head.application.continuationApplicationsExact
          (by rw [executedDiscoverySchedule_code head.execution]
              exact ConstitutedLocalWitness.code_size head.schedule.entry)
      change tailRun.toSequentialHistory.stats.continuationApplications +
        head.stats.continuationApplications = _
      rw [inductionHypothesis, headExact]

theorem ConstitutiveExecutionHistory.testedCandidates_eq_attempts
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.stats.testedCandidates =
      run.toSequentialHistory.stats.discoveryAttempts := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      have activeOutcome : head.discoveryRun.outcome = headRun.discoveryRun.outcome := by
        calc
          head.discoveryRun.outcome =
              (executeSequentialStageFromActiveRecorded _ _ _
                headRun.discoveryRun.asRecorded
                headRun.discoveryRun.extractionExact headRun.discovery
                headRun.recordedDiscoveryFound headRun.discoveryExact
                headRun.discoveryWorkLeCanonical).discoveryRun.outcome :=
            congrArg (fun stage => stage.discoveryRun.outcome)
              headRun.stageFromDiscovery
          _ = headRun.discoveryRun.outcome := rfl
      change tailRun.toSequentialHistory.stats.testedCandidates +
          head.discoveryRun.outcome.testedCandidates.length =
        tailRun.toSequentialHistory.stats.discoveryAttempts +
          head.discoveryRun.outcome.attempts
      rw [inductionHypothesis, activeOutcome, headRun.discoveryRun.outcomeExact,
        exploreRecordedCandidates_tested_length]

theorem ConstitutiveExecutionHistory.relationQueries_eq_attempts
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.stats.relationQueries =
      run.toSequentialHistory.stats.discoveryAttempts := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      have activeOutcome : head.discoveryRun.outcome = headRun.discoveryRun.outcome := by
        calc
          head.discoveryRun.outcome =
              (executeSequentialStageFromActiveRecorded _ _ _
                headRun.discoveryRun.asRecorded
                headRun.discoveryRun.extractionExact headRun.discovery
                headRun.recordedDiscoveryFound headRun.discoveryExact
                headRun.discoveryWorkLeCanonical).discoveryRun.outcome :=
            congrArg (fun stage => stage.discoveryRun.outcome)
              headRun.stageFromDiscovery
          _ = headRun.discoveryRun.outcome := rfl
      change tailRun.toSequentialHistory.stats.relationQueries +
          head.discoveryRun.outcome.relationQueries =
        tailRun.toSequentialHistory.stats.discoveryAttempts +
          head.discoveryRun.outcome.attempts
      rw [inductionHypothesis, activeOutcome, headRun.discoveryRun.outcomeExact,
        (exploreRecordedCandidates_work_exact
          (constructStage (_ + 1)).operationalRoot
          headRun.discoveryRun.candidates).2.2.2.2]

theorem ConstitutiveExecutionHistory.executedBits_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.executedBits = List.replicate count true := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      change head.application.output.1 head.schedule.entry.var ::
          tailRun.toSequentialHistory.executedBits = _
      rw [head.output_selected, inductionHypothesis, List.replicate_succ]

theorem ConstitutiveExecutionHistory.executedBits_length
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.toSequentialHistory.executedBits.length = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      change Nat.succ tailRun.toSequentialHistory.executedBits.length =
        Nat.succ _
      exact congrArg Nat.succ inductionHypothesis

def executeConstitutiveExecutionHistory
    (count : Nat) : {depth : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      ThreadedStateFreshForNext state →
      ConstitutiveExecutionHistory (count := count) state
  | _, _, state, fresh => match count with
    | 0 => .nil state
    | count + 1 =>
        let discoveryRun := runThreadedNextDiscovery state
        match found : discoveryRun.outcome.discovered? with
        | none => False.elim ((runThreadedNextDiscovery_found state fresh) found)
        | some discovery =>
            let built := buildThreadedConstitutiveStage state discoveryRun rfl discovery found
              (by rw [← runThreadedNextDiscovery_discovered_exact state fresh]; exact found)
              (runThreadedNextDiscovery_work_le_canonical state fresh)
              (state.decisionsAvoidNext fresh)
            .step built.stage built.run
              (executeConstitutiveExecutionHistory count built.run.nextRun.next
                (built.run.nextRun.fresh fresh))

/-- Accounting emitted by the feedback recursion itself.  Extraction and
next-discovery work remain owned by the existing extraction/discovery phases;
they are not added again here. -/
structure ConstitutiveFeedbackStats where
  decisionAccumulations : Nat
  provenanceVisits : Nat
  historyFilteringVisits : Nat
  deriving DecidableEq, Repr

def ConstitutiveFeedbackStats.zero : ConstitutiveFeedbackStats := ⟨0, 0, 0⟩

def ConstitutiveFeedbackStats.addStage (stats : ConstitutiveFeedbackStats)
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : ConstitutiveFeedbackStats :=
  { decisionAccumulations := stats.decisionAccumulations + run.nextRun.decisionAccumulationWork
    provenanceVisits := stats.provenanceVisits + run.nextRun.provenanceWork
    historyFilteringVisits :=
      stats.historyFilteringVisits + run.discoveryRun.filtering.visits }

def ConstitutiveExecutionHistory.feedbackStats :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state → ConstitutiveFeedbackStats
  | _, _, _, _, .nil _ => .zero
  | _, _, _, _, .step _ headRun tailRun =>
      tailRun.feedbackStats.addStage headRun

theorem ConstitutiveExecutionHistory.decisionAccumulations_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.decisionAccumulations = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.decisionAccumulationWorkExact]

theorem ConstitutiveExecutionHistory.provenanceVisits_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.provenanceVisits = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.provenanceWorkExact,
        headRun.nextRun.provenanceRun.visitsExact]

theorem ConstitutiveExecutionHistory.inspections_bound
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.historyFilteringVisits ≤
      count * ((2 * (depth + count) + 13) *
        (state.decisions.length + count)) := by
  induction run with
  | nil => exact Nat.zero_le _
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have nextLength : headRun.nextRun.next.decisions.length = state.decisions.length + 1 :=
        Eq.trans
          (congrArg List.length headRun.nextRun.decisionsFromExecution)
          (Eq.refl (state.decisions.length + 1))
      have filteringBound : headRun.discoveryRun.filtering.visits ≤
          (2 * depth + 13) * state.decisions.length := by
        have generic := filterCandidatesByProvenance_visits_le
          state.provenance headRun.discoveryRun.generated.extraction.candidates
        have candidateLength :
            headRun.discoveryRun.generated.extraction.candidates.length =
              2 * depth + 13 := by
          rw [headRun.discoveryRun.generatedExact]
          rw [(measuredGeneratedExtraction state.generation).extractionExact]
          unfold stageRecordedDiscoveryRun runRecordedDiscovery
          dsimp only
          rw [runCandidateExtraction_length_exact]
          change
            (stageRecordedDiscoveryRun (depth + 1)).extraction.stats.candidatesEmitted =
              2 * depth + 13
          exact executeSequentialStage_extractedCandidates depth assignment
        have provenanceLength :
            state.provenance.length = state.decisions.length :=
          Eq.trans
            (congrArg List.length state.provenanceExact)
            (listMapLengthConstructive
              (fun decision : StructuralBranchDecision => decision.var)
              state.decisions)
        have filteringExact :=
          congrArg CandidateProvenanceFilterRun.visits
            headRun.discoveryRun.filteringExact
        have lengthProduct :
            headRun.discoveryRun.generated.extraction.candidates.length *
                state.provenance.length =
              (2 * depth + 13) * state.decisions.length := by
          exact Eq.trans
            (congrArg
              (fun length => length * state.provenance.length)
              candidateLength)
            (congrArg
              (fun length => (2 * depth + 13) * length)
              provenanceLength)
        calc
          headRun.discoveryRun.filtering.visits =
              (filterCandidatesByProvenance state.provenance
                headRun.discoveryRun.generated.extraction.candidates).visits :=
            filteringExact
          _ ≤ headRun.discoveryRun.generated.extraction.candidates.length *
                state.provenance.length :=
            generic
          _ = (2 * depth + 13) * state.decisions.length :=
            lengthProduct
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      have sameEnvelope :
          2 * ((depth + 1) + count) + 13 =
            2 * (depth + (count + 1)) + 13 := by
        have indices : (depth + 1) + count = depth + (count + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 count]
        exact congrArg (fun index => 2 * index + 13) indices
      have sameDecisions :
          headRun.nextRun.next.decisions.length + count =
            state.decisions.length + (count + 1) := by
        rw [nextLength, Nat.add_assoc, Nat.add_comm 1 count]
      calc
        _ ≤ count * ((2 * ((depth + 1) + count) + 13) *
              (headRun.nextRun.next.decisions.length + count)) +
              ((2 * depth + 13) * state.decisions.length) :=
          Nat.add_le_add inductionHypothesis filteringBound
        _ ≤ (count + 1) * ((2 * (depth + (count + 1)) + 13) *
              (state.decisions.length + (count + 1))) := by
          let envelope := (2 * (depth + (count + 1)) + 13) *
            (state.decisions.length + (count + 1))
          have tailFactor :
              (2 * ((depth + 1) + count) + 13) *
                  (headRun.nextRun.next.decisions.length + count) ≤ envelope := by
            apply Nat.mul_le_mul
            · exact Nat.le_of_eq sameEnvelope
            · exact Nat.le_of_eq sameDecisions
          have tailTotal :
              count * ((2 * ((depth + 1) + count) + 13) *
                (headRun.nextRun.next.decisions.length + count)) ≤
                count * envelope := Nat.mul_le_mul_left count tailFactor
          have stageFactor : (2 * depth + 13) * state.decisions.length ≤ envelope := by
            apply Nat.mul_le_mul
            · exact Nat.add_le_add_right
                (Nat.mul_le_mul_left 2 (Nat.le_add_right depth (count + 1))) 13
            · exact Nat.le_add_right state.decisions.length (count + 1)
          calc
            _ ≤ count * envelope + envelope := Nat.add_le_add tailTotal stageFactor
            _ = (count + 1) * envelope := (Nat.succ_mul count envelope).symm

theorem executedFeedbackHistory_decisionAccumulations
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.decisionAccumulations =
      count := by
  exact (executeConstitutiveExecutionHistory count state fresh).decisionAccumulations_eq_count

theorem executedFeedbackHistory_provenanceVisits
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.provenanceVisits =
      count := by
  exact (executeConstitutiveExecutionHistory count state fresh).provenanceVisits_eq_count

theorem executedFeedbackHistory_inspections_bound
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.historyFilteringVisits ≤
      count * ((2 * (depth + count) + 13) *
        (state.decisions.length + count)) := by
  exact (executeConstitutiveExecutionHistory count state fresh).inspections_bound

/-- Four-role reading of one feedback stage. -/
structure ThreadedConstitutiveRoleStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) where
  searchState : ThreadedConstitutiveState depth assignment
  searchStateExact : searchState = state
  structuralOpening : AcceptingExactBinarySplit
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
    (constructStage (depth + 1)).operationalRoot
    ((constructStage (depth + 1)).operationalRoot.child stage.discovery.var false stage.discovery.fresh)
    ((constructStage (depth + 1)).operationalRoot.child stage.discovery.var true stage.discovery.fresh)
  executedDecision : StructuralBranchDecision
  decisionFromExecution : executedDecision = executedBranchDecision stage
  executedDecisionExact : executedDecision = ⟨stageSelectedVar (depth + 1), true⟩
  reconstructedRelationComesFromTransmittedState :
    run.discoveryRun.outcome.discovered? = some stage.discovery
  pExecutionProducesContinuation :
    stage.application.output =
      (stage.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
          stage.schedule.entry.var)).map stage.sourceContinuation
  nextNpState : ThreadedConstitutiveState (depth + 1) stage.next
  nextNpStateExact : nextNpState = run.nextRun.next

def threadedConstitutiveRoleStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ThreadedConstitutiveRoleStage run :=
  { searchState := state
    searchStateExact := rfl
    structuralOpening := generatedStructuralSplit
      (constructStage (depth + 1)).operationalRoot stage.discovery.var stage.discovery.fresh
    executedDecision := executedBranchDecision stage
    decisionFromExecution := rfl
    executedDecisionExact := executedBranchDecision_eq_selected_true stage
    reconstructedRelationComesFromTransmittedState := run.relationFromTransmittedState
    pExecutionProducesContinuation := run.executedOutputFromThatCode
    nextNpState := run.nextRun.next
    nextNpStateExact := rfl }

theorem roleStage_decision_reads_executedOutput {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (threadedConstitutiveRoleStage run).executedDecision =
      ⟨stageSelectedVar (depth + 1),
        stage.application.output.1 (stageSelectedVar (depth + 1))⟩ := by
  rfl

theorem roleStage_output_constitutes_nextOperationalState {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.threadedAssignment.assignment = stage.application.output.1 ∧
      run.nextRun.next.decisions =
        ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions ∧
      run.nextRun.next.provenance =
        stageSelectedVar (depth + 1) :: state.provenance := by
  refine ⟨?_, run.nextRun.decisionsFromExecution, run.nextRun.provenanceFromExecution⟩
  rw [run.nextRun.assignmentFromExecution]
  exact stage.nextAssignmentExact

/-- The four-role reading follows the same dependent tail as the operational
feedback history; no independent role history can be injected. -/
inductive ThreadedConstitutiveRoleHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (run : ConstitutiveExecutionHistory (count := count) state) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      ThreadedConstitutiveRoleHistory (ConstitutiveExecutionHistory.nil state)
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
      ThreadedConstitutiveRoleHistory
        (ConstitutiveExecutionHistory.step head headRun tailRun)

def buildThreadedConstitutiveRoleHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (run : ConstitutiveExecutionHistory (count := count) state) →
      ThreadedConstitutiveRoleHistory run
  | _, _, _, _, .nil _ => .nil
  | _, _, _, _, .step _ headRun tailRun =>
      .step (threadedConstitutiveRoleStage headRun)
        (buildThreadedConstitutiveRoleHistory tailRun)

/-- The common executed origin used by both sides of the separator.  Its stage
is built from the returned discovery by the same active builder as the public
recursion. -/
def nextDiscoveryCommonOrigin (depth : Nat) :
    ConstructedThreadedStageRun (initialThreadedConstitutiveState depth) := by
  let state := initialThreadedConstitutiveState depth
  let discoveryRun := runThreadedNextDiscovery state
  let discovery := canonicalStageDiscovery (depth + 1)
  have found : discoveryRun.outcome.discovered? = some discovery := by
    rw [runThreadedNextDiscovery_discovered_exact state
      (initialThreadedConstitutiveState_fresh depth)]
    exact canonicalStageDiscovery_found (depth + 1)
  exact buildThreadedConstitutiveStage state discoveryRun rfl discovery found
    (canonicalStageDiscovery_found (depth + 1))
    (runThreadedNextDiscovery_work_le_canonical state
      (initialThreadedConstitutiveState_fresh depth))
    (state.decisionsAvoidNext (initialThreadedConstitutiveState_fresh depth))

/-- The blocking operation is a genuine generated child of the target produced
by the common executed stage.  Offset `2` is exactly the next stage variable. -/
def blockedNextDiscoveryChild (depth : Nat) :=
  integratedMarkedTarget (nextDiscoveryCommonOrigin depth).stage 2 (by decide)

/-- Existentially package the assignment index with a complete valid state. -/
structure PackedThreadedConstitutiveState (depth : Nat) where
  assignment : SequentialAssignment depth
  state : ThreadedConstitutiveState depth assignment

def retainedNextDiscoveryState (depth : Nat) :
    PackedThreadedConstitutiveState (depth + 1) :=
  let origin := nextDiscoveryCommonOrigin depth
  ⟨origin.stage.next, origin.run.nextRun.next⟩

/-- Erase only the accumulated decision history from the state genuinely returned
by the common executed stage.  Assignment, reader and generated target remain
those of that reachable state. -/
def erasedNextDiscoveryState (depth : Nat) :
    PackedThreadedConstitutiveState (depth + 1) :=
  let retained := retainedNextDiscoveryState depth
  ⟨retained.assignment,
    { threadedAssignment := retained.state.threadedAssignment
      threadedAssignmentExact := retained.state.threadedAssignmentExact
      generation := retained.state.generation
      searchSeed := retained.state.searchSeed
      searchSeedExact := retained.state.searchSeedExact
      decisions := []
      provenance := []
      provenanceExact := rfl
      decisionsHold := True.intro }⟩

theorem distinctDecoyVariables_mem_of_lt (candidate : Var) :
    ∀ count, candidate < count → candidate ∈ distinctDecoyVariables count
  | 0, before => False.elim (Nat.not_lt_zero candidate before)
  | count + 1, before => by
      change candidate ∈ count :: distinctDecoyVariables count
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with
      | inl below =>
          exact List.Mem.tail _ (distinctDecoyVariables_mem_of_lt candidate count below)
      | inr same => cases same; exact List.Mem.head _

theorem provenanceAvoidCheck_false_of_mem (candidate : Var) :
    ∀ provenance : List Var, candidate ∈ provenance →
      provenanceAvoidCheck candidate provenance = false
  | [], member => by cases member
  | prior :: rest, member => by
      rw [provenanceAvoidCheck]
      split
      · rfl
      · cases member with
        | head => contradiction
        | tail _ priorMember =>
            exact provenanceAvoidCheck_false_of_mem candidate rest priorMember

theorem provenanceAvoidCheck_false_implies_mem (candidate : Var) :
    ∀ provenance : List Var,
      provenanceAvoidCheck candidate provenance = false → candidate ∈ provenance
  | [], failed => by contradiction
  | prior :: rest, failed => by
      rw [provenanceAvoidCheck] at failed
      by_cases same : prior = candidate
      · cases same
        exact List.Mem.head rest
      · rw [if_neg same] at failed
        exact List.Mem.tail _
          (provenanceAvoidCheck_false_implies_mem candidate rest failed)

theorem provenanceAvoidCheck_true_of_not_mem (candidate : Var) :
    ∀ provenance : List Var, candidate ∉ provenance →
      provenanceAvoidCheck candidate provenance = true
  | [], _ => rfl
  | prior :: rest, absent => by
      rw [provenanceAvoidCheck]
      have different : prior ≠ candidate := by
        intro same
        cases same
        exact absent (List.Mem.head rest)
      rw [if_neg different]
      apply provenanceAvoidCheck_true_of_not_mem candidate rest
      intro member
      exact absent (List.Mem.tail prior member)

theorem filteredList_nodup {alpha : Type} (predicate : alpha → Bool) :
    ∀ values : List alpha, values.Nodup → (values.filter predicate).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases nodup with
      | cons headAbsent tailNodup =>
      rw [List.filter]
      split
      · apply List.Pairwise.cons
        · intro candidate member
          exact headAbsent candidate
            (memberOfFilter_original predicate candidate tail member)
        · exact filteredList_nodup predicate tail tailNodup
      · exact filteredList_nodup predicate tail tailNodup

/-- Executable removal used only by the constructive cardinality argument. -/
def removeFirstVar (target : Var) : List Var → List Var
  | [] => []
  | head :: tail => if head = target then tail else head :: removeFirstVar target tail

theorem removeFirstVar_member_original (target value : Var) :
    ∀ values, value ∈ removeFirstVar target values → value ∈ values
  | [], member => by cases member
  | head :: tail, member => by
      rw [removeFirstVar] at member
      split at member
      · exact List.Mem.tail head member
      · cases member with
        | head => exact List.Mem.head tail
        | tail _ prior =>
            exact List.Mem.tail head
              (removeFirstVar_member_original target value tail prior)

theorem removeFirstVar_preserves_other (target value : Var)
    (different : value ≠ target) :
    ∀ values, value ∈ values → value ∈ removeFirstVar target values
  | [], member => by cases member
  | head :: tail, member => by
      rw [removeFirstVar]
      by_cases same : head = target
      · rw [if_pos same]
        cases member with
        | head => exact False.elim (different same)
        | tail _ prior => exact prior
      · rw [if_neg same]
        cases member with
        | head => exact List.Mem.head _
        | tail _ prior =>
            exact List.Mem.tail _
              (removeFirstVar_preserves_other target value different tail prior)

theorem removeFirstVar_length_plus_one (target : Var) :
    ∀ values, target ∈ values →
      (removeFirstVar target values).length + 1 = values.length
  | [], member => by cases member
  | head :: tail, member => by
      rw [removeFirstVar]
      by_cases same : head = target
      · rw [if_pos same]
        rfl
      · rw [if_neg same]
        cases member with
        | head => exact False.elim (same rfl)
        | tail _ prior =>
            change (removeFirstVar target tail).length + 1 + 1 = tail.length + 1
            exact congrArg (fun length => length + 1)
              (removeFirstVar_length_plus_one target tail prior)

theorem removeFirstVar_nodup (target : Var) :
    ∀ values, values.Nodup → (removeFirstVar target values).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases nodup with
      | cons headAbsent tailNodup =>
        rw [removeFirstVar]
        by_cases same : head = target
        · rw [if_pos same]
          exact tailNodup
        · rw [if_neg same]
          apply List.Pairwise.cons
          · intro value member
            exact headAbsent value
              (removeFirstVar_member_original target value tail member)
          · exact removeFirstVar_nodup target tail tailNodup

theorem removeFirstVar_excludes_target (target : Var) :
    ∀ values, values.Nodup → target ∉ removeFirstVar target values
  | [], _, member => by cases member
  | head :: tail, nodup, member => by
      cases nodup with
      | cons headAbsent tailNodup =>
        rw [removeFirstVar] at member
        by_cases same : head = target
        · rw [if_pos same] at member
          cases same
          exact (headAbsent target member) rfl
        · rw [if_neg same] at member
          cases member with
          | head => exact same rfl
          | tail _ prior =>
              exact removeFirstVar_excludes_target target tail tailNodup prior

/-- Constructive finite-cardinality comparison.  The proof removes one
explicit witness at a time and does not pass through finite sets or quotients. -/
theorem nodupVarLists_sameLength_of_mutualMembership :
    ∀ (left right : List Var), left.Nodup → right.Nodup →
      (∀ value, value ∈ left → value ∈ right) →
      (∀ value, value ∈ right → value ∈ left) →
      left.length = right.length
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, _, rightToLeft => by
      have impossible := rightToLeft head (List.Mem.head tail)
      cases impossible
  | head :: tail, right, leftNodup, rightNodup, leftToRight, rightToLeft => by
      cases leftNodup with
      | cons headAbsent tailNodup =>
        have headInRight : head ∈ right :=
          leftToRight head (List.Mem.head tail)
        have tailToRemoved : ∀ value, value ∈ tail →
            value ∈ removeFirstVar head right := by
          intro value member
          exact removeFirstVar_preserves_other head value
            (Ne.symm (headAbsent value member)) right
            (leftToRight value (List.Mem.tail head member))
        have removedToTail : ∀ value, value ∈ removeFirstVar head right →
            value ∈ tail := by
          intro value member
          have valueInRight := removeFirstVar_member_original head value right member
          have valueInLeft := rightToLeft value valueInRight
          cases valueInLeft with
          | head =>
              exact False.elim
                (removeFirstVar_excludes_target head right rightNodup member)
          | tail _ prior => exact prior
        have tailLength := nodupVarLists_sameLength_of_mutualMembership
          tail (removeFirstVar head right) tailNodup
          (removeFirstVar_nodup head right rightNodup)
          tailToRemoved removedToTail
        have removedLength := removeFirstVar_length_plus_one head right headInRight
        exact Eq.trans (congrArg (fun length => length + 1) tailLength) removedLength

/-- Filtering by a Boolean predicate and by its Boolean complement partitions
the input length, proved directly by structural recursion. -/
theorem filter_complement_lengths (predicate : alpha → Bool) :
    ∀ values : List alpha,
      (values.filter predicate).length +
        (values.filter (fun value => !(predicate value))).length = values.length
  | [] => rfl
  | head :: tail => by
      rw [List.filter, List.filter]
      cases checked : predicate head with
      | false =>
          change (tail.filter predicate).length +
              ((head :: tail.filter (fun value => !(predicate value)))).length =
            tail.length + 1
          simp only [List.length_cons]
          have prior := filter_complement_lengths predicate tail
          rw [← Nat.add_assoc, prior]
      | true =>
          change ((head :: tail.filter predicate)).length +
              (tail.filter (fun value => !(predicate value))).length =
            tail.length + 1
          simp only [List.length_cons]
          have prior := filter_complement_lengths predicate tail
          rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, prior]

theorem filter_append_constructive (predicate : alpha → Bool) :
    ∀ (left right : List alpha),
      (left ++ right).filter predicate =
        left.filter predicate ++ right.filter predicate
  | [], _ => rfl
  | head :: tail, right => by
      rw [List.cons_append, List.filter, List.filter]
      split
      · exact congrArg (List.cons head)
          (filter_append_constructive predicate tail right)
      · exact filter_append_constructive predicate tail right

theorem rejectedCandidates_length_eq_provenance
    (candidates provenance : List Var)
    (candidatesNodup : candidates.Nodup)
    (provenanceNodup : provenance.Nodup)
    (contained : ∀ candidate, candidate ∈ provenance → candidate ∈ candidates) :
    (candidates.filter (fun candidate => !(provenanceAvoidCheck candidate provenance))).length =
      provenance.length := by
  apply nodupVarLists_sameLength_of_mutualMembership
  · exact filteredList_nodup
      (fun candidate => !(provenanceAvoidCheck candidate provenance))
      candidates candidatesNodup
  · exact provenanceNodup
  · intro candidate member
    have accepted := memberOfFilter_predicate
      (fun candidate => !(provenanceAvoidCheck candidate provenance))
      candidate candidates member
    have failed : provenanceAvoidCheck candidate provenance = false := by
      cases checked : provenanceAvoidCheck candidate provenance with
      | false => rfl
      | true =>
          rw [checked] at accepted
          contradiction
    exact provenanceAvoidCheck_false_implies_mem candidate provenance failed
  · intro candidate member
    apply memberOfFilter_of_original_and_predicate
    · exact contained candidate member
    · have failed := provenanceAvoidCheck_false_of_mem candidate provenance member
      rw [failed]
      rfl

theorem retainedCandidates_length_add_provenance
    (candidates provenance : List Var)
    (candidatesNodup : candidates.Nodup)
    (provenanceNodup : provenance.Nodup)
    (contained : ∀ candidate, candidate ∈ provenance → candidate ∈ candidates) :
    (candidates.filter (fun candidate => provenanceAvoidCheck candidate provenance)).length +
      provenance.length = candidates.length := by
  have partition := filter_complement_lengths
    (fun candidate => provenanceAvoidCheck candidate provenance) candidates
  rw [rejectedCandidates_length_eq_provenance candidates provenance candidatesNodup
    provenanceNodup contained] at partition
  exact partition

theorem exploreFailuresThenSuccess_attempts
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (failures : List Var) (selected : Var) (rest : List Var)
    (allFail : ∀ candidate, candidate ∈ failures →
      (tryMeasuredCandidate state candidate).produced? = none)
    (selectedSucceeds : (tryMeasuredCandidate state selected).produced? ≠ none) :
    (exploreRecordedCandidates state (failures ++ selected :: rest)).attempts =
      failures.length + 1 := by
  induction failures with
  | nil =>
      rw [List.nil_append, exploreRecordedCandidates]
      cases found : (tryMeasuredCandidate state selected).produced? with
      | none => exact False.elim (selectedSucceeds found)
      | some produced => rfl
  | cons candidate tail inductionHypothesis =>
      rw [List.cons_append, exploreRecordedCandidates]
      rw [allFail candidate (List.Mem.head tail)]
      change
        (exploreRecordedCandidates state (tail ++ selected :: rest)).attempts + 1 =
          tail.length + 1 + 1
      rw [inductionHypothesis]
      intro prior member
      exact allFail prior (List.Mem.tail candidate member)

/-- The provenance of a canonical feedback state contains no duplicate and
remains bounded by the most recently exposed selected variable. -/
structure ThreadedProvenanceInvariant {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) : Prop where
  nodup : state.provenance.Nodup
  bounded : ∀ candidate, candidate ∈ state.provenance →
    candidate ≤ stageSelectedVar depth

theorem initialThreadedProvenanceInvariant (depth : Nat) :
    ThreadedProvenanceInvariant (initialThreadedConstitutiveState depth) := by
  constructor
  · change ([].Nodup)
    exact List.Pairwise.nil
  · intro _ impossible
    change _ ∈ [] at impossible
    cases impossible

theorem ThreadedProvenanceInvariant.next {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (invariant : ThreadedProvenanceInvariant state)
    (run : NextOperationalStateRun state stage) :
    ThreadedProvenanceInvariant run.next := by
  constructor
  · rw [run.provenanceFromExecution]
    apply List.Pairwise.cons
    · intro candidate member
      have belowCurrent := invariant.bounded candidate member
      have belowNext : stageSelectedVar depth < stageSelectedVar (depth + 1) := by
        rw [stageSelectedVar_succ]
        exact Nat.lt_add_of_pos_right (by decide)
      exact Nat.ne_of_gt (Nat.lt_of_le_of_lt belowCurrent belowNext)
    · exact invariant.nodup
  · intro candidate member
    rw [run.provenanceFromExecution] at member
    cases member with
    | head => exact Nat.le_refl _
    | tail _ prior =>
        exact Nat.le_trans (invariant.bounded _ prior)
          (by rw [stageSelectedVar_succ]; exact Nat.le_add_right _ _)

theorem selectedMeasuredCandidate_succeeds (depth : Nat) :
    (tryMeasuredCandidate (constructStage (depth + 1)).operationalRoot
      (stageSelectedVar (depth + 1))).produced? ≠ none := by
  intro failed
  let measured := tryMeasuredCandidate (constructStage (depth + 1)).operationalRoot
    (stageSelectedVar (depth + 1))
  have resultNone : measured.result = none := by
    unfold MeasuredCandidateRun.result
    rw [failed]
    rfl
  have unmeasuredNone :
      tryEndogenousFlipCandidate (constructStage (depth + 1)).operationalRoot
        (stageSelectedVar (depth + 1)) = none := by
    rw [← tryMeasuredCandidate_exact]
    exact resultNone
  exact (distinctGrowingDiscoveryUsefulCandidate_found
    (constructStage (depth + 1)).searchIndex) unmeasuredNone

/-- The attempts emitted by one authoritative discovery are exactly the
canonical decoy prefix minus the distinct variables already carried by its
produced provenance. -/
theorem threadedDiscovery_attempts_add_provenance_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (invariant : ThreadedProvenanceInvariant state) :
    (runThreadedNextDiscovery state).outcome.attempts + state.provenance.length =
      2 * depth + 10 := by
  let run := runThreadedNextDiscovery state
  let decoys :=
    distinctDecoyVariables ((constructStage (depth + 1)).searchIndex + 1)
  let retainedDecoys := decoys.filter
    (fun candidate => provenanceAvoidCheck candidate state.provenance)
  have provenanceContained : ∀ candidate, candidate ∈ state.provenance →
      candidate ∈ decoys := by
    intro candidate member
    apply distinctDecoyVariables_mem_of_lt candidate
      ((constructStage (depth + 1)).searchIndex + 1)
    have bounded := invariant.bounded candidate member
    unfold stageSelectedVar growingDiscoverySplitVar at bounded
    rw [generateCanonicalStage_searchIndex_advances]
    exact Nat.lt_succ_of_le bounded
  have retainedLength : retainedDecoys.length + state.provenance.length =
      decoys.length :=
    retainedCandidates_length_add_provenance decoys state.provenance
      (distinctDecoyVariables_nodup _) invariant.nodup provenanceContained
  have selectedAccepted :
      provenanceAvoidCheck (stageSelectedVar (depth + 1)) state.provenance = true := by
    apply provenanceAvoidCheck_true_of_not_mem
    intro member
    have bounded := invariant.bounded _ member
    exact (Nat.ne_of_lt (Nat.lt_of_le_of_lt bounded
      (by rw [stageSelectedVar_succ]; exact Nat.lt_add_of_pos_right (by decide)))) rfl
  have anchorAccepted :
      provenanceAvoidCheck (stageAnchorVar (depth + 1)) state.provenance = true := by
    apply provenanceAvoidCheck_true_of_not_mem
    intro member
    have bounded := invariant.bounded _ member
    have selectedBelowAnchor :
        stageSelectedVar depth < stageAnchorVar (depth + 1) := by
      unfold stageSelectedVar stageAnchorVar growingDiscoverySplitVar
        growingDiscoveryAnchorVar
      rw [generateCanonicalStage_searchIndex_advances]
      exact Nat.lt_add_of_pos_right (by decide)
    exact (Nat.ne_of_lt (Nat.lt_of_le_of_lt bounded selectedBelowAnchor)) rfl
  have candidatesExact : run.candidates =
      retainedDecoys ++
        [stageSelectedVar (depth + 1), stageAnchorVar (depth + 1),
          stageSelectedVar (depth + 1), stageAnchorVar (depth + 1)] := by
    rw [run.candidatesExact, run.filteringExact,
      filterCandidatesByProvenance_retained]
    rw [run.generated.extractionExact]
    change (stageExtractedCandidates (depth + 1)).filter _ = _
    rw [stageExtractedCandidates_exact, filter_append_constructive]
    change provenanceAvoidCheck
      (growingDiscoverySplitVar (constructStage (depth + 1)).searchIndex)
      state.provenance = true at selectedAccepted
    change provenanceAvoidCheck
      (growingDiscoveryAnchorVar (constructStage (depth + 1)).searchIndex)
      state.provenance = true at anchorAccepted
    change _ = retainedDecoys ++
      [growingDiscoverySplitVar (constructStage (depth + 1)).searchIndex,
        growingDiscoveryAnchorVar (constructStage (depth + 1)).searchIndex,
        growingDiscoverySplitVar (constructStage (depth + 1)).searchIndex,
        growingDiscoveryAnchorVar (constructStage (depth + 1)).searchIndex]
    simp only [List.filter, selectedAccepted, anchorAccepted]
    rfl
  have retainedFail : ∀ candidate, candidate ∈ retainedDecoys →
      (tryMeasuredCandidate (constructStage (depth + 1)).operationalRoot candidate).produced? =
        none := by
    intro candidate member
    have decoyMember := memberOfFilter_original
      (fun candidate => provenanceAvoidCheck candidate state.provenance)
      candidate decoys member
    have unmeasured := distinctGrowingDiscoveryDecoyCandidate_none
      (constructStage (depth + 1)).searchIndex candidate decoyMember
    let measured := tryMeasuredCandidate
      (constructStage (depth + 1)).operationalRoot candidate
    have resultNone : measured.result = none := by
      exact Eq.trans (tryMeasuredCandidate_exact _ _) unmeasured
    change measured.produced?.map (fun produced => produced.discovery) = none at resultNone
    exact optionEqNoneOfMapEqNone (fun produced => produced.discovery)
      measured.produced? resultNone
  have attempts : run.outcome.attempts = retainedDecoys.length + 1 := by
    rw [run.outcomeExact, candidatesExact]
    exact exploreFailuresThenSuccess_attempts
      (constructStage (depth + 1)).operationalRoot retainedDecoys
      (stageSelectedVar (depth + 1))
      [stageAnchorVar (depth + 1), stageSelectedVar (depth + 1),
        stageAnchorVar (depth + 1)] retainedFail
      (selectedMeasuredCandidate_succeeds depth)
  rw [attempts]
  rw [Nat.add_assoc, Nat.add_comm 1 state.provenance.length, ← Nat.add_assoc,
    retainedLength, distinctDecoyVariables_length]
  exact constitutedSearchIndex_next_add_two depth

/-- Sum of the linearly increasing discovery effort produced by causal
feedback.  The base is itself the attempt count emitted by the first stage. -/
def threadedAttemptTotal (base : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => threadedAttemptTotal (base + 1) count + base

theorem ThreadedConstitutiveStageRun.stageDiscoveryOutcomeExact
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.discoveryRun.outcome = run.discoveryRun.outcome := by
  calc
    stage.discoveryRun.outcome =
        (executeSequentialStageFromActiveRecorded depth assignment state.generation
          run.discoveryRun.asRecorded run.discoveryRun.extractionExact run.discovery
          run.recordedDiscoveryFound run.discoveryExact
          run.discoveryWorkLeCanonical).discoveryRun.outcome :=
      congrArg (fun built => built.discoveryRun.outcome) run.stageFromDiscovery
    _ = run.discoveryRun.outcome := rfl

theorem natAddRightCancelConstructive {left right suffix : Nat}
    (equal : left + suffix = right + suffix) : left = right := by
  induction suffix with
  | zero => exact equal
  | succ suffix inductionHypothesis =>
      apply inductionHypothesis
      exact Nat.succ.inj equal

theorem nextThreadedDiscovery_attempts_succ {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (invariant : ThreadedProvenanceInvariant state)
    (run : NextOperationalStateRun state stage) :
    (runThreadedNextDiscovery run.next).outcome.attempts =
      (runThreadedNextDiscovery state).outcome.attempts + 1 := by
  have current := threadedDiscovery_attempts_add_provenance_exact state invariant
  have following := threadedDiscovery_attempts_add_provenance_exact run.next
    (invariant.next run)
  have lengthExact : run.next.provenance.length = state.provenance.length + 1 := by
    rw [run.provenanceFromExecution]
    rfl
  rw [lengthExact] at following
  have rhsExact : 2 * (depth + 1) + 10 = (2 * depth + 10) + 2 := by
    calc
      2 * (depth + 1) + 10 = (2 * depth + 2) + 10 := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = 2 * depth + (2 + 10) := Nat.add_assoc _ _ _
      _ = 2 * depth + (10 + 2) :=
        congrArg (Nat.add (2 * depth)) (Nat.add_comm 2 10)
      _ = (2 * depth + 10) + 2 := (Nat.add_assoc _ _ _).symm
  rw [rhsExact, ← current] at following
  have rearranged :
      (runThreadedNextDiscovery run.next).outcome.attempts + 1 +
          state.provenance.length =
        ((runThreadedNextDiscovery state).outcome.attempts + 1) + 1 +
          state.provenance.length := by
    calc
      (runThreadedNextDiscovery run.next).outcome.attempts + 1 +
            state.provenance.length =
          (runThreadedNextDiscovery run.next).outcome.attempts +
            (state.provenance.length + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 state.provenance.length]
      _ = ((runThreadedNextDiscovery state).outcome.attempts +
            state.provenance.length) + 2 := following
      _ = (runThreadedNextDiscovery state).outcome.attempts +
            (state.provenance.length + 2) := Nat.add_assoc _ _ _
      _ = (runThreadedNextDiscovery state).outcome.attempts +
            (2 + state.provenance.length) :=
              congrArg
                (Nat.add (runThreadedNextDiscovery state).outcome.attempts)
                (Nat.add_comm state.provenance.length 2)
      _ = ((runThreadedNextDiscovery state).outcome.attempts + 2) +
            state.provenance.length := (Nat.add_assoc _ _ _).symm
      _ = ((runThreadedNextDiscovery state).outcome.attempts + 1) + 1 +
            state.provenance.length := by rfl
  exact natAddRightCancelConstructive
    (natAddRightCancelConstructive rearranged)

/-- The counter folded from the authoritative recursive history is exactly the
sum of the attempts emitted by its causally threaded discoveries. -/
theorem ConstitutiveExecutionHistory.discoveryAttempts_eq_threadedTotal
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (history : ConstitutiveExecutionHistory (count := count) state)
    (invariant : ThreadedProvenanceInvariant state) :
    history.toSequentialHistory.stats.discoveryAttempts =
      threadedAttemptTotal
        (runThreadedNextDiscovery state).outcome.attempts count := by
  induction history with
  | nil => rfl
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have tailInvariant := invariant.next headRun.nextRun
      have tailExact := inductionHypothesis tailInvariant
      have nextAttempts := nextThreadedDiscovery_attempts_succ invariant headRun.nextRun
      have headAttempts : head.stats.discoveryAttempts =
          (runThreadedNextDiscovery state).outcome.attempts := by
        change head.discoveryRun.outcome.attempts = _
        rw [headRun.stageDiscoveryOutcomeExact, headRun.discoveryRunExact]
      change tailRun.toSequentialHistory.stats.discoveryAttempts +
          head.stats.discoveryAttempts = _
      rw [tailExact, nextAttempts, headAttempts]
      rfl

theorem threadedAttemptTotal_mono {first second : Nat}
    (ordered : first ≤ second) (count : Nat) :
    threadedAttemptTotal first count ≤ threadedAttemptTotal second count := by
  induction count generalizing first second with
  | zero => exact Nat.le_refl 0
  | succ count inductionHypothesis =>
      exact Nat.add_le_add
        (inductionHypothesis (Nat.add_le_add_right ordered 1)) ordered

theorem threadedAttemptTotal_integrated_strict (input : Nat) :
    threadedAttemptTotal (2 * input + 10) (input + 1) <
      threadedAttemptTotal (2 * (input + 1) + 10) (input + 2) := by
  change threadedAttemptTotal (2 * input + 10) (input + 1) <
    threadedAttemptTotal (2 * (input + 1) + 10 + 1) (input + 1) +
      (2 * (input + 1) + 10)
  have ordered : 2 * input + 10 ≤ 2 * (input + 1) + 10 + 1 :=
    Nat.le_trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (Nat.le_add_right input 1)) 10)
      (Nat.le_add_right (2 * (input + 1) + 10) 1)
  have lower := threadedAttemptTotal_mono
    (first := 2 * input + 10)
    (second := 2 * (input + 1) + 10 + 1)
    ordered (input + 1)
  have positive : 0 < 2 * (input + 1) + 10 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _)
      (Nat.lt_add_of_pos_right (by decide))
  exact Nat.lt_of_le_of_lt lower (Nat.lt_add_of_pos_right positive)

theorem executedThreadedHistory_attempts_exact (depth count : Nat) :
    (executeConstitutiveExecutionHistory count
      (initialThreadedConstitutiveState depth)
      (initialThreadedConstitutiveState_fresh depth)).toSequentialHistory.stats.discoveryAttempts =
        threadedAttemptTotal (2 * depth + 10) count := by
  let history := executeConstitutiveExecutionHistory count
    (initialThreadedConstitutiveState depth)
    (initialThreadedConstitutiveState_fresh depth)
  have exactTotal := history.discoveryAttempts_eq_threadedTotal
    (initialThreadedProvenanceInvariant depth)
  have initialAttempts := threadedDiscovery_attempts_add_provenance_exact
    (initialThreadedConstitutiveState depth)
    (initialThreadedProvenanceInvariant depth)
  change (runThreadedNextDiscovery
    (initialThreadedConstitutiveState depth)).outcome.attempts + 0 =
      2 * depth + 10 at initialAttempts
  rw [Nat.add_zero] at initialAttempts
  rw [exactTotal, initialAttempts]

theorem member_append_left_constructive {alpha : Type} (value : alpha) :
    ∀ {left right : List alpha}, value ∈ left → value ∈ left ++ right
  | [], _, member => nomatch member
  | head :: tail, right, member => by
      cases member with
      | head => exact List.Mem.head _
      | tail _ prior =>
          exact List.Mem.tail _ (member_append_left_constructive value prior)

theorem priorSelected_extracted_next (depth : Nat) :
    stageSelectedVar (depth + 1) ∈
      stageExtractedCandidates ((depth + 1) + 1) := by
  rw [stageExtractedCandidates_exact]
  apply member_append_left_constructive
  apply distinctDecoyVariables_mem_of_lt
  rw [generateCanonicalStage_searchIndex_advances (depth + 1)]
  unfold stageSelectedVar growingDiscoverySplitVar
  exact Nat.lt_succ_self _

theorem filterCandidatesByHistory_empty (candidates : List Var) :
    (filterCandidatesByHistory [] candidates).retained = candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [filterCandidatesByHistory]
      change candidate :: (filterCandidatesByHistory [] rest).retained = _
      rw [inductionHypothesis]

theorem filterCandidatesByProvenance_empty (candidates : List Var) :
    (filterCandidatesByProvenance [] candidates).retained = candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest inductionHypothesis =>
      rw [filterCandidatesByProvenance]
      change candidate :: (filterCandidatesByProvenance [] rest).retained = _
      rw [inductionHypothesis]

theorem erasedHistory_retains_priorSelected (depth : Nat) :
    stageSelectedVar (depth + 1) ∈
      (runThreadedNextDiscovery
        (erasedNextDiscoveryState depth).state).candidates := by
  let run := runThreadedNextDiscovery (erasedNextDiscoveryState depth).state
  rw [run.candidatesExact, run.filteringExact]
  change stageSelectedVar (depth + 1) ∈
    (filterCandidatesByProvenance [] run.generated.extraction.candidates).retained
  rw [filterCandidatesByProvenance_empty, run.generated.extractionExact]
  exact priorSelected_extracted_next depth

theorem retainedHistory_rejects_priorSelected (depth : Nat) :
    stageSelectedVar (depth + 1) ∉
      (runThreadedNextDiscovery
        (retainedNextDiscoveryState depth).state).candidates := by
  intro retained
  let state := (retainedNextDiscoveryState depth).state
  let run := runThreadedNextDiscovery state
  have filtered : stageSelectedVar (depth + 1) ∈
      run.generated.extraction.candidates.filter (fun candidate =>
        provenanceAvoidCheck candidate state.provenance) := by
    rw [← filterCandidatesByProvenance_retained,
      ← run.filteringExact, ← run.candidatesExact]
    exact retained
  have accepted := memberOfFilter_predicate
    (fun candidate => provenanceAvoidCheck candidate state.provenance)
    (stageSelectedVar (depth + 1)) _ filtered
  have rejected : provenanceAvoidCheck (stageSelectedVar (depth + 1))
      state.provenance = false := by
    change provenanceAvoidCheck (stageSelectedVar (depth + 1))
      (nextDiscoveryCommonOrigin depth).run.nextRun.next.provenance = false
    rw [(nextDiscoveryCommonOrigin depth).run.nextRun.provenanceFromExecution]
    exact provenanceAvoidCheck_head_selected
      (stageSelectedVar (depth + 1)) []
  rw [rejected] at accepted
  cases accepted

/-- On the reachable next-stage family, erasing the constituted history
changes the candidate trace that is actually passed to exploration. -/
theorem reachableHistory_candidateTraces_different (depth : Nat) :
    (runThreadedNextDiscovery
        (retainedNextDiscoveryState depth).state).candidates ≠
      (runThreadedNextDiscovery
        (erasedNextDiscoveryState depth).state).candidates := by
  intro same
  apply retainedHistory_rejects_priorSelected depth
  rw [same]
  exact erasedHistory_retains_priorSelected depth

theorem blockedNextDiscoveryChild_decisions (depth : Nat) :
    (blockedNextDiscoveryChild depth).context.decisions =
      ⟨stageSelectedVar ((depth + 1) + 1), false⟩ ::
        (retainedNextDiscoveryState depth).state.decisions := by
  unfold blockedNextDiscoveryChild integratedMarkedTarget
    retainedNextDiscoveryState
  dsimp only
  change
    ⟨(nextDiscoveryCommonOrigin depth).stage.storedSchedule.entry.var + 2, false⟩ ::
        (nextDiscoveryCommonOrigin depth).stage.storedSchedule.entry.target.context.decisions =
      ⟨stageSelectedVar (depth + 1 + 1), false⟩ ::
        (nextDiscoveryCommonOrigin depth).run.nextRun.next.decisions
  rw [(retained_decisions_exact (nextDiscoveryCommonOrigin depth).stage).2]
  rw [(nextDiscoveryCommonOrigin depth).run.nextRun.decisionsFromExecution]
  rw [retained_var_exact, stageSelectedVar_succ]
  rw [stageSelectedVar_succ (depth + 1)]
  rfl

/-- A second genuine child records the anchor determination as well.  This
ensures the blocked search contains no unfiltered copy of either non-decoy
candidate. -/
def blockedNextDiscoveryCarrier (depth : Nat) :=
  GeneratedStructuralBranchContext.child
    (blockedNextDiscoveryChild depth)
    (stageAnchorVar ((depth + 1) + 1)) true (by
      rw [blockedNextDiscoveryChild_decisions]
      constructor
      · rw [stageAnchorVar_eq_selected_succ]
        exact Nat.ne_of_lt (Nat.lt_succ_self _)
      · apply structuralDecisionsAvoid_of_all_lt
        intro decision member
        exact Nat.lt_trans
          ((nextDiscoveryCommonOrigin depth).run.nextRun.fresh
            (initialThreadedConstitutiveState_fresh depth) decision member)
          (by rw [stageAnchorVar_eq_selected_succ]; exact Nat.lt_succ_self _))

theorem blockedNextDiscoveryCarrier_decisions (depth : Nat) :
    (blockedNextDiscoveryCarrier depth).context.decisions =
      ⟨stageAnchorVar ((depth + 1) + 1), true⟩ ::
      ⟨stageSelectedVar ((depth + 1) + 1), false⟩ ::
        (retainedNextDiscoveryState depth).state.decisions := by
  unfold blockedNextDiscoveryCarrier
  dsimp only [GeneratedStructuralBranchContext.child, structuralChildContext]
  rw [blockedNextDiscoveryChild_decisions]

theorem retainedNextDiscoveryState_fresh (depth : Nat) :
    ThreadedStateFreshForNext (retainedNextDiscoveryState depth).state :=
  (nextDiscoveryCommonOrigin depth).run.nextRun.fresh
    (initialThreadedConstitutiveState_fresh depth)

/-- A complete state whose decisions and provenance are extracted from the
genuine child generated from the common executed target. -/
structure BlockedNextDiscoveryConstruction (depth : Nat) where
  state : ThreadedConstitutiveState (depth + 1)
    (retainedNextDiscoveryState depth).assignment
  decisionsFromChild :
    state.decisions = (blockedNextDiscoveryCarrier depth).context.decisions
  provenanceFromChild :
    state.provenance =
      (blockedNextDiscoveryCarrier depth).context.decisions.map
        (fun decision => decision.var)

set_option maxHeartbeats 6000000 in
def blockedNextDiscoveryConstruction (depth : Nat) :
    BlockedNextDiscoveryConstruction depth := by
  have childHold :
      StructuralDecisionsHold
        (retainedNextDiscoveryState depth).assignment.assignment
        (blockedNextDiscoveryCarrier depth).context.decisions := by
    rw [blockedNextDiscoveryCarrier_decisions]
    exact
      ⟨(retainedNextDiscoveryState depth).assignment.futureAnchorTrue _
          (Nat.le_refl _),
        ⟨(retainedNextDiscoveryState depth).assignment.futureSelectedFalse _
            (Nat.le_refl _),
          (retainedNextDiscoveryState depth).state.decisionsHold⟩⟩
  exact
    { state :=
        { threadedAssignment :=
            (retainedNextDiscoveryState depth).state.threadedAssignment
          threadedAssignmentExact :=
            (retainedNextDiscoveryState depth).state.threadedAssignmentExact
          generation := (retainedNextDiscoveryState depth).state.generation
          searchSeed := (retainedNextDiscoveryState depth).state.searchSeed
          searchSeedExact := (retainedNextDiscoveryState depth).state.searchSeedExact
          decisions := (blockedNextDiscoveryCarrier depth).context.decisions
          provenance :=
            (blockedNextDiscoveryCarrier depth).context.decisions.map
              (fun decision => decision.var)
          provenanceExact := rfl
          decisionsHold := childHold }
      decisionsFromChild := rfl
      provenanceFromChild := rfl }

def blockedNextDiscoveryState (depth : Nat) :
    PackedThreadedConstitutiveState (depth + 1) :=
  let retained := retainedNextDiscoveryState depth
  ⟨retained.assignment, (blockedNextDiscoveryConstruction depth).state⟩

/-- Two organizations sharing one executed origin.  The retained organization
is produced by execution; the blocked organization is constructed
counterfactually from that origin. -/
inductive NextDiscoveryOrganization where
  | retained
  | blocked
  deriving DecidableEq

structure NextDiscoveryConstitution (depth : Nat) where
  organization : NextDiscoveryOrganization
  packed : PackedThreadedConstitutiveState (depth + 1)
  stateExact : packed = match organization with
    | .retained => retainedNextDiscoveryState depth
    | .blocked => blockedNextDiscoveryState depth

def nextDiscoveryConstitution (depth : Nat)
    (organization : NextDiscoveryOrganization) : NextDiscoveryConstitution depth :=
  match organization with
  | .retained => ⟨.retained, retainedNextDiscoveryState depth, rfl⟩
  | .blocked => ⟨.blocked, blockedNextDiscoveryState depth, rfl⟩

/-- The projectable state data deliberately exclude decision history and
provenance.  Unlike the former constant projection, this reads the actual
assignment, generation witness, and transmitted seed of each constitution. -/
def nextDiscoveryProjection {depth : Nat}
    (constitution : NextDiscoveryConstitution depth) :
    SequentialAssignment (depth + 1) × CanonicalStageGeneration (depth + 1) × Nat :=
  (constitution.packed.assignment, constitution.packed.state.generation,
    constitution.packed.state.searchSeed)

def nextDiscoveryOutcome {depth : Nat} (state : NextDiscoveryConstitution depth) :=
  (runThreadedNextDiscovery state.packed.state).outcome.discovered?

theorem nextDiscovery_retained_found (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠ none := by
  exact runThreadedNextDiscovery_found (retainedNextDiscoveryState depth).state
    (retainedNextDiscoveryState_fresh depth)

theorem nextDiscovery_blocked_none (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .blocked) = none := by
  let state := (blockedNextDiscoveryState depth).state
  let run := runThreadedNextDiscovery state
  have allFailed : ∀ candidate, candidate ∈ run.candidates →
      (tryMeasuredCandidate
        (constructStage ((depth + 1) + 1)).operationalRoot candidate).produced? = none := by
    intro candidate tested
    have filtered : candidate ∈
        (run.generated.extraction.candidates.filter (fun candidate =>
          provenanceAvoidCheck candidate state.provenance)) := by
      rw [← filterCandidatesByProvenance_retained]
      rw [← run.filteringExact, ← run.candidatesExact]
      exact tested
    have extracted := memberOfFilter_original
      (fun candidate => provenanceAvoidCheck candidate state.provenance)
      candidate _ filtered
    have compatibleProvenance := memberOfFilter_predicate
      (fun candidate => provenanceAvoidCheck candidate state.provenance)
      candidate _ filtered
    have compatible :
        structuralDecisionsAvoidCheck candidate state.decisions = true := by
      rw [← provenanceAvoidCheck_decisions candidate state.decisions]
      rw [← state.provenanceExact]
      exact compatibleProvenance
    have canonicalMember : candidate ∈
        (stageRecordedDiscoveryRun ((depth + 1) + 1)).extraction.candidates := by
      rw [← run.generated.extractionExact]
      exact extracted
    have stageMember : candidate ∈
        stageExtractedCandidates ((depth + 1) + 1) := canonicalMember
    rcases stageExtracted_classification ((depth + 1) + 1) candidate stageMember with
      decoy | selected | anchor
    · have unmeasuredNone := distinctGrowingDiscoveryDecoyCandidate_none
        (constructStage ((depth + 1) + 1)).searchIndex candidate decoy
      let measured := tryMeasuredCandidate
        (constructStage ((depth + 1) + 1)).operationalRoot candidate
      have resultNone : measured.result = none := by
        rw [tryMeasuredCandidate_exact]
        exact unmeasuredNone
      change measured.produced?.map (fun produced => produced.discovery) = none at resultNone
      exact optionEqNoneOfMapEqNone (fun produced => produced.discovery)
        measured.produced? resultNone
    · have avoid := structuralDecisionsAvoid_of_check_true candidate state.decisions compatible
      dsimp only [state] at avoid
      change StructuralDecisionsAvoid candidate
        (blockedNextDiscoveryConstruction depth).state.decisions at avoid
      rw [(blockedNextDiscoveryConstruction depth).decisionsFromChild,
        blockedNextDiscoveryCarrier_decisions] at avoid
      exact False.elim (avoid.2.1 selected.symm)
    · have avoid := structuralDecisionsAvoid_of_check_true candidate state.decisions compatible
      dsimp only [state] at avoid
      change StructuralDecisionsAvoid candidate
        (blockedNextDiscoveryConstruction depth).state.decisions at avoid
      rw [(blockedNextDiscoveryConstruction depth).decisionsFromChild,
        blockedNextDiscoveryCarrier_decisions] at avoid
      exact False.elim (avoid.1 anchor.symm)
  change run.outcome.discovered? = none
  rw [run.outcomeExact]
  exact exploreRecordedCandidates_none_of_all_failed _ run.candidates allFailed

theorem blocked_discovery_constructs_no_stage (depth : Nat) :
    (runThreadedNextDiscovery
      (blockedNextDiscoveryState depth).state).outcome.discovered? = none :=
  nextDiscovery_blocked_none depth

theorem nextDiscovery_states_share_executed_origin (depth : Nat) :
      (nextDiscoveryConstitution depth .retained).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next ∧
      (nextDiscoveryConstitution depth .blocked).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next := by
  exact ⟨rfl, rfl⟩

theorem retainedNextDiscovery_history_length (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions.length = 1 :=
  by
    change (nextDiscoveryCommonOrigin depth).run.nextRun.next.decisions.length = 1
    rw [(nextDiscoveryCommonOrigin depth).run.nextRun.decisionsFromExecution]
    rfl

theorem blockedNextDiscovery_history_length (depth : Nat) :
    (nextDiscoveryConstitution depth .blocked).packed.state.decisions.length = 3 := by
  change (blockedNextDiscoveryConstruction depth).state.decisions.length = 3
  rw [(blockedNextDiscoveryConstruction depth).decisionsFromChild]
  rw [blockedNextDiscoveryCarrier_decisions]
  change (retainedNextDiscoveryState depth).state.decisions.length + 2 = 3
  have retainedLength :
      (retainedNextDiscoveryState depth).state.decisions.length = 1 := by
    change (nextDiscoveryCommonOrigin depth).run.nextRun.next.decisions.length = 1
    rw [(nextDiscoveryCommonOrigin depth).run.nextRun.decisionsFromExecution]
    rfl
  rw [retainedLength]

theorem nextDiscovery_history_lengths_distinct (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions.length ≠
      (nextDiscoveryConstitution depth .blocked).packed.state.decisions.length := by
  intro lengthsEqual
  have oneEqThree : 1 = 3 :=
    Eq.trans (retainedNextDiscovery_history_length depth).symm
      (Eq.trans lengthsEqual (blockedNextDiscovery_history_length depth))
  exact (by decide : (1 : Nat) ≠ 3) oneEqThree

theorem nextDiscovery_histories_distinct (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions ≠
      (nextDiscoveryConstitution depth .blocked).packed.state.decisions := by
  intro decisionsEqual
  exact nextDiscovery_history_lengths_distinct depth
    (congrArg List.length decisionsEqual)

theorem nextDiscovery_constitutions_distinct (depth : Nat) :
    nextDiscoveryConstitution depth .retained ≠
      nextDiscoveryConstitution depth .blocked := by
  intro impossible
  have organizationsEqual := congrArg NextDiscoveryConstitution.organization impossible
  cases organizationsEqual

theorem nextDiscovery_projection_equal (depth : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
      nextDiscoveryProjection (nextDiscoveryConstitution depth .blocked) :=
  by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl

theorem nextDiscovery_outcome_different (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠
      nextDiscoveryOutcome (nextDiscoveryConstitution depth .blocked) := by
  rw [nextDiscovery_blocked_none]
  exact nextDiscovery_retained_found depth

theorem nextDiscovery_not_factors (depth : Nat) :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := depth))
        (nextDiscoveryOutcome (depth := depth)) := by
  apply value_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .retained)
    (nextDiscoveryConstitution depth .blocked)
  · exact nextDiscovery_projection_equal depth
  · exact nextDiscovery_outcome_different depth

/-- Failure exposes no code, next state or terminal placeholder. -/
structure FeedbackFailureArtifacts where
  codeAtoms : Nat
  nextProduced : Bool
  terminalProduced : Bool
  deriving DecidableEq, Repr

def feedbackFailureArtifacts (depth : Nat) : FeedbackFailureArtifacts :=
  match nextDiscoveryOutcome (nextDiscoveryConstitution depth .blocked) with
  | none => ⟨0, false, false⟩
  | some _ => ⟨1, true, true⟩

theorem feedbackFailureArtifacts_exact (depth : Nat) :
    feedbackFailureArtifacts depth = ⟨0, false, false⟩ := by
  unfold feedbackFailureArtifacts
  rw [nextDiscovery_blocked_none]

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.inspectTransmittedDecisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.inspectTransmittedDecisions_head_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralDecisionsAvoidCheck_true_of_avoid
#print axioms ConstitutiveSearch.EndogenousDecomposition.inspectTransmittedDecisions_available_of_all_lt
#print axioms ConstitutiveSearch.EndogenousDecomposition.inspectTransmittedDecisions_visits_of_all_ne
#print axioms ConstitutiveSearch.EndogenousDecomposition.initializationEndpointExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveStateFromInitialization
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveStateFromInitialization_generation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveState_generation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveStateFromInitialization_fresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveState
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedConstitutiveState_fresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralDecisionsAvoid_of_all_lt
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveState.decisionsAvoidNext
#print axioms ConstitutiveSearch.EndogenousDecomposition.exploreRecordedCandidates_transport_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.runFeedbackDiscoveryFromData
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageSelectedVar_eq_nextSearchIndex
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedProducedSearchSeed
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedProducedSearchSeed_eq_scheduleEntry
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedProducedSearchSeed_eq_nextSearchIndex
#print axioms ConstitutiveSearch.EndogenousDecomposition.runThreadedNextDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.filterCandidatesByHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.provenanceAvoidCheck
#print axioms ConstitutiveSearch.EndogenousDecomposition.inspectCandidateProvenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.provenanceAvoidCheck_decisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.filterCandidatesByProvenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.listMapLengthConstructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.filterCandidatesByProvenance_matches_history
#print axioms ConstitutiveSearch.EndogenousDecomposition.filterCandidatesByProvenance_retained_decisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.filterCandidatesByProvenance_retained_length_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.runThreadedNextDiscovery_discovered_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.appendProvenanceMeasured
#print axioms ConstitutiveSearch.EndogenousDecomposition.prependProvenanceMeasured
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralDecisionsHold_transport
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageNext_preserves_threadedDecisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedBranchDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedBranchDecision_eq_selected_true
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeNextOperationalState
#print axioms ConstitutiveSearch.EndogenousDecomposition.NextOperationalStateRun.fresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.NextOperationalStateRun.generationCanonical
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildThreadedConstitutiveStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveStageRun.nextDiscoveryConsumesProducedProvenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveStageRun.nextDiscoveryConsumesRetainedSearchSeed
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeThreadedConstitutiveStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.failedDiscovery_noStageRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.failedDiscovery_noConstructedStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.failedDiscovery_historyCount_eq_zero
#print axioms ConstitutiveSearch.EndogenousDecomposition.failedDiscovery_noPositiveHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.toSequentialHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.provenanceAvoidCheck_false_of_mem
#print axioms ConstitutiveSearch.EndogenousDecomposition.provenanceAvoidCheck_false_implies_mem
#print axioms ConstitutiveSearch.EndogenousDecomposition.provenanceAvoidCheck_true_of_not_mem
#print axioms ConstitutiveSearch.EndogenousDecomposition.filteredList_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar_member_original
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar_preserves_other
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar_length_plus_one
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstVar_excludes_target
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodupVarLists_sameLength_of_mutualMembership
#print axioms ConstitutiveSearch.EndogenousDecomposition.filter_complement_lengths
#print axioms ConstitutiveSearch.EndogenousDecomposition.filter_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.rejectedCandidates_length_eq_provenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedCandidates_length_add_provenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.exploreFailuresThenSuccess_attempts
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedProvenanceInvariant
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialThreadedProvenanceInvariant
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedProvenanceInvariant.next
#print axioms ConstitutiveSearch.EndogenousDecomposition.selectedMeasuredCandidate_succeeds
#print axioms ConstitutiveSearch.EndogenousDecomposition.threadedDiscovery_attempts_add_provenance_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.threadedAttemptTotal
#print axioms ConstitutiveSearch.EndogenousDecomposition.ThreadedConstitutiveStageRun.stageDiscoveryOutcomeExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.natAddRightCancelConstructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextThreadedDiscovery_attempts_succ
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.discoveryAttempts_eq_threadedTotal
#print axioms ConstitutiveSearch.EndogenousDecomposition.threadedAttemptTotal_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.threadedAttemptTotal_integrated_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedThreadedHistory_attempts_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.listLengthAppendConstructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.extractCnfCandidateRun_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.runCandidateExtraction_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.priorSelected_extracted_next
#print axioms ConstitutiveSearch.EndogenousDecomposition.erasedHistory_retains_priorSelected
#print axioms ConstitutiveSearch.EndogenousDecomposition.reachableHistory_candidateTraces_different
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.testedCandidates_eq_attempts
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.controlStats_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.executedBits_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.decisionAccumulations_eq_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.provenanceVisits_eq_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExecutionHistory.inspections_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedFeedbackHistory_provenanceVisits
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedFeedbackHistory_inspections_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleStage_decision_reads_executedOutput
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleStage_output_constitutes_nextOperationalState
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildThreadedConstitutiveRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryCommonOrigin
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscoveryChild
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedNextDiscoveryState
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscoveryChild_decisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscoveryCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscoveryConstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscoveryState
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_retained_found
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscoveryProjection
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_blocked_none
#print axioms ConstitutiveSearch.EndogenousDecomposition.blocked_discovery_constructs_no_stage
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_states_share_executed_origin
#print axioms ConstitutiveSearch.EndogenousDecomposition.blockedNextDiscovery_history_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_history_lengths_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_histories_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_outcome_different
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_projection_equal
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.feedbackFailureArtifacts_exact
/- AXIOM_AUDIT_END -/
