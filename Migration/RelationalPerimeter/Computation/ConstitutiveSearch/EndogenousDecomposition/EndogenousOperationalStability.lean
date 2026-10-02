import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExtensionalOperationalStability
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolution
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

/-!
# Endogenous operational stability

The certificate in this file joins the constituted openings, the measured
candidate exploration, the discovered total transports, the accepted frontier
reductions, and the causally threaded next states. Width equalities are
consequences of this joined evidence; they are not licenses for reduction.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Every candidate in a list was genuinely executed and returned no result. -/
inductive AllMeasuredCandidatesFail {root : Cnf}
    (state : GeneratedStructuralBranchContext root) : List Var → Prop where
  | nil : AllMeasuredCandidatesFail state []
  | cons {candidate rest} :
      (tryMeasuredCandidate state candidate).produced? = none →
      AllMeasuredCandidatesFail state rest →
      AllMeasuredCandidatesFail state (candidate :: rest)

/-- Executed failed-prefix/success decomposition of one exploration. -/
inductive ExecutedSuccessfulSearch {root : Cnf}
    (state : GeneratedStructuralBranchContext root) : List Var → Type where
  | found {candidate rest} :
      (tryMeasuredCandidate state candidate).produced? ≠ none →
      ExecutedSuccessfulSearch state (candidate :: rest)
  | failed {candidate rest} :
      (tryMeasuredCandidate state candidate).produced? = none →
      ExecutedSuccessfulSearch state rest →
      ExecutedSuccessfulSearch state (candidate :: rest)

namespace ExecutedSuccessfulSearch

/-- Candidates genuinely rejected before the successful one. -/
def failedCandidates {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → ExecutedSuccessfulSearch state candidates → List Var
  | _, .found _ => []
  | _, @failed _ _ candidate _ _ tail =>
      candidate :: failedCandidates tail

/-- First candidate whose executed attempt returns a result. -/
def selectedCandidate {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → ExecutedSuccessfulSearch state candidates → Var
  | _, @found _ _ candidate _ _ => candidate
  | _, .failed _ tail => selectedCandidate tail

/-- The stored failed prefix carries the actual failed attempt equations. -/
theorem failuresAreMeasured {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → (evidence : ExecutedSuccessfulSearch state candidates) →
      AllMeasuredCandidatesFail state evidence.failedCandidates
  | _, .found _ => .nil
  | _, @failed _ _ _ _ failure tail =>
      .cons failure (failuresAreMeasured tail)

/-- The selected candidate is backed by an executed successful attempt. -/
theorem selectedSucceeds {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → (evidence : ExecutedSuccessfulSearch state candidates) →
      (tryMeasuredCandidate state evidence.selectedCandidate).produced? ≠ none
  | _, .found success => success
  | _, .failed _ tail => selectedSucceeds tail

/-- The candidate list begins with the exact failed prefix and selection. -/
theorem candidates_prefix_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → (evidence : ExecutedSuccessfulSearch state candidates) →
      ∃ rest,
        candidates = evidence.failedCandidates ++ evidence.selectedCandidate :: rest
  | _, @found _ _ _ rest _ => ⟨rest, rfl⟩
  | _, .failed _ tail =>
      let ⟨rest, exactTail⟩ := candidates_prefix_exact tail
      ⟨rest, congrArg (List.cons _) exactTail⟩

/-- Build evidence by following the same recursion that explored candidates. -/
def build {root : Cnf}
    (state : GeneratedStructuralBranchContext root) :
    ∀ candidates,
      (exploreRecordedCandidates state candidates).discovered? ≠ none →
      ExecutedSuccessfulSearch state candidates
  | [], success => False.elim (success rfl)
  | candidate :: rest, success => by
      cases found : (tryMeasuredCandidate state candidate).produced? with
      | none =>
          have tailSuccess :
              (exploreRecordedCandidates state rest).discovered? ≠ none := by
            intro tailFailed
            apply success
            simp only [exploreRecordedCandidates, found]
            exact tailFailed
          exact .failed found (build state rest tailSuccess)
      | some _ =>
          exact .found (fun impossible => by
            have contradiction := Eq.trans found.symm impossible
            nomatch contradiction)

/-- Recorded attempts are failed-prefix length plus the successful attempt. -/
theorem attempts_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → (evidence : ExecutedSuccessfulSearch state candidates) →
      (exploreRecordedCandidates state candidates).attempts =
        evidence.failedCandidates.length + 1
  | _, @found _ _ candidate _ success => by
      cases found : (tryMeasuredCandidate state candidate).produced? with
      | none => exact False.elim (success found)
      | some _ =>
          simp only [exploreRecordedCandidates, found, failedCandidates]
          rfl
  | _, @failed _ _ candidate _ failure tail => by
      simp only [exploreRecordedCandidates, failure, failedCandidates]
      exact congrArg (fun value => value + 1) (attempts_exact tail)

/-- Emitted tested candidates are exactly failures followed by selection. -/
theorem testedCandidates_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} :
    {candidates : List Var} → (evidence : ExecutedSuccessfulSearch state candidates) →
      (exploreRecordedCandidates state candidates).testedCandidates =
        evidence.failedCandidates ++ [evidence.selectedCandidate]
  | _, @found _ _ candidate _ success => by
      cases found : (tryMeasuredCandidate state candidate).produced? with
      | none => exact False.elim (success found)
      | some _ =>
          simp only [exploreRecordedCandidates, found, failedCandidates,
            selectedCandidate]
          rfl
  | _, @failed _ _ candidate _ failure tail => by
      simp only [exploreRecordedCandidates, failure, failedCandidates,
        selectedCandidate]
      exact congrArg (List.cons candidate) (testedCandidates_exact tail)

end ExecutedSuccessfulSearch

/-- Search-work evidence consumed by one executed stage. -/
structure ExecutedDiscoveryWorkEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Type where
  search : ExecutedSuccessfulSearch
    (constructStage (depth + 1)).operationalRoot run.discoveryRun.candidates
  outcomeExact : run.discoveryRun.outcome =
    exploreRecordedCandidates
      (constructStage (depth + 1)).operationalRoot run.discoveryRun.candidates
  discoveryExact : run.discoveryRun.outcome.discovered? = some stage.discovery
  attemptsExact : run.discoveryRun.outcome.attempts =
    search.failedCandidates.length + 1
  testedPrefixExact : run.discoveryRun.outcome.testedCandidates =
    search.failedCandidates ++ [search.selectedCandidate]
  failuresMeasured : AllMeasuredCandidatesFail
    (constructStage (depth + 1)).operationalRoot search.failedCandidates
  selectedMeasuredSuccess :
    (tryMeasuredCandidate
      (constructStage (depth + 1)).operationalRoot
      search.selectedCandidate).produced? ≠ none

/-- Construct work evidence from the recorded outcome of the executed run. -/
def executedDiscoveryWorkEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExecutedDiscoveryWorkEvidence run := by
  have exploredFound :
      (exploreRecordedCandidates
        (constructStage (depth + 1)).operationalRoot
        run.discoveryRun.candidates).discovered? = some stage.discovery :=
    Eq.trans
      (congrArg RecordedDiscoveryOutcome.discovered?
        run.discoveryRun.outcomeExact).symm
      run.relationFromTransmittedState
  have exploredSuccess :
      (exploreRecordedCandidates
        (constructStage (depth + 1)).operationalRoot
        run.discoveryRun.candidates).discovered? ≠ none := by
    intro impossible
    have contradiction : some stage.discovery = none :=
      Eq.trans exploredFound.symm impossible
    nomatch contradiction
  let search := ExecutedSuccessfulSearch.build _ _ exploredSuccess
  refine
    { search := search
      outcomeExact := run.discoveryRun.outcomeExact
      discoveryExact := run.relationFromTransmittedState
      attemptsExact := ?_
      testedPrefixExact := ?_
      failuresMeasured := search.failuresAreMeasured
      selectedMeasuredSuccess := search.selectedSucceeds }
  · exact Eq.trans
      (congrArg RecordedDiscoveryOutcome.attempts run.discoveryRun.outcomeExact)
      (ExecutedSuccessfulSearch.attempts_exact search)
  · exact Eq.trans
      (congrArg RecordedDiscoveryOutcome.testedCandidates
        run.discoveryRun.outcomeExact)
      (ExecutedSuccessfulSearch.testedCandidates_exact search)

/-- If an executed successful search performs at least ten attempts, at least
nine tenths of those attempts belong to its positively identified failed
prefix. -/
theorem executed_failed_candidate_rate {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (tenAttempts : 10 ≤ run.discoveryRun.outcome.attempts) :
    9 * run.discoveryRun.outcome.attempts ≤
      10 * (executedDiscoveryWorkEvidence run).search.failedCandidates.length := by
  let failures :=
    (executedDiscoveryWorkEvidence run).search.failedCandidates.length
  have attemptsExact : run.discoveryRun.outcome.attempts = failures + 1 :=
    (executedDiscoveryWorkEvidence run).attemptsExact
  have tenBelow : 10 ≤ failures + 1 := by
    rw [← attemptsExact]
    exact tenAttempts
  have nineBelow : 9 ≤ failures :=
    Nat.le_of_succ_le_succ tenBelow
  rw [attemptsExact, Nat.mul_add, Nat.mul_one]
  change 9 * failures + 9 ≤ 10 * failures
  rw [show 10 = 9 + 1 by rfl, Constructive.nat_add_mul, Nat.one_mul]
  exact Nat.add_le_add_left nineBelow (9 * failures)

/-- The first discovery actually executed for depth `depth` performs the exact
canonical number of attempts, beginning with ten at depth zero. -/
theorem initialExecutedDiscovery_attempts_exact (depth : Nat) :
    (nextDiscoveryCommonOrigin depth).run.discoveryRun.outcome.attempts =
      2 * depth + 10 := by
  have exactAttempts := threadedDiscovery_attempts_add_provenance_exact
    (initialThreadedConstitutiveState depth)
    (initialThreadedProvenanceInvariant depth)
  have provenanceEmpty :
      (initialThreadedConstitutiveState depth).provenance.length = 0 :=
    rfl
  rw [provenanceEmpty, Nat.add_zero] at exactAttempts
  rw [(nextDiscoveryCommonOrigin depth).run.discoveryRunExact]
  exact exactAttempts

/-- At least ninety percent of the candidates tested by the actual initial
discovery at every depth are rejected before the selected success. -/
theorem initialExecutedDiscovery_failed_candidate_rate (depth : Nat) :
    9 * (nextDiscoveryCommonOrigin depth).run.discoveryRun.outcome.attempts ≤
      10 * (executedDiscoveryWorkEvidence
        (nextDiscoveryCommonOrigin depth).run).search.failedCandidates.length := by
  apply executed_failed_candidate_rate
  rw [initialExecutedDiscovery_attempts_exact]
  exact Nat.le_add_left 10 (2 * depth)


/-- Causally indexed history of the executed candidate work. -/
def ExecutedDiscoveryWorkHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ExecutedDiscoveryWorkEvidence headRun ×
        ExecutedDiscoveryWorkHistory tailRoles

def buildExecutedDiscoveryWorkHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      ExecutedDiscoveryWorkHistory roles
  | _, _, _, _, _, .nil => by
      change Unit
      exact ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ⟨executedDiscoveryWorkEvidence headRun,
        buildExecutedDiscoveryWorkHistory tailRoles⟩

/-- Read the exact head work record from the causally indexed discovery history. -/
def executedDiscoveryWorkHistoryHead
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExecutedDiscoveryWorkHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExecutedDiscoveryWorkEvidence headRun :=
  history.1

/-- The discovery-work tail is indexed by the state produced by its head. -/
def executedDiscoveryWorkHistoryTail
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExecutedDiscoveryWorkHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExecutedDiscoveryWorkHistory tailRoles :=
  history.2

/-- History of extensional projections, indexed by the same causal chain. -/
def ExtensionalOperationalStabilityHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type 1
  | _, _, _, _, _, .nil => ULift.{1} Unit
  | depth, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ _ _ _ tailRoles =>
      ExtensionalOperationalStabilityView
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)) ×
        ExtensionalOperationalStabilityHistory tailRoles

def buildExtensionalOperationalStabilityHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      ExtensionalOperationalStabilityHistory roles
  | _, _, _, _, _, .nil => ULift.up.{1} ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ⟨executedStepToExtensionalView headRun,
        buildExtensionalOperationalStabilityHistory tailRoles⟩

/-- Read the exact executed projection at the head of the dependent history. -/
def extensionalOperationalStabilityHistoryHead
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExtensionalOperationalStabilityHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExtensionalOperationalStabilityView
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)) :=
  history.1

/-- The projected tail remains indexed by the next state of the head run. -/
def extensionalOperationalStabilityHistoryTail
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExtensionalOperationalStabilityHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExtensionalOperationalStabilityHistory tailRoles :=
  history.2

/-- Closed exact causal evidence package over the authoritative dependent role
history. Numerical width traces remain derived readouts of the constituted
frontiers and are proved separately rather than stored as causal premises. -/
structure EndogenousOperationalStabilityEvidence
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Type 2 where
  private mk ::
  reductions : ExecutedOperationalReductionHistory roles
  discoveryWork : ExecutedDiscoveryWorkHistory roles
  extensionalProjection : ExtensionalOperationalStabilityHistory roles
  structuralExact : structuralWidth roles = 2 ^ operationalStageCount roles
  pendingExact : pendingWidth roles = structuralWidth roles
  executedExact : executedWidth roles = 1
  structuralComplete : ∀ profile, List.Mem profile (structuralFrontier roles)
  structuralNoDuplicates : (structuralFrontier roles).Nodup
  pendingComplete : ∀ profile, List.Mem profile (pendingFrontier roles)
  pendingNoDuplicates : (pendingFrontier roles).Nodup
  operationalComplete : ∀ profile, List.Mem profile (operationalFrontier roles)
  operationalNoDuplicates : (operationalFrontier roles).Nodup
  acceptedPayload : ∀ profile, StructuralAcceptedPayload roles profile
  normalizeAcceptedPayload : ∀ profile,
    StructuralAcceptedPayload roles profile → OperationalAcceptedPayload roles
  reductionsExact : reductions = buildExecutedOperationalReductionHistory roles
  discoveryWorkExact : discoveryWork = buildExecutedDiscoveryWorkHistory roles
  extensionalProjectionExact :
    extensionalProjection = buildExtensionalOperationalStabilityHistory roles
  acceptedPayloadExact : ∀ profile,
    acceptedPayload profile =
      everyStructuralObligationHasAcceptedPayload roles profile
  normalizeAcceptedPayloadExact : ∀ profile payload,
    normalizeAcceptedPayload profile payload =
      normalizeStructuralAcceptedPayload roles profile payload

def endogenousOperationalStabilityEvidence
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    EndogenousOperationalStabilityEvidence roles :=
  { reductions := buildExecutedOperationalReductionHistory roles
    discoveryWork := buildExecutedDiscoveryWorkHistory roles
    extensionalProjection := buildExtensionalOperationalStabilityHistory roles
    structuralExact := structuralWidth_eq_two_pow_stageCount roles
    pendingExact := pendingWidth_eq_structuralWidth roles
    executedExact := executedWidth_eq_one roles
    structuralComplete := structuralFrontier_complete roles
    structuralNoDuplicates := structuralFrontier_nodup roles
    pendingComplete := pendingFrontier_complete roles
    pendingNoDuplicates := pendingFrontier_nodup roles
    operationalComplete := operationalFrontier_complete roles
    operationalNoDuplicates := operationalFrontier_nodup roles
    acceptedPayload := everyStructuralObligationHasAcceptedPayload roles
    normalizeAcceptedPayload := normalizeStructuralAcceptedPayload roles
    reductionsExact := rfl
    discoveryWorkExact := rfl
    extensionalProjectionExact := rfl
    acceptedPayloadExact := fun _ => rfl
    normalizeAcceptedPayloadExact := fun _ _ => rfl }

/-- Public evidence built from the unique causal execution of an input. -/
def publicEndogenousOperationalStability (input : Nat) :
    EndogenousOperationalStabilityEvidence
      (executeConstitutiveResolution input).feedbackRoleHistory :=
  endogenousOperationalStabilityEvidence
    (executeConstitutiveResolution input).feedbackRoleHistory

/-- Positive histories have a strictly wider pending than executed carrier. -/
theorem executedWidth_lt_pendingWidth_of_positiveStageCount
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run)
    (positive : 0 < operationalStageCount roles) :
    executedWidth roles < pendingWidth roles := by
  have powerStrict := Constructive.two_pow_strictly_grows positive
  rw [executedWidth_eq_one roles,
    pendingWidth_eq_two_pow_stageCount roles]
  exact powerStrict

/-- A same-width singleton carrying the wrong sibling. -/
def wrongSingleton {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :=
  [(constructStage (depth + 1)).operationalRoot.child
    stage.discovery.var false stage.discovery.fresh]

theorem wrongSingleton_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (wrongSingleton run).length = 1 :=
  rfl

theorem wrongSingleton_ne_executedRetained {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    wrongSingleton run ≠ (executedSiblingReduction run).retained := by
  intro same
  exact executedSiblingStates_distinct run (List.cons.inj same).1

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.AllMeasuredCandidatesFail
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.failedCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.selectedCandidate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.failuresAreMeasured
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.selectedSucceeds
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.candidates_prefix_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.build
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.attempts_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedSuccessfulSearch.testedCandidates_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedDiscoveryWorkEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedDiscoveryWorkEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.executed_failed_candidate_rate
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialExecutedDiscovery_attempts_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialExecutedDiscovery_failed_candidate_rate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedDiscoveryWorkHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedDiscoveryWorkHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedDiscoveryWorkHistoryHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedDiscoveryWorkHistoryTail
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalOperationalStabilityHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExtensionalOperationalStabilityHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalOperationalStabilityHistoryHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalOperationalStabilityHistoryTail
#print axioms ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalStabilityEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.endogenousOperationalStabilityEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicEndogenousOperationalStability
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidth_lt_pendingWidth_of_positiveStageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.wrongSingleton
#print axioms ConstitutiveSearch.EndogenousDecomposition.wrongSingleton_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.wrongSingleton_ne_executedRetained
/- AXIOM_AUDIT_END -/
