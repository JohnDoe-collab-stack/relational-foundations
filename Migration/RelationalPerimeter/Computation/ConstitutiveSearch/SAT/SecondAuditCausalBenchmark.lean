import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ParametricSymmetricFamily

set_option linter.defProp false

/-!
# Second-audit causal decision benchmark

This module repairs the two causal gaps left by the earlier benchmark.

Discovery is endogenous: candidate variables are extracted from the current
residual formula, freshness is checked executably, candidates are explored in
order, and every attempted candidate is charged by the recursive search run.

The successful pipeline is indexed phase by phase:

`EndogenousFlipDiscovery -> DiscoverySchedule -> ValidatedDiscoverySchedule
  -> ExecutedDiscoverySchedule -> ExecutedTerminalArtifact -> Bool`.

The terminal constructor receives an execution object, not the original input.
Its scan can only inspect the state produced at the endpoint of that execution.
This is an API-level causal claim about this procedure; it is not a claim that
no other mathematical algorithm could decide the same extensional language.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Variable named by one literal. -/
def candidateVariable : Literal -> Var
  | .positive var => var
  | .negative var => var

end Literal

namespace Clause

/-- Candidate variables extracted by structural traversal of one clause. -/
def candidateVariables : Clause -> List Var
  | [] => []
  | literal :: rest =>
      literal.candidateVariable :: candidateVariables rest

end Clause

namespace Cnf

/-- Candidate variables extracted by structural traversal of a CNF. -/
def candidateVariables : Cnf -> List Var
  | [] => []
  | clause :: rest =>
      clause.candidateVariables ++ candidateVariables rest

end Cnf

/-- Counters produced by the structural candidate-extraction recursion. -/
structure CandidateExtractionStats where
  clauseVisits : Nat
  literalVisits : Nat
  candidatesEmitted : Nat
  deriving DecidableEq, Repr

/-- Candidate list together with the work that produced it. -/
structure CandidateExtractionRun where
  candidates : List Var
  stats : CandidateExtractionStats
  deriving DecidableEq, Repr

/-- Traverse one clause and charge every visited literal. -/
def extractClauseCandidateRun : Clause -> CandidateExtractionRun
  | [] =>
      { candidates := []
        stats :=
          { clauseVisits := 0
            literalVisits := 0
            candidatesEmitted := 0 } }
  | literal :: rest =>
      let tail := extractClauseCandidateRun rest
      { candidates := literal.candidateVariable :: tail.candidates
        stats :=
          { clauseVisits := 0
            literalVisits := tail.stats.literalVisits + 1
            candidatesEmitted := tail.stats.candidatesEmitted + 1 } }

/-- Traverse a CNF, charging every visited clause and literal. -/
def extractCnfCandidateRun : Cnf -> CandidateExtractionRun
  | [] =>
      { candidates := []
        stats :=
          { clauseVisits := 0
            literalVisits := 0
            candidatesEmitted := 0 } }
  | clause :: rest =>
      let head := extractClauseCandidateRun clause
      let tail := extractCnfCandidateRun rest
      { candidates := head.candidates ++ tail.candidates
        stats :=
          { clauseVisits := tail.stats.clauseVisits + 1
            literalVisits :=
              head.stats.literalVisits + tail.stats.literalVisits
            candidatesEmitted :=
              head.stats.candidatesEmitted + tail.stats.candidatesEmitted } }

/-- Instrumentation preserves the candidate order of the structural traversal. -/
theorem extractClauseCandidateRun_candidates
    (clause : Clause) :
    (extractClauseCandidateRun clause).candidates =
      clause.candidateVariables := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      change
          literal.candidateVariable ::
            (extractClauseCandidateRun rest).candidates =
          literal.candidateVariable :: Clause.candidateVariables rest
      rw [inductionHypothesis]

/-- Instrumentation preserves the candidate order of the complete CNF traversal. -/
theorem extractCnfCandidateRun_candidates
    (formula : Cnf) :
    (extractCnfCandidateRun formula).candidates =
      formula.candidateVariables := by
  induction formula with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      change
        (extractClauseCandidateRun clause).candidates ++
            (extractCnfCandidateRun rest).candidates =
          Clause.candidateVariables clause ++ Cnf.candidateVariables rest
      rw [
        extractClauseCandidateRun_candidates,
        inductionHypothesis
      ]

theorem extractClauseCandidateRun_candidatesEmitted
    (clause : Clause) :
    (extractClauseCandidateRun clause).stats.candidatesEmitted =
      (extractClauseCandidateRun clause).stats.literalVisits := by
  induction clause with
  | nil => rfl
  | cons _ rest inductionHypothesis =>
      change
        (extractClauseCandidateRun rest).stats.candidatesEmitted + 1 =
          (extractClauseCandidateRun rest).stats.literalVisits + 1
      rw [inductionHypothesis]

theorem extractCnfCandidateRun_candidatesEmitted
    (formula : Cnf) :
    (extractCnfCandidateRun formula).stats.candidatesEmitted =
      (extractCnfCandidateRun formula).stats.literalVisits := by
  induction formula with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      change
        (extractClauseCandidateRun clause).stats.candidatesEmitted +
            (extractCnfCandidateRun rest).stats.candidatesEmitted =
          (extractClauseCandidateRun clause).stats.literalVisits +
            (extractCnfCandidateRun rest).stats.literalVisits
      rw [extractClauseCandidateRun_candidatesEmitted, inductionHypothesis]

/-- Candidate extraction reads and instruments the current generated state itself. -/
def runCandidateExtraction
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
  CandidateExtractionRun :=
  extractCnfCandidateRun state.context.formula

theorem runCandidateExtraction_candidatesEmitted
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runCandidateExtraction state).stats.candidatesEmitted =
      (runCandidateExtraction state).stats.literalVisits :=
  extractCnfCandidateRun_candidatesEmitted state.context.formula

/-- Compatibility projection of the candidates produced by the extraction run. -/
def extractStructuralCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var :=
  (runCandidateExtraction state).candidates

/--
Successful endogenous discovery at one current state.  The selected variable,
freshness witness, sibling endpoints and structural relation are one dependent
piece of data.
-/
structure CandidateFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) where
  fresh :
    StructuralDecisionsAvoid
      candidate
      state.context.decisions
  relation :
    GeneratedStructuralFlipAtRelation
      candidate
      (GeneratedStructuralBranchContext.child
        state candidate false fresh)
      (GeneratedStructuralBranchContext.child
        state candidate true fresh)

/-- Selected variable together with the evidence produced while trying it. -/
abbrev EndogenousFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :=
  Sigma (CandidateFlipDiscovery state)

namespace EndogenousFlipDiscovery

def var
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) : Var :=
  discovery.1

def fresh
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    StructuralDecisionsAvoid
      discovery.var
      state.context.decisions :=
  discovery.2.fresh

def relation
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    GeneratedStructuralFlipAtRelation
      discovery.var
      (GeneratedStructuralBranchContext.child
        state discovery.var false discovery.fresh)
      (GeneratedStructuralBranchContext.child
        state discovery.var true discovery.fresh) :=
  discovery.2.relation

end EndogenousFlipDiscovery

/-- Try one extracted variable, including executable freshness checking. -/
def tryEndogenousFlipCandidate
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) :
    Option (CandidateFlipDiscovery state candidate) :=
  match freshness :
      structuralDecisionsAvoidCheck
        candidate
        state.context.decisions with
  | false => none
  | true =>
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      match
        (generatedStructuralFlipAtSearch
          rootFormula
          candidate).find
            (GeneratedStructuralBranchContext.child
              state candidate false fresh)
            (GeneratedStructuralBranchContext.child
              state candidate true fresh) with
      | none => none
      | some relation =>
          some
            { fresh := fresh
              relation := relation }

/-- A supplied positive relation certifies success of the executable attempt. -/
theorem tryEndogenousFlipCandidate_found_of_relation
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var)
    (freshness :
      structuralDecisionsAvoidCheck
          candidate
          state.context.decisions =
        true)
    (relation :
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      GeneratedStructuralFlipAtRelation
        candidate
        (GeneratedStructuralBranchContext.child
          state candidate false fresh)
        (GeneratedStructuralBranchContext.child
          state candidate true fresh)) :
    tryEndogenousFlipCandidate state candidate ≠ none := by
  unfold tryEndogenousFlipCandidate
  split
  · rename_i checkFalse
    rw [checkFalse] at freshness
    cases freshness
  · rename_i checkTrue
    have proofExact : checkTrue = freshness :=
      Subsingleton.elim _ _
    cases proofExact
    dsimp [generatedStructuralFlipAtSearch]
    rw [
      dif_pos relation.formulaExact,
      dif_pos relation.decisionsExact
    ]
    intro impossible
    cases impossible

/-- A certified formula mismatch makes one executable candidate attempt fail. -/
theorem tryEndogenousFlipCandidate_none_of_formula_mismatch
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var)
    (freshness :
      structuralDecisionsAvoidCheck
          candidate
          state.context.decisions =
        true)
    (formulaMismatch :
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      (GeneratedStructuralBranchContext.child
          state candidate true fresh).context.formula ≠
        Cnf.flipAt candidate
          (GeneratedStructuralBranchContext.child
            state candidate false fresh).context.formula) :
    tryEndogenousFlipCandidate state candidate = none := by
  unfold tryEndogenousFlipCandidate
  split
  · rename_i checkFalse
    rw [checkFalse] at freshness
  · rename_i checkTrue
    have proofExact : checkTrue = freshness :=
      Subsingleton.elim _ _
    cases proofExact
    dsimp [generatedStructuralFlipAtSearch]
    rw [dif_neg formulaMismatch]

/-- Outcome and actual number of attempted candidates. -/
structure EndogenousDiscoveryOutcome
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  discovered? : Option (EndogenousFlipDiscovery state)
  attempts : Nat

/-- Structurally recursive exploration charging one unit per attempted head. -/
def exploreStructuralCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var -> EndogenousDiscoveryOutcome state
  | [] =>
      { discovered? := none
        attempts := 0 }
  | candidate :: rest =>
      match tryEndogenousFlipCandidate state candidate with
      | some candidateDiscovery =>
          { discovered? :=
              some ⟨candidate, candidateDiscovery⟩
            attempts := 1 }
      | none =>
          let tail :=
            exploreStructuralCandidates state rest
          { discovered? := tail.discovered?
            attempts := tail.attempts + 1 }

/-- Full discovery run records both extracted candidates and exploration. -/
structure EndogenousDiscoveryRun
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  extraction : CandidateExtractionRun
  outcome : EndogenousDiscoveryOutcome state

namespace EndogenousDiscoveryRun

/-- Candidates are exposed only as the result of the instrumented extraction. -/
def candidates
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (run : EndogenousDiscoveryRun state) : List Var :=
  run.extraction.candidates

end EndogenousDiscoveryRun

/-- Current state -> extraction -> exploration. -/
def runEndogenousFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    EndogenousDiscoveryRun state :=
  let candidates :=
    runCandidateExtraction state
  { extraction := candidates
    outcome :=
      exploreStructuralCandidates
        state
        candidates.candidates }

/-- A schedule indexed by, and containing no data beyond, its discovery. -/
inductive DiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) : Type where
  | fromDiscovery : DiscoverySchedule discovery

/-- Canonical schedule production from discovered data only. -/
def scheduleFromDiscovery
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    DiscoverySchedule discovery :=
  .fromDiscovery

namespace DiscoverySchedule

/-- The unique local schedule entry is reconstructed from the discovery index. -/
def entry
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (_schedule : DiscoverySchedule discovery) :
    ConstitutedLocalWitness rootFormula :=
  { var := discovery.1
    source :=
      GeneratedStructuralBranchContext.child
        state
        discovery.1
        false
        discovery.2.fresh
    target :=
      GeneratedStructuralBranchContext.child
        state
        discovery.1
        true
        discovery.2.fresh
    relation := discovery.2.relation }

end DiscoverySchedule

/-- Schedule plus the production counter emitted by its constructor run. -/
structure DiscoveryScheduleProductionRun
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) where
  schedule : DiscoverySchedule discovery
  atomsEmitted : Nat
  atomsExact : atomsEmitted = schedule.entry.code.size

/-- Produce the unique schedule from discovery and charge its emitted atom. -/
def runDiscoveryScheduleProduction
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    DiscoveryScheduleProductionRun discovery :=
  let schedule := scheduleFromDiscovery discovery
  { schedule := schedule
    atomsEmitted := 1
    atomsExact := by
      exact (ConstitutedLocalWitness.code_size schedule.entry).symm }

/-- The schedule-production run emits exactly one constituted atom. -/
theorem runDiscoveryScheduleProduction_atoms
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    (runDiscoveryScheduleProduction discovery).atomsEmitted = 1 :=
  rfl

/-- Execute the validator for the unique discovered schedule atom. -/
def runDiscoveryScheduleValidation
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    SearchableCodeValidationRun :=
  match
    (generatedStructuralFlipAtSearch
      rootFormula
      schedule.entry.var).find
        schedule.entry.source
        schedule.entry.target with
  | some _ =>
      { success := true
        primitiveQueries := 1
        validatedAtoms := 1 }
  | none =>
      { success := false
        primitiveQueries := 1
        validatedAtoms := 1 }

/-- Validation cost is read from the validator run and is exactly one query. -/
theorem runDiscoveryScheduleValidation_queries
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    (runDiscoveryScheduleValidation schedule).primitiveQueries = 1 := by
  unfold runDiscoveryScheduleValidation
  split <;> rfl

theorem runDiscoveryScheduleValidation_validatedAtoms
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    (runDiscoveryScheduleValidation schedule).validatedAtoms = 1 := by
  unfold runDiscoveryScheduleValidation
  split <;> rfl

/-- Validation data is indexed by the exact schedule it validates. -/
structure ValidatedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) where
  run : SearchableCodeValidationRun
  runExact :
    run = runDiscoveryScheduleValidation schedule
  success : run.success = true

/-- Execute validation and retain the exact run that established success. -/
def validateDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    ValidatedDiscoverySchedule schedule :=
  { run :=
      runDiscoveryScheduleValidation schedule
    runExact := rfl
    success := by
      cases schedule
      change
        (runDiscoveryScheduleValidation
          (scheduleFromDiscovery discovery)).success = true
      unfold runDiscoveryScheduleValidation
      dsimp [
        scheduleFromDiscovery,
        DiscoverySchedule.entry
      ]
      dsimp [generatedStructuralFlipAtSearch]
      rw [
        dif_pos discovery.2.relation.formulaExact,
        dif_pos discovery.2.relation.decisionsExact
      ] }

/--
Local execution is indexed by the validated schedule.  A value of this type
contains the actual closure-search run and positive evidence that it found a
code for the schedule endpoints.  It also stores that returned code and the
state produced at its indexed target as data for the next phase.
-/
structure ExecutedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) where
  run :
    ClosureSearchRun
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        schedule.entry.var)
      schedule.entry.source
      schedule.entry.target
  runExact : run = schedule.entry.executionRun
  code :
    TransportClosure
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        schedule.entry.var)
      schedule.entry.source
      schedule.entry.target
  codeExact : run.code? = some code
  producedState : GeneratedStructuralBranchContext rootFormula
  producedStateExact : producedState = schedule.entry.target

/-- Execute the validated local schedule. -/
def executeValidatedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    ExecutedDiscoverySchedule validated :=
  let run := schedule.entry.executionRun
  match exactCode : run.code? with
  | none =>
      False.elim
        (schedule.entry.executionRun_found exactCode)
  | some code =>
      { run := run
        runExact := rfl
        code := code
        codeExact := exactCode
        producedState := schedule.entry.target
        producedStateExact := rfl }

/-- The actual one-atom execution run reports one query and no composition. -/
theorem executeValidatedDiscoverySchedule_stats
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    (executeValidatedDiscoverySchedule
        validated).run.stats.primitiveQueries = 1 /\
      (executeValidatedDiscoverySchedule
        validated).run.stats.compositionCandidates = 0 := by
  have runExact :=
    (executeValidatedDiscoverySchedule validated).runExact
  rw [runExact]
  cases schedule
  change
    (searchTransportClosureBounded
        (generatedStructuralFlipAtSearch
          rootFormula
          discovery.1)
        []
        1
        (GeneratedStructuralBranchContext.child
          state discovery.1 false discovery.2.fresh)
        (GeneratedStructuralBranchContext.child
          state discovery.1 true discovery.2.fresh)).stats.primitiveQueries = 1 /\
      (searchTransportClosureBounded
        (generatedStructuralFlipAtSearch
          rootFormula
          discovery.1)
        []
        1
        (GeneratedStructuralBranchContext.child
          state discovery.1 false discovery.2.fresh)
        (GeneratedStructuralBranchContext.child
          state discovery.1 true discovery.2.fresh)).stats.compositionCandidates = 0
  unfold searchTransportClosureBounded
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos discovery.2.relation.formulaExact,
    dif_pos discovery.2.relation.decisionsExact
  ]
  exact ⟨rfl, rfl⟩

/-- The execution-produced state is exactly the target indexed by its returned code. -/
theorem ExecutedDiscoverySchedule.producedState_eq_target
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) :
    execution.producedState = schedule.entry.target :=
  execution.producedStateExact

/-- Statistics produced by an executable scan of an executed terminal CNF. -/
structure ExecutedTerminalScan where
  containsEmpty : Bool
  clauseChecks : Nat

/-- Terminal scan with cost generated by its structural recursion. -/
def scanExecutedTerminal : Cnf -> ExecutedTerminalScan
  | [] =>
      { containsEmpty := false
        clauseChecks := 0 }
  | clause :: rest =>
      if clause = [] then
        { containsEmpty := true
          clauseChecks := 1 }
      else
        let tail := scanExecutedTerminal rest
        { containsEmpty := tail.containsEmpty
          clauseChecks := tail.clauseChecks + 1 }

/--
Terminal artifact indexed by the execution that produced its state.  There is
no input or independently supplied state in this interface.
-/
structure ExecutedTerminalArtifact
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) where
  scan : ExecutedTerminalScan
  scanExact :
    scan =
      scanExecutedTerminal
        execution.producedState.context.formula

/-- Construct the terminal only from the completed execution. -/
def terminalFromExecution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) :
    ExecutedTerminalArtifact execution :=
  { scan :=
      scanExecutedTerminal
        execution.producedState.context.formula
    scanExact := rfl }

/-- Positive provenance equation carried by every terminal artifact. -/
theorem ExecutedTerminalArtifact.scan_from_execution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution) :
    terminal.scan =
      scanExecutedTerminal
        execution.producedState.context.formula :=
  terminal.scanExact

/-- The decision reads only the executed terminal artifact. -/
def decideExecutedTerminal
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution) : Bool :=
  !terminal.scan.containsEmpty

/-! ## Concrete nonconstant family using the generic causal pipeline -/

/-- The useful split variable changes with the input. -/
def causalDecisionSplitVar (input : Nat) : Var :=
  input + 2

/-- A distinct anchor derived from the useful split variable. -/
def causalDecisionAnchorVar (input : Nat) : Var :=
  causalDecisionSplitVar input + 1

/-- Alternating, executable semantic signal with unbounded YES and NO inputs. -/
def causalDecisionSignal : Nat → Bool
  | 0 => true
  | input + 1 => !(causalDecisionSignal input)

/--
The background is empty on signal-true inputs and contains an explicit
empty-clause obstruction on signal-false inputs.
-/
def causalDecisionBackground (input : Nat) : Cnf :=
  match causalDecisionSignal input with
  | true => []
  | false => [[]]

/-- Presented formula; the procedure is not separately given its split variable. -/
def causalDecisionFormula (input : Nat) : Cnf :=
  symmetricBlockFamily
    (causalDecisionSplitVar input)
    (causalDecisionAnchorVar input)
    (causalDecisionBackground input)

/-- Current root state from which candidate extraction begins. -/
def causalDecisionRoot
    (input : Nat) :
    GeneratedStructuralBranchContext
      (causalDecisionFormula input) :=
  GeneratedStructuralBranchContext.root
    (causalDecisionFormula input)

/-- Every variable is fresh at a generated root. -/
theorem causalDecisionRootFresh
    (input : Nat)
    (var : Var) :
    StructuralDecisionsAvoid
      var
      (causalDecisionRoot input).context.decisions :=
  True.intro

/-- Freshness witness produced by the executable root check. -/
def causalDecisionCheckedFresh
    (input : Nat) :
    StructuralDecisionsAvoid
      (causalDecisionSplitVar input)
      (causalDecisionRoot input).context.decisions :=
  structuralDecisionsAvoid_of_check_true
    (causalDecisionSplitVar input)
    (causalDecisionRoot input).context.decisions
    rfl

/-- The derived anchor is distinct from the derived split variable. -/
theorem causalDecisionAnchor_ne_split
    (input : Nat) :
    causalDecisionAnchorVar input ≠
      causalDecisionSplitVar input := by
  unfold causalDecisionAnchorVar
  exact Nat.ne_of_gt (Nat.lt_succ_self _)

/-- The benchmark background contains no literal at all. -/
theorem causalDecisionBackground_avoids
    (input : Nat) :
    Cnf.AvoidsVar
      (causalDecisionSplitVar input)
      (causalDecisionBackground input) := by
  unfold causalDecisionBackground
  cases causalDecisionSignal input with
  | false => exact ⟨True.intro, True.intro⟩
  | true => exact True.intro

/-- The useful sibling relation exists for the candidate encoded in the formula. -/
theorem causalDecision_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (causalDecisionFormula input)
      (causalDecisionSplitVar input) := by
  unfold causalDecisionFormula
  apply symmetricBlockFamily_flipSymmetric
  · exact causalDecisionAnchor_ne_split input
  · exact causalDecisionBackground_avoids input

/-- Exact witness used only to prove completeness of executable discovery. -/
def causalDecisionExpectedRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      (causalDecisionSplitVar input)
      (GeneratedStructuralBranchContext.child
        (causalDecisionRoot input)
        (causalDecisionSplitVar input)
        false
        (causalDecisionCheckedFresh input))
      (GeneratedStructuralBranchContext.child
        (causalDecisionRoot input)
        (causalDecisionSplitVar input)
        true
        (causalDecisionCheckedFresh input)) :=
  flipSymmetricSiblingRelation
    (causalDecisionRoot input)
    (causalDecisionSplitVar input)
    (causalDecisionCheckedFresh input)
    (causalDecision_flipSymmetric input)

/-- The first candidate is extracted from syntax rather than passed separately. -/
theorem causalDecision_firstCandidate
    (input : Nat) :
    exists rest,
      extractStructuralCandidates
          (causalDecisionRoot input) =
        causalDecisionSplitVar input :: rest := by
  refine
    ⟨[causalDecisionAnchorVar input,
        causalDecisionSplitVar input,
        causalDecisionAnchorVar input] ++
        (causalDecisionBackground input).candidateVariables,
      ?_⟩
  unfold extractStructuralCandidates runCandidateExtraction
  rw [extractCnfCandidateRun_candidates]
  rfl

/-- The syntactically extracted useful candidate succeeds when tried. -/
theorem causalDecision_candidate_found
    (input : Nat) :
    tryEndogenousFlipCandidate
        (causalDecisionRoot input)
        (causalDecisionSplitVar input) ≠
      none := by
  exact
    tryEndogenousFlipCandidate_found_of_relation
      (causalDecisionRoot input)
      (causalDecisionSplitVar input)
      rfl
      (causalDecisionExpectedRelation input)

/-- Endogenous discovery succeeds after exactly one actually attempted candidate. -/
theorem causalDecision_discovery_found
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery /\
      discovery.var = causalDecisionSplitVar input /\
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.attempts = 1 := by
  rcases causalDecision_firstCandidate input with
    ⟨rest, candidatesExact⟩
  cases found :
      tryEndogenousFlipCandidate
        (causalDecisionRoot input)
        (causalDecisionSplitVar input) with
  | none =>
      exact False.elim ((causalDecision_candidate_found input) found)
  | some candidateDiscovery =>
      let discovery : EndogenousFlipDiscovery (causalDecisionRoot input) :=
        ⟨causalDecisionSplitVar input, candidateDiscovery⟩
      refine ⟨discovery, ?_, rfl, ?_⟩
      · change
          (exploreStructuralCandidates
            (causalDecisionRoot input)
            (extractStructuralCandidates
              (causalDecisionRoot input))).discovered? =
            some discovery
        rw [candidatesExact]
        unfold exploreStructuralCandidates
        rw [found]
      · change
          (exploreStructuralCandidates
            (causalDecisionRoot input)
            (extractStructuralCandidates
              (causalDecisionRoot input))).attempts = 1
        rw [candidatesExact]
        unfold exploreStructuralCandidates
        rw [found]

/-- Any witness returned by the benchmark run carries the extracted split variable. -/
theorem causalDecision_discovered_var
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (found :
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery) :
    discovery.var = causalDecisionSplitVar input := by
  rcases causalDecision_discovery_found input with
    ⟨expected, expectedFound, expectedVar, _attempts⟩
  rw [found] at expectedFound
  have same : discovery = expected :=
    Option.some.inj expectedFound
  rw [same]
  exact expectedVar

/-- Exact retained residual for a true child at the derived split variable. -/
theorem causalDecision_trueChild_formula
    (input : Nat)
    (fresh :
      StructuralDecisionsAvoid
        (causalDecisionSplitVar input)
        (causalDecisionRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (causalDecisionRoot input)
      (causalDecisionSplitVar input)
      true
      fresh).context.formula =
        symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input) ::
          causalDecisionBackground input := by
  change
    branchResidual
        (causalDecisionFormula input)
        (causalDecisionSplitVar input)
        true =
      symmetricNegativeClause
          (causalDecisionSplitVar input)
          (causalDecisionAnchorVar input) ::
        causalDecisionBackground input
  unfold causalDecisionFormula
  unfold symmetricBlockFamily
  have positiveHit :
      Clause.containsLiteral
          (Literal.forValue
            (causalDecisionSplitVar input)
            true)
          (symmetricPositiveClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input)) =
        true := by
    unfold symmetricPositiveClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have negativeMiss :
      Clause.containsLiteral
          (Literal.forValue
            (causalDecisionSplitVar input)
            true)
          (symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input)) =
        false := by
    unfold symmetricNegativeClause
    dsimp [Literal.forValue]
    have firstDifferent :
        Literal.negative (causalDecisionSplitVar input) ≠
          Literal.positive (causalDecisionSplitVar input) := by
      intro impossible
      cases impossible
    have secondDifferent :
        Literal.positive (causalDecisionAnchorVar input) ≠
          Literal.positive (causalDecisionSplitVar input) := by
      intro impossible
      have sameVar :
          causalDecisionAnchorVar input =
            causalDecisionSplitVar input :=
        Literal.positive.inj impossible
      exact (causalDecisionAnchor_ne_split input) sameVar
    rw [Clause.containsLiteral, if_neg firstDifferent]
    rw [Clause.containsLiteral, if_neg secondDifferent]
    rfl
  rw [
    branchResidual_cons_hit
      (symmetricPositiveClause
        (causalDecisionSplitVar input)
        (causalDecisionAnchorVar input))
      (symmetricNegativeClause
          (causalDecisionSplitVar input)
          (causalDecisionAnchorVar input) ::
        causalDecisionBackground input)
      (causalDecisionSplitVar input)
      true
      positiveHit
  ]
  rw [
    branchResidual_cons_miss
      (symmetricNegativeClause
        (causalDecisionSplitVar input)
        (causalDecisionAnchorVar input))
      (causalDecisionBackground input)
      (causalDecisionSplitVar input)
      true
      negativeMiss
  ]
  rw [
    Cnf.branchResidual_eq_self
      (causalDecisionBackground_avoids input)
      true
  ]

/-- Full typed tail of the procedure after successful endogenous discovery. -/
def causalTerminalAfterDiscovery
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input)) :=
  terminalFromExecution
    (executeValidatedDiscoverySchedule
      (validateDiscoverySchedule
        (scheduleFromDiscovery discovery)))

/-- The post-discovery decision is a function of the executed terminal only. -/
def causalDecisionAfterDiscovery
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input)) : Bool :=
  decideExecutedTerminal
    (causalTerminalAfterDiscovery input discovery)

/-- The successful terminal is exactly the state indexed by the discovered execution. -/
theorem causalDecisionAfterDiscovery_terminal_formula
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (selected :
      discovery.var = causalDecisionSplitVar input) :
    (causalTerminalAfterDiscovery
      input
      discovery).scan =
      scanExecutedTerminal
        (symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input) ::
          causalDecisionBackground input) := by
  cases discovery with
  | mk candidate evidence =>
      change candidate = causalDecisionSplitVar input at selected
      subst candidate
      unfold causalTerminalAfterDiscovery
      rw [ExecutedTerminalArtifact.scan_from_execution]
      rw [ExecutedDiscoverySchedule.producedState_eq_target]
      change
        scanExecutedTerminal
            ((GeneratedStructuralBranchContext.child
              (causalDecisionRoot input)
              (causalDecisionSplitVar input)
              true
              evidence.fresh).context.formula) =
          scanExecutedTerminal
            (symmetricNegativeClause
                (causalDecisionSplitVar input)
                (causalDecisionAnchorVar input) ::
              causalDecisionBackground input)
      rw [causalDecision_trueChild_formula input evidence.fresh]

/-- Extensional SAT acceptance of the presented benchmark formula. -/
def CausalDecisionAccept (input : Nat) : Prop :=
  exists assignment : Assignment,
    Satisfies assignment (causalDecisionFormula input)

/-- Concrete satisfying assignment for the YES instance. -/
def causalDecisionYesAssignment : Assignment
  | _ => true

/-- Every signal-true input is a genuine satisfying instance. -/
theorem causalDecision_signal_true_accepts
    {input : Nat}
    (signalTrue : causalDecisionSignal input = true) :
    CausalDecisionAccept input := by
  unfold CausalDecisionAccept causalDecisionFormula
  unfold causalDecisionBackground
  rw [signalTrue]
  exact
    ⟨causalDecisionYesAssignment,
      .cons rfl (.cons rfl .nil)⟩

/-- Every signal-false input contains the explicit empty-clause obstruction. -/
theorem causalDecision_signal_false_rejects
    {input : Nat}
    (signalFalse : causalDecisionSignal input = false) :
    ¬ CausalDecisionAccept input := by
  intro accepted
  rcases accepted with ⟨assignment, satisfaction⟩
  unfold causalDecisionFormula at satisfaction
  unfold causalDecisionBackground at satisfaction
  rw [signalFalse] at satisfaction
  cases satisfaction with
  | cons firstSatisfied restSatisfied =>
      cases restSatisfied with
      | cons secondSatisfied finalSatisfied =>
          cases finalSatisfied with
          | cons emptySatisfied tailSatisfied =>
              change false = true at emptySatisfied
              cases emptySatisfied

/-- The extensional SAT language is exactly the alternating semantic signal. -/
theorem causalDecision_accept_iff_signal
    (input : Nat) :
    CausalDecisionAccept input <->
      causalDecisionSignal input = true := by
  constructor
  · intro accepted
    cases signalExact : causalDecisionSignal input with
    | false =>
        exact
          False.elim
            ((causalDecision_signal_false_rejects signalExact)
              accepted)
    | true => exact rfl
  · intro signalTrue
    exact causalDecision_signal_true_accepts signalTrue

/-- Two successor steps preserve the alternating signal. -/
theorem causalDecisionSignal_add_two
    (input : Nat) :
    causalDecisionSignal (input + 2) =
      causalDecisionSignal input := by
  induction input with
  | zero =>
      rfl
  | succ input inductionHypothesis =>
      change
        Bool.not (causalDecisionSignal (input + 2)) =
          Bool.not (causalDecisionSignal input)
      exact
        congrArg
          (fun value : Bool => !value)
          inductionHypothesis

/-- Canonical unbounded YES indices. -/
def causalDecisionYesInput : Nat → Nat
  | 0 => 0
  | index + 1 => causalDecisionYesInput index + 2

/-- Canonical unbounded NO indices. -/
def causalDecisionNoInput : Nat → Nat
  | 0 => 1
  | index + 1 => causalDecisionNoInput index + 2

/-- Every canonical YES index is accepted. -/
theorem causalDecisionYesInput_accepts
    (index : Nat) :
    CausalDecisionAccept (causalDecisionYesInput index) := by
  apply causalDecision_signal_true_accepts
  induction index with
  | zero =>
      rfl
  | succ index inductionHypothesis =>
      exact
        Eq.trans
          (causalDecisionSignal_add_two
            (causalDecisionYesInput index))
          inductionHypothesis

/-- Every canonical NO index is rejected. -/
theorem causalDecisionNoInput_rejects
    (index : Nat) :
    ¬ CausalDecisionAccept (causalDecisionNoInput index) := by
  apply causalDecision_signal_false_rejects
  induction index with
  | zero =>
      rfl
  | succ index inductionHypothesis =>
      exact
        Eq.trans
          (causalDecisionSignal_add_two
            (causalDecisionNoInput index))
          inductionHypothesis

/-- The YES witnesses are strictly increasing, hence not a finite singleton. -/
theorem causalDecisionYesInput_strict
    (index : Nat) :
    causalDecisionYesInput index <
      causalDecisionYesInput (index + 1) :=
  Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)

/-- The NO witnesses are also strictly increasing. -/
theorem causalDecisionNoInput_strict
    (index : Nat) :
    causalDecisionNoInput index <
      causalDecisionNoInput (index + 1) :=
  Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)

/-- The terminal-only readout is correct once discovery has selected its result. -/
theorem causalDecisionAfterDiscovery_correct
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (selected :
      discovery.var = causalDecisionSplitVar input) :
    causalDecisionAfterDiscovery input discovery = true <->
      CausalDecisionAccept input := by
  unfold causalDecisionAfterDiscovery
  unfold decideExecutedTerminal
  rw [
    causalDecisionAfterDiscovery_terminal_formula
      input
      discovery
      selected
  ]
  cases signalExact : causalDecisionSignal input with
  | true =>
    unfold causalDecisionBackground
    rw [signalExact]
    change true = true <-> CausalDecisionAccept input
    exact
      ⟨fun _accepted => causalDecision_signal_true_accepts signalExact,
        fun _witness => rfl⟩
  | false =>
    unfold causalDecisionBackground
    rw [signalExact]
    change false = true <-> CausalDecisionAccept input
    exact
      ⟨fun impossible => Bool.noConfusion impossible,
        fun accepted =>
          False.elim
            ((causalDecision_signal_false_rejects signalExact)
              accepted)⟩

/--
Correct terminal formula for any retained typed chain, not only the canonical
constructor used by `causalTerminalAfterDiscovery`.
-/
theorem executedTerminalArtifact_selected_formula
    (input : Nat)
    {discovery : EndogenousFlipDiscovery (causalDecisionRoot input)}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution)
    (selected : discovery.var = causalDecisionSplitVar input) :
    terminal.scan =
      scanExecutedTerminal
        (symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input) ::
          causalDecisionBackground input) := by
  rw [terminal.scanExact]
  rw [execution.producedStateExact]
  cases schedule
  cases discovery with
  | mk candidate evidence =>
      change candidate = causalDecisionSplitVar input at selected
      subst candidate
      change
        scanExecutedTerminal
            ((GeneratedStructuralBranchContext.child
              (causalDecisionRoot input)
              (causalDecisionSplitVar input)
              true
              evidence.fresh).context.formula) =
          scanExecutedTerminal
            (symmetricNegativeClause
                (causalDecisionSplitVar input)
                (causalDecisionAnchorVar input) ::
              causalDecisionBackground input)
      rw [causalDecision_trueChild_formula input evidence.fresh]

/-- Every terminal in a retained selected chain decides the benchmark correctly. -/
theorem decideExecutedTerminal_selected_correct
    (input : Nat)
    {discovery : EndogenousFlipDiscovery (causalDecisionRoot input)}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution)
    (selected : discovery.var = causalDecisionSplitVar input) :
    decideExecutedTerminal terminal = true <->
      CausalDecisionAccept input := by
  unfold decideExecutedTerminal
  rw [executedTerminalArtifact_selected_formula input terminal selected]
  cases signalExact : causalDecisionSignal input with
  | true =>
    unfold causalDecisionBackground
    rw [signalExact]
    change true = true <-> CausalDecisionAccept input
    exact
      ⟨fun _accepted => causalDecision_signal_true_accepts signalExact,
        fun _witness => rfl⟩
  | false =>
    unfold causalDecisionBackground
    rw [signalExact]
    change false = true <-> CausalDecisionAccept input
    exact
      ⟨fun impossible => Bool.noConfusion impossible,
        fun accepted =>
          False.elim
            ((causalDecision_signal_false_rejects signalExact)
              accepted)⟩

/-- Separate costs, each read from the run that produced that phase. -/
structure CausalDecisionProcedureStats where
  extractedCandidates : Nat
  extractionClauseVisits : Nat
  extractionLiteralVisits : Nat
  discoveryAttempts : Nat
  scheduleAtoms : Nat
  validationQueries : Nat
  executionPrimitiveQueries : Nat
  executionCompositionCandidates : Nat
  terminalChecks : Nat

namespace CausalDecisionProcedureStats

def total (stats : CausalDecisionProcedureStats) : Nat :=
  stats.extractionClauseVisits +
    stats.extractionLiteralVisits +
    stats.discoveryAttempts +
    stats.scheduleAtoms +
    stats.validationQueries +
    stats.executionPrimitiveQueries +
    stats.executionCompositionCandidates +
    stats.terminalChecks

end CausalDecisionProcedureStats

/-- Observable result and phase-local costs of the complete procedure. -/
structure CausalDecisionProcedureRun where
  result : Bool
  terminalProduced : Bool
  stats : CausalDecisionProcedureStats

/-- Phase costs reconstructed only from the retained producer runs. -/
def causalDecisionStatsFromPhases
    {input : Nat}
    (discoveryRun :
      EndogenousDiscoveryRun (causalDecisionRoot input))
    {discovery :
      EndogenousFlipDiscovery (causalDecisionRoot input)}
    (scheduleRun : DiscoveryScheduleProductionRun discovery)
    (validated : ValidatedDiscoverySchedule scheduleRun.schedule)
    (execution : ExecutedDiscoverySchedule validated)
    (terminal : ExecutedTerminalArtifact execution) :
    CausalDecisionProcedureStats :=
  { extractedCandidates := discoveryRun.candidates.length
    extractionClauseVisits :=
      discoveryRun.extraction.stats.clauseVisits
    extractionLiteralVisits :=
      discoveryRun.extraction.stats.literalVisits
    discoveryAttempts := discoveryRun.outcome.attempts
    scheduleAtoms := scheduleRun.atomsEmitted
    validationQueries := validated.run.primitiveQueries
    executionPrimitiveQueries :=
      execution.run.stats.primitiveQueries
    executionCompositionCandidates :=
      execution.run.stats.compositionCandidates
    terminalChecks := terminal.scan.clauseChecks }

/-!
Unlike the observable projection below, this is the constitutive output of the
procedure.  Every phase output is retained and the type of each later output is
indexed by the exact preceding output.  The result is accompanied by an
equation showing that it was read from the retained terminal artifact.
-/
structure CausalDecisionCertifiedRun (input : Nat) where
  discoveryRun :
    EndogenousDiscoveryRun (causalDecisionRoot input)
  discoveryRunExact :
    discoveryRun =
      runEndogenousFlipDiscovery (causalDecisionRoot input)
  discovery :
    EndogenousFlipDiscovery (causalDecisionRoot input)
  discoveredExact :
    discoveryRun.outcome.discovered? = some discovery
  scheduleRun : DiscoveryScheduleProductionRun discovery
  scheduleRunExact :
    scheduleRun = runDiscoveryScheduleProduction discovery
  validated : ValidatedDiscoverySchedule scheduleRun.schedule
  execution : ExecutedDiscoverySchedule validated
  terminal : ExecutedTerminalArtifact execution
  result : Bool
  resultExact : result = decideExecutedTerminal terminal
  stats : CausalDecisionProcedureStats
  statsExact :
    stats =
      causalDecisionStatsFromPhases
        discoveryRun
        scheduleRun
        validated
        execution
        terminal

/-- Build the retained causal chain from one result of actual discovery. -/
def causalDecisionCertifiedAfterDiscovery
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (discoveredExact :
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery) :
    CausalDecisionCertifiedRun input :=
  let discoveryRun :=
    runEndogenousFlipDiscovery (causalDecisionRoot input)
  let scheduleRun := runDiscoveryScheduleProduction discovery
  let validated := validateDiscoverySchedule scheduleRun.schedule
  let execution := executeValidatedDiscoverySchedule validated
  let terminal := terminalFromExecution execution
  { discoveryRun := discoveryRun
    discoveryRunExact := rfl
    discovery := discovery
    discoveredExact := discoveredExact
    scheduleRun := scheduleRun
    scheduleRunExact := rfl
    validated := validated
    execution := execution
    terminal := terminal
    result := decideExecutedTerminal terminal
    resultExact := rfl
    stats :=
      causalDecisionStatsFromPhases
        discoveryRun
        scheduleRun
        validated
        execution
        terminal
    statsExact := rfl }

/--
Execute discovery and retain every causally linked phase output.  The impossible
failure branch is eliminated by the proved completeness of endogenous
discovery for this family; no replacement terminal is reconstructed from the
input.
-/
def executeCausalDecisionCertified
    (input : Nat) : CausalDecisionCertifiedRun input :=
  let discoveryRun :=
    runEndogenousFlipDiscovery (causalDecisionRoot input)
  match discovered : discoveryRun.outcome.discovered? with
  | none =>
      False.elim (by
        rcases causalDecision_discovery_found input with
          ⟨expected, expectedFound, _selected, _attempts⟩
        change discoveryRun.outcome.discovered? = some expected at expectedFound
        rw [discovered] at expectedFound
        cases expectedFound)
  | some discovery =>
      causalDecisionCertifiedAfterDiscovery
        input
        discovery
        discovered

/-- The retained discovery is exactly the result of the public discovery run. -/
theorem CausalDecisionCertifiedRun.discovery_from_actual_run
    {input : Nat}
    (run : CausalDecisionCertifiedRun input) :
    (runEndogenousFlipDiscovery
      (causalDecisionRoot input)).outcome.discovered? =
        some run.discovery :=
  Eq.trans
    (congrArg
      (fun discoveryRun => discoveryRun.outcome.discovered?)
      run.discoveryRunExact).symm
    run.discoveredExact

/-- The certified result is the readout of its retained terminal and is correct. -/
theorem CausalDecisionCertifiedRun.result_correct
    {input : Nat}
    (run : CausalDecisionCertifiedRun input) :
    run.result = true <-> CausalDecisionAccept input := by
  have selected :=
    causalDecision_discovered_var
      input
      run.discovery
      run.discovery_from_actual_run
  have terminalCorrect :=
    decideExecutedTerminal_selected_correct
      input
      run.terminal
      selected
  constructor
  · intro resultTrue
    apply terminalCorrect.1
    exact Eq.trans run.resultExact.symm resultTrue
  · intro accepted
    exact Eq.trans run.resultExact (terminalCorrect.2 accepted)

/-- No certified execution can retain a failed closure-search run. -/
theorem CausalDecisionCertifiedRun.execution_found
    {input : Nat}
    (run : CausalDecisionCertifiedRun input) :
    run.execution.run.code? = some run.execution.code :=
  run.execution.codeExact

/-- The certified terminal scan is definitionally tied to the executed state. -/
theorem CausalDecisionCertifiedRun.terminal_from_execution
    {input : Nat}
    (run : CausalDecisionCertifiedRun input) :
    run.terminal.scan =
      scanExecutedTerminal
        run.execution.producedState.context.formula :=
  run.terminal.scanExact

/-- Erase proof-relevant phase data only after the certified run exists. -/
def CausalDecisionCertifiedRun.toObservable
    {input : Nat}
    (run : CausalDecisionCertifiedRun input) :
    CausalDecisionProcedureRun :=
  { result := run.result
    terminalProduced := true
    stats := run.stats }

/--
Observable projection of the complete certified pipeline.  This function can
no longer manufacture a result in a separate failure branch: it first obtains
the proof-relevant causal run and only then erases its internal witnesses.
-/
def executeCausalDecision
    (input : Nat) : CausalDecisionProcedureRun :=
  (executeCausalDecisionCertified input).toObservable

/-- The complete run always reaches the typed success branch. -/
theorem executeCausalDecision_success_branch
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery := by
  rcases causalDecision_discovery_found input with
    ⟨discovery, found, _selected, _attempts⟩
  exact ⟨discovery, found⟩

/-- The complete decision is caused by, and agrees with, its terminal readout. -/
theorem executeCausalDecision_correct
    (input : Nat) :
    (executeCausalDecision input).result = true <->
      CausalDecisionAccept input :=
  (executeCausalDecisionCertified input).result_correct

/-- A successful complete run certifies that an execution-indexed terminal exists. -/
theorem executeCausalDecision_terminalProduced
    (input : Nat) :
    (executeCausalDecision input).terminalProduced = true :=
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.extractClauseCandidateRun
#print axioms ConstitutiveSearch.SAT.extractCnfCandidateRun
#print axioms ConstitutiveSearch.SAT.extractClauseCandidateRun_candidates
#print axioms ConstitutiveSearch.SAT.extractCnfCandidateRun_candidates
#print axioms ConstitutiveSearch.SAT.extractClauseCandidateRun_candidatesEmitted
#print axioms ConstitutiveSearch.SAT.extractCnfCandidateRun_candidatesEmitted
#print axioms ConstitutiveSearch.SAT.runCandidateExtraction_candidatesEmitted
#print axioms ConstitutiveSearch.SAT.runCandidateExtraction
#print axioms ConstitutiveSearch.SAT.extractStructuralCandidates
#print axioms ConstitutiveSearch.SAT.tryEndogenousFlipCandidate
#print axioms ConstitutiveSearch.SAT.tryEndogenousFlipCandidate_none_of_formula_mismatch
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates
#print axioms ConstitutiveSearch.SAT.runEndogenousFlipDiscovery
#print axioms ConstitutiveSearch.SAT.DiscoverySchedule
#print axioms ConstitutiveSearch.SAT.DiscoveryScheduleProductionRun
#print axioms ConstitutiveSearch.SAT.runDiscoveryScheduleProduction
#print axioms ConstitutiveSearch.SAT.runDiscoveryScheduleProduction_atoms
#print axioms ConstitutiveSearch.SAT.runDiscoveryScheduleValidation_queries
#print axioms ConstitutiveSearch.SAT.runDiscoveryScheduleValidation_validatedAtoms
#print axioms ConstitutiveSearch.SAT.validateDiscoverySchedule
#print axioms ConstitutiveSearch.SAT.executeValidatedDiscoverySchedule
#print axioms ConstitutiveSearch.SAT.executeValidatedDiscoverySchedule_stats
#print axioms ConstitutiveSearch.SAT.ExecutedDiscoverySchedule.producedState
#print axioms ConstitutiveSearch.SAT.ExecutedDiscoverySchedule.producedState_eq_target
#print axioms ConstitutiveSearch.SAT.terminalFromExecution
#print axioms ConstitutiveSearch.SAT.ExecutedTerminalArtifact.scan_from_execution
#print axioms ConstitutiveSearch.SAT.decideExecutedTerminal
#print axioms ConstitutiveSearch.SAT.causalDecision_discovery_found
#print axioms ConstitutiveSearch.SAT.causalDecisionAfterDiscovery_terminal_formula
#print axioms ConstitutiveSearch.SAT.causalDecision_accept_iff_signal
#print axioms ConstitutiveSearch.SAT.causalDecisionYesInput_accepts
#print axioms ConstitutiveSearch.SAT.causalDecisionNoInput_rejects
#print axioms ConstitutiveSearch.SAT.causalDecisionYesInput_strict
#print axioms ConstitutiveSearch.SAT.causalDecisionNoInput_strict
#print axioms ConstitutiveSearch.SAT.causalDecisionAfterDiscovery_correct
#print axioms ConstitutiveSearch.SAT.executedTerminalArtifact_selected_formula
#print axioms ConstitutiveSearch.SAT.decideExecutedTerminal_selected_correct
#print axioms ConstitutiveSearch.SAT.causalDecisionStatsFromPhases
#print axioms ConstitutiveSearch.SAT.CausalDecisionCertifiedRun
#print axioms ConstitutiveSearch.SAT.executeCausalDecisionCertified
#print axioms ConstitutiveSearch.SAT.CausalDecisionCertifiedRun.discovery_from_actual_run
#print axioms ConstitutiveSearch.SAT.CausalDecisionCertifiedRun.result_correct
#print axioms ConstitutiveSearch.SAT.CausalDecisionCertifiedRun.execution_found
#print axioms ConstitutiveSearch.SAT.CausalDecisionCertifiedRun.terminal_from_execution
#print axioms ConstitutiveSearch.SAT.executeCausalDecision
#print axioms ConstitutiveSearch.SAT.executeCausalDecision_correct
#print axioms ConstitutiveSearch.SAT.executeCausalDecision_terminalProduced
/- AXIOM_AUDIT_END -/
