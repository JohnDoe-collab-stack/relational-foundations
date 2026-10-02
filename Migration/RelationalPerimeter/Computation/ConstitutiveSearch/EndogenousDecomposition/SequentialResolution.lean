import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.StoredLocalSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAssignment
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Causal succession of constituted operational stages

This module strengthens the per-stage run into a genuine succession.  The
assignment returned by the code executed at stage `depth` is retained as the
assignment entering stage `depth + 1`.  A future-freshness invariant proves
that the next discovered split can be entered without resetting or replacing
that assignment.

The relation is still discovered after constitution.  A `GeneratedStep` is
never converted into an operational relation or transport.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- Useful variable of the operational root produced at this stage. -/
def stageSelectedVar (depth : Nat) : Var :=
  growingDiscoverySplitVar (constructStage depth).searchIndex

/-- Anchor required by the accepted local continuation at this stage. -/
def stageAnchorVar (depth : Nat) : Var :=
  growingDiscoveryAnchorVar (constructStage depth).searchIndex

/-- Successive constituted stages expose successive useful variables. -/
theorem stageSelectedVar_succ (depth : Nat) :
    stageSelectedVar (depth + 1) = stageSelectedVar depth + 2 := by
  unfold stageSelectedVar growingDiscoverySplitVar
  rw [generateCanonicalStage_searchIndex_advances]

theorem stageAnchorVar_eq_selected_succ (depth : Nat) :
    stageAnchorVar depth = stageSelectedVar depth + 1 := by
  unfold stageAnchorVar stageSelectedVar growingDiscoveryAnchorVar
  unfold growingDiscoverySplitVar
  rfl

theorem stageSelectedVar_strict
    {earlier later : Nat}
    (before : earlier < later) :
    stageSelectedVar earlier < stageSelectedVar later := by
  unfold stageSelectedVar growingDiscoverySplitVar
  rw [constructStage_searchIndex, constructStage_searchIndex]
  change
    2 * constitutedOperationalIndex earlier + 2 <
      2 * constitutedOperationalIndex later + 2
  rw [constitutedOperationalIndex_exact, constitutedOperationalIndex_exact]
  rw [Nat.two_mul, Nat.two_mul]
  have shifted : earlier + 3 < later + 3 :=
    Nat.add_lt_add_right before 3
  exact
    Nat.add_lt_add_right
      (Nat.add_lt_add shifted shifted)
      2

/--
Extract the actual discovery returned by the executable run.  The impossible
branch is discharged by the previously proved total success of this concrete
family; no witness is selected from an existential proposition.
-/
def canonicalStageDiscovery (depth : Nat) :
    EndogenousFlipDiscovery (constructStage depth).operationalRoot :=
  match found : (stageRecordedDiscoveryRun depth).outcome.discovered? with
  | none => False.elim (stageRecordedDiscovery_ne_none depth found)
  | some discovery => discovery

theorem canonicalStageDiscovery_found (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.discovered? =
      some (canonicalStageDiscovery depth) := by
  unfold canonicalStageDiscovery
  split
  · rename_i failed
    exact False.elim ((stageRecordedDiscovery_ne_none depth) failed)
  · rename_i discovery found
    exact found

theorem canonicalStageDiscovery_var (depth : Nat) :
    (canonicalStageDiscovery depth).var = stageSelectedVar depth := by
  rcases stageRecordedDiscovery_found_after_exact_attempts depth with
    ⟨discovery, found, selected, _attempts⟩
  rw [canonicalStageDiscovery_found depth] at found
  have same : canonicalStageDiscovery depth = discovery :=
    Option.some.inj found
  rw [same]
  exact selected

/--
An operational assignment at a stage, together with the invariant needed for
all variables from the current discovered split onward.
-/
structure SequentialAssignment (depth : Nat) where
  assignment : Assignment
  reader : MeasuredAssignment assignment
  zeroTrue : assignment 0 = true
  futureSelectedFalse :
    ∀ futureDepth,
      depth + 1 ≤ futureDepth →
        assignment (stageSelectedVar futureDepth) = false
  futureAnchorTrue :
    ∀ futureDepth,
      depth + 1 ≤ futureDepth →
        assignment (stageAnchorVar futureDepth) = true

/-- Alternating executable bit used to construct the initial accepted state. -/
def alternatingAssignmentBit : Nat → Bool
  | 0 => true
  | 1 => true
  | value + 2 => !(alternatingAssignmentBit (value + 1))

/-- Executable initial reader; each recursive Boolean operation is charged. -/
def readAlternatingAssignment : (query : Var) → MeasuredValue (alternatingAssignmentBit query)
  | 0 => ⟨true, rfl, ⟨1, 0⟩⟩
  | 1 => ⟨true, rfl, ⟨1, 0⟩⟩
  | query + 2 =>
    let prior := readAlternatingAssignment (query + 1)
    ⟨!prior.value, congrArg Bool.not prior.valueExact, prior.work.visit⟩

theorem alternatingAssignmentBit_even_odd (value : Nat) :
    alternatingAssignmentBit (2 * value + 2) = false ∧
      alternatingAssignmentBit (2 * value + 3) = true := by
  induction value with
  | zero =>
      constructor <;> rfl
  | succ value inductionHypothesis =>
      constructor
      · change (!(alternatingAssignmentBit (2 * value + 3))) = false
        rw [inductionHypothesis.2]
        rfl
      · change (!(!(alternatingAssignmentBit (2 * value + 3)))) = true
        rw [inductionHypothesis.2]
        rfl

theorem alternatingAssignmentBit_even (value : Nat) :
    alternatingAssignmentBit (2 * value + 2) = false :=
  (alternatingAssignmentBit_even_odd value).1

theorem alternatingAssignmentBit_odd (value : Nat) :
    alternatingAssignmentBit (2 * value + 3) = true :=
  (alternatingAssignmentBit_even_odd value).2

/-- Initial assignment, constructed without knowledge of a later target. -/
def initialSequentialAssignment (depth : Nat) : SequentialAssignment depth :=
  { assignment := alternatingAssignmentBit
    reader := readAlternatingAssignment
    zeroTrue := rfl
    futureSelectedFalse := by
      intro futureDepth _above
      unfold stageSelectedVar growingDiscoverySplitVar
      rw [constructStage_searchIndex]
      exact alternatingAssignmentBit_even _
    futureAnchorTrue := by
      intro futureDepth _above
      unfold stageAnchorVar growingDiscoveryAnchorVar
      rw [constructStage_searchIndex]
      exact alternatingAssignmentBit_odd _ }

/-- Source continuation constructed from the current threaded assignment. -/
def sequentialSourceContinuation
    (depth : Nat)
    (input : SequentialAssignment depth) :
    GeneratedStructuralBranchContinuation
      (DiscoverySchedule.entry
        (scheduleFromDiscovery
          (canonicalStageDiscovery (depth + 1)))).source := by
  refine ⟨input.assignment, ?_⟩
  constructor
  · change input.assignment (canonicalStageDiscovery (depth + 1)).var = false
    rw [canonicalStageDiscovery_var]
    exact input.futureSelectedFalse _ (Nat.le_refl _)
  · exact True.intro

/-
Application of the exact code returned by local execution.  The output is
indexed by the target of the validated discovered schedule.
-/
/-- Result and counters are produced by the same structural recursion that
interprets and applies the returned transport code. -/
structure MeasuredTransportApplication
    {system : SearchSystem}
    {Generator : system.State → system.State → Type}
    (action : AcceptedRelationalAction system Generator)
    {source target : system.State}
    (code : TransportCode Generator source target)
    (input : system.Continuation source) where
  output : system.Continuation target
  evaluatedAtoms : Nat
  continuationApplications : Nat
  outputExact : output = (code.eval action).map input
  evaluatedAtomsExact : evaluatedAtoms = code.size
  continuationApplicationsExact : continuationApplications = code.size

/-- Instrumented interpreter/application. No counter is reconstructed from the
finished output: each atom emits one evaluation and one continuation mapping
when its recursive branch is executed. -/
def applyMeasuredTransportCode
    {system : SearchSystem}
    {Generator : system.State → system.State → Type}
    (action : AcceptedRelationalAction system Generator) :
    {source target : system.State} →
      (code : TransportCode Generator source target) →
      (input : system.Continuation source) →
      MeasuredTransportApplication action code input
  | _, _, .identity _, input =>
      { output := input
        evaluatedAtoms := 0
        continuationApplications := 0
        outputExact := rfl
        evaluatedAtomsExact := rfl
        continuationApplicationsExact := rfl }
  | _, _, .atom witness, input =>
      { output := (action.toTransport witness).map input
        evaluatedAtoms := 1
        continuationApplications := 1
        outputExact := rfl
        evaluatedAtomsExact := rfl
        continuationApplicationsExact := rfl }
  | _, _, .compose first second, input =>
      let firstRun := applyMeasuredTransportCode action first input
      let secondRun := applyMeasuredTransportCode action second firstRun.output
      { output := secondRun.output
        evaluatedAtoms := firstRun.evaluatedAtoms + secondRun.evaluatedAtoms
        continuationApplications :=
          firstRun.continuationApplications + secondRun.continuationApplications
        outputExact := by
          rw [secondRun.outputExact, firstRun.outputExact]
          rfl
        evaluatedAtomsExact := by
          rw [firstRun.evaluatedAtomsExact, secondRun.evaluatedAtomsExact]
          rfl
        continuationApplicationsExact := by
          rw [firstRun.continuationApplicationsExact,
            secondRun.continuationApplicationsExact]
          rfl }

structure AppliedDiscoveryExecution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source) where
  output : GeneratedStructuralBranchContinuation schedule.entry.target
  outputExact :
    output =
      (execution.code.eval
        (generatedStructuralFlipAtAction
          rootFormula
          schedule.entry.var)).map input
  evaluatedAtoms : Nat
  continuationApplications : Nat
  outputFromInstrumentedRun :
    output =
      (applyMeasuredTransportCode
        (generatedStructuralFlipAtAction rootFormula schedule.entry.var)
        execution.code input).output
  evaluatedAtomsFromInstrumentedRun :
    evaluatedAtoms =
      (applyMeasuredTransportCode
        (generatedStructuralFlipAtAction rootFormula schedule.entry.var)
        execution.code input).evaluatedAtoms
  continuationApplicationsFromInstrumentedRun :
    continuationApplications =
      (applyMeasuredTransportCode
        (generatedStructuralFlipAtAction rootFormula schedule.entry.var)
        execution.code input).continuationApplications
  evaluatedAtomsExact : evaluatedAtoms = execution.code.size
  continuationApplicationsExact : continuationApplications = execution.code.size

/-- Evaluate the code actually returned by the local execution run. -/
def applyDiscoveryExecution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source) :
    AppliedDiscoveryExecution execution input :=
  let applicationRun := applyMeasuredTransportCode
    (generatedStructuralFlipAtAction rootFormula schedule.entry.var)
    execution.code input
  { output :=
      (execution.code.eval
        (generatedStructuralFlipAtAction rootFormula schedule.entry.var)).map input
    outputExact := rfl
    evaluatedAtoms := applicationRun.evaluatedAtoms
    continuationApplications := applicationRun.continuationApplications
    outputFromInstrumentedRun := applicationRun.outputExact.symm
    evaluatedAtomsFromInstrumentedRun := rfl
    continuationApplicationsFromInstrumentedRun := rfl
    evaluatedAtomsExact := applicationRun.evaluatedAtomsExact
    continuationApplicationsExact := applicationRun.continuationApplicationsExact }

/-- The executable local run returns the exact atom carried by its schedule. -/
theorem constitutedLocalExecutionRun_code
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (_validated : ValidatedDiscoverySchedule schedule) :
    schedule.entry.executionRun.code? = some schedule.entry.code := by
  unfold ConstitutedLocalWitness.executionRun
  dsimp [searchTransportClosureBounded]
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos schedule.entry.relation.formulaExact,
    dif_pos schedule.entry.relation.decisionsExact
  ]
  rfl

/-- Any stored successful execution carries that exact returned atom. -/
theorem executedDiscoverySchedule_code
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) :
    execution.code = schedule.entry.code := by
  have codeExact := execution.codeExact
  have runExact := execution.runExact
  rw [runExact] at codeExact
  rw [constitutedLocalExecutionRun_code validated] at codeExact
  exact (Option.some.inj codeExact).symm

/-- The returned program, not a reconstructed target, transforms the input. -/
theorem applyDiscoveryExecution_assignment
    {root : Cnf} {state : GeneratedStructuralBranchContext root}
    {discovery : EndogenousFlipDiscovery state} {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated)
    (input : GeneratedStructuralBranchContinuation schedule.entry.source) :
    (applyDiscoveryExecution execution input).output.1 =
      Assignment.flipAt schedule.entry.var input.1 := by
  rw [(applyDiscoveryExecution execution input).outputExact]
  change ((execution.code.eval (generatedStructuralFlipAtAction root schedule.entry.var)).map input).1 = _
  rw [executedDiscoverySchedule_code]
  rfl

/-- The output assignment is the action of the returned code, not its target. -/
theorem AppliedDiscoveryExecution.assignment_from_returned_code
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    {input : GeneratedStructuralBranchContinuation schedule.entry.source}
    (application : AppliedDiscoveryExecution execution input) :
    application.output.1 =
      ((execution.code.eval
        (generatedStructuralFlipAtAction
          rootFormula
          schedule.entry.var)).map input).1 :=
  congrArg Subtype.val application.outputExact

/--
Acceptance is transported by the very code returned by execution and used to
produce `output`; it is not reconstructed from the target state.
-/
theorem AppliedDiscoveryExecution.preservesAccept
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    {input : GeneratedStructuralBranchContinuation schedule.entry.source}
    (application : AppliedDiscoveryExecution execution input)
    (accepted : GeneratedStructuralBranchAccept schedule.entry.source input) :
    GeneratedStructuralBranchAccept schedule.entry.target application.output := by
  rw [application.outputExact]
  exact
    (execution.code.eval
      (generatedStructuralFlipAtAction
        rootFormula
        schedule.entry.var)).preservesAccept input accepted

/-- A nonempty distinct decoy clause is satisfied by a true zero bit. -/
theorem distinctDecoyClause_satisfied_by_zero
    (assignment : Assignment)
    (zeroTrue : assignment 0 = true)
    (count : Nat) :
    Clause.eval assignment (distinctDecoyClause (Nat.succ count)) = true := by
  induction count with
  | zero =>
      rw [distinctDecoyClause, Clause.eval, Literal.eval, zeroTrue]
      rw [distinctDecoyClause, Clause.eval]
      rfl
  | succ count inductionHypothesis =>
      rw [distinctDecoyClause, Clause.eval, Literal.eval, inductionHypothesis]
      cases assignment (count + 1) <;> rfl

theorem symmetricPositiveClause_satisfied_by_anchor
    (assignment : Assignment)
    (selected anchor : Var)
    (anchorTrue : assignment anchor = true) :
    Clause.eval assignment (symmetricPositiveClause selected anchor) = true := by
  unfold symmetricPositiveClause
  rw [Clause.eval, Literal.eval, Clause.eval, Literal.eval, anchorTrue]
  cases assignment selected <;> rfl

theorem symmetricNegativeClause_satisfied_by_anchor
    (assignment : Assignment)
    (selected anchor : Var)
    (anchorTrue : assignment anchor = true) :
    Clause.eval assignment (symmetricNegativeClause selected anchor) = true := by
  unfold symmetricNegativeClause
  rw [Clause.eval, Literal.eval, Clause.eval, Literal.eval, anchorTrue]
  cases assignment selected <;> rfl

/-- The threaded assignment satisfies the complete root used by the next run. -/
theorem sequentialAssignment_satisfies_next_root
    (depth : Nat)
    (input : SequentialAssignment depth) :
    Satisfies
      input.assignment
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex) := by
  unfold distinctGrowingDiscoveryFormula symmetricBlockFamily
  apply Satisfies.cons
  · exact
      distinctDecoyClause_satisfied_by_zero
        input.assignment
        input.zeroTrue
        (constructStage (depth + 1)).searchIndex
  · apply Satisfies.cons
    · exact
        symmetricPositiveClause_satisfied_by_anchor
          input.assignment
          (stageSelectedVar (depth + 1))
          (stageAnchorVar (depth + 1))
          (input.futureAnchorTrue (depth + 1) (Nat.le_refl _))
    · apply Satisfies.cons
      · exact
          symmetricNegativeClause_satisfied_by_anchor
            input.assignment
            (stageSelectedVar (depth + 1))
            (stageAnchorVar (depth + 1))
            (input.futureAnchorTrue (depth + 1) (Nat.le_refl _))
      · exact Satisfies.nil

/-- The actual continuation supplied to execution is accepted at its source. -/
theorem sequentialSourceContinuation_accepted
    (depth : Nat)
    (input : SequentialAssignment depth) :
    GeneratedStructuralBranchAccept
      (DiscoverySchedule.entry
        (scheduleFromDiscovery
          (canonicalStageDiscovery (depth + 1)))).source
      (sequentialSourceContinuation depth input) := by
  change
    Satisfies input.assignment
      (branchResidual
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)
        (canonicalStageDiscovery (depth + 1)).var
        false)
  exact
    (branchWeakening
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)
      (canonicalStageDiscovery (depth + 1)).var
      false).preservesSatisfaction
        (sequentialAssignment_satisfies_next_root depth input)

/--
All typed phases of one causally ordered stage.  Each later field is indexed by
the concrete output stored in the preceding field.
-/
structure SequentialStageRun
    (depth : Nat)
    (input : SequentialAssignment depth) where
  generation : CanonicalStageGeneration depth
  discoveryRun : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot
  extractionExact : discoveryRun.extraction =
    (stageRecordedDiscoveryRun (depth + 1)).extraction
  discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot
  discoveryRunFound : discoveryRun.outcome.discovered? = some discovery
  discoveryExact :
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery
  discoveryWorkLeCanonical :
    (discoveryRun.outcome.comparisonWork.add
      discoveryRun.outcome.constructionWork).total ≤
    ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
      (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total
  storedSchedule : StoredLocalSchedule discovery
  storedScheduleExact : storedSchedule = discoveryRun.outcome.produceStoredSchedule discovery
    discoveryRunFound
  measuredValidation : MeasuredScheduleValidation storedSchedule
  measuredExecution : MeasuredScheduleExecution measuredValidation
  schedule : DiscoverySchedule discovery
  scheduleExact : schedule = scheduleFromDiscovery discovery
  validated : ValidatedDiscoverySchedule schedule
  validatedFromMeasured : HEq validated measuredValidation.validated
  execution : ExecutedDiscoverySchedule validated
  executionFromMeasured : HEq execution measuredExecution.execution
  sourceContinuation :
    GeneratedStructuralBranchContinuation schedule.entry.source
  sourceAssignmentExact : sourceContinuation.1 = input.assignment
  sourceAccepted :
    GeneratedStructuralBranchAccept schedule.entry.source sourceContinuation
  application : AppliedDiscoveryExecution execution sourceContinuation
  outputAccepted :
    GeneratedStructuralBranchAccept schedule.entry.target application.output
  next : SequentialAssignment (depth + 1)
  nextAssignmentExact : next.assignment = application.output.1
  nextReaderExact : HEq next.reader
    (readTransportedAssignment schedule.entry.var execution.code
      sourceContinuation
      (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
        input.reader sourceAssignmentExact.symm))
  nextReaderWorkExact : ∀ query,
    (next.reader query).work =
      (readTransportedAssignment schedule.entry.var execution.code
        sourceContinuation
        (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
          input.reader sourceAssignmentExact.symm) query).work

/-- The returned executable atom changes only the discovered current split. -/
theorem sequentialStage_next_from_input
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.next.assignment = Assignment.flipAt run.schedule.entry.var input.assignment := by
  rw [run.nextAssignmentExact, run.application.assignment_from_returned_code,
    executedDiscoverySchedule_code]
  change Assignment.flipAt run.schedule.entry.var run.sourceContinuation.1 = _
  rw [run.sourceAssignmentExact]

theorem sequentialStage_selected_exact
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.schedule.entry.var = stageSelectedVar (depth + 1) := by
  rw [run.scheduleExact]
  change run.discovery.var = _
  have same : run.discovery = canonicalStageDiscovery (depth + 1) :=
    Option.some.inj (Eq.trans run.discoveryExact.symm (canonicalStageDiscovery_found _))
  rw [same]
  exact canonicalStageDiscovery_var _

theorem returnedAssignment_preserves_other
    (depth : Nat)
    (input : SequentialAssignment depth)
    (query : Var)
    (different : query ≠ stageSelectedVar (depth + 1)) :
        (applyDiscoveryExecution
          (executeValidatedDiscoverySchedule
            (validateDiscoverySchedule
              (scheduleFromDiscovery
                (canonicalStageDiscovery (depth + 1)))))
          (sequentialSourceContinuation depth input)).output.1
            query = input.assignment query := by
  rw [applyDiscoveryExecution_assignment]
  rw [Assignment.flipAt_other]
  · rfl
  · change query ≠ (canonicalStageDiscovery (depth + 1)).var
    rw [canonicalStageDiscovery_var]
    exact different

/-- Future selected variables remain false after flipping the current split. -/
theorem returnedAssignment_futureSelectedFalse
    (depth : Nat)
    (input : SequentialAssignment depth) :
    ∀ futureDepth,
      (depth + 1) + 1 ≤ futureDepth →
        (applyDiscoveryExecution
          (executeValidatedDiscoverySchedule
            (validateDiscoverySchedule
              (scheduleFromDiscovery
                (canonicalStageDiscovery (depth + 1)))))
          (sequentialSourceContinuation depth input)).output.1
            (stageSelectedVar futureDepth) = false := by
  intro futureDepth above
  rw [returnedAssignment_preserves_other]
  · exact input.futureSelectedFalse futureDepth (Nat.le_trans (Nat.le_succ _) above)
  · exact
      Nat.ne_of_gt
        (stageSelectedVar_strict
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self (depth + 1)) above))

theorem returnedAssignment_zeroTrue
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (applyDiscoveryExecution
      (executeValidatedDiscoverySchedule
        (validateDiscoverySchedule
          (scheduleFromDiscovery
            (canonicalStageDiscovery (depth + 1)))))
      (sequentialSourceContinuation depth input)).output.1 0 = true := by
  rw [returnedAssignment_preserves_other]
  · exact input.zeroTrue
  · unfold stageSelectedVar growingDiscoverySplitVar
    rw [constructStage_searchIndex]
    intro impossible
    cases impossible

theorem returnedAssignment_futureAnchorTrue
    (depth : Nat)
    (input : SequentialAssignment depth) :
    ∀ futureDepth,
      (depth + 1) + 1 ≤ futureDepth →
        (applyDiscoveryExecution
          (executeValidatedDiscoverySchedule
            (validateDiscoverySchedule
              (scheduleFromDiscovery
                (canonicalStageDiscovery (depth + 1)))))
          (sequentialSourceContinuation depth input)).output.1
            (stageAnchorVar futureDepth) = true := by
  intro futureDepth above
  rw [returnedAssignment_preserves_other]
  · exact input.futureAnchorTrue futureDepth (Nat.le_trans (Nat.le_succ _) above)
  · have selectedLtAnchor :
        stageSelectedVar (depth + 1) < stageAnchorVar futureDepth := by
      have selectedLeFuture :
          stageSelectedVar (depth + 1) ≤ stageSelectedVar futureDepth :=
        Nat.le_of_lt
          (stageSelectedVar_strict
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self (depth + 1)) above))
      rw [stageAnchorVar_eq_selected_succ]
      exact Nat.lt_of_le_of_lt selectedLeFuture (Nat.lt_succ_self _)
    exact Nat.ne_of_gt selectedLtAnchor

/--
Build a stage from the witness returned by the recorded discovery run.  The
equality argument is operational provenance: it prevents a caller from
substituting another relation while retaining the same stage type.
-/
def executeSequentialStageFromActiveRecorded
    (depth : Nat)
    (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (extractionExact : recorded.extraction =
      (stageRecordedDiscoveryRun (depth + 1)).extraction)
    (discovery :
      EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found :
      recorded.outcome.discovered? = some discovery)
    (canonicalFound :
      (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery)
    (workLeCanonical :
      (recorded.outcome.comparisonWork.add recorded.outcome.constructionWork).total ≤
      ((stageRecordedDiscoveryRun (depth + 1)).outcome.comparisonWork.add
        (stageRecordedDiscoveryRun (depth + 1)).outcome.constructionWork).total) :
    SequentialStageRun depth input := by
  have same : discovery = canonicalStageDiscovery (depth + 1) := by
    exact
      Option.some.inj
        (Eq.trans canonicalFound.symm (canonicalStageDiscovery_found (depth + 1)))
  let schedule := scheduleFromDiscovery discovery
  let storedSchedule := recorded.outcome.produceStoredSchedule discovery found
  let measuredValidation := validateStoredSchedule storedSchedule
  let measuredExecution := executeStoredSchedule measuredValidation
  let validated := measuredValidation.validated
  let execution := measuredExecution.execution
  let source : GeneratedStructuralBranchContinuation schedule.entry.source :=
    ⟨input.assignment, by
      change StructuralDecisionsHold input.assignment
        (scheduleFromDiscovery discovery).entry.source.context.decisions
      rw [same]
      exact (sequentialSourceContinuation depth input).property⟩
  have sourceAccepted : GeneratedStructuralBranchAccept schedule.entry.source source := by
    cases same
    exact sequentialSourceContinuation_accepted depth input
  let application := applyDiscoveryExecution execution source
  have outputReference : application.output.1 =
      (applyDiscoveryExecution
        (executeValidatedDiscoverySchedule
          (validateDiscoverySchedule (scheduleFromDiscovery (canonicalStageDiscovery (depth + 1)))))
        (sequentialSourceContinuation depth input)).output.1 := by
    rw [applyDiscoveryExecution_assignment, applyDiscoveryExecution_assignment]
    change Assignment.flipAt discovery.var input.assignment = _
    rw [same]
    rfl
  let next : SequentialAssignment (depth + 1) :=
    { assignment := application.output.1
      reader := readTransportedAssignment schedule.entry.var execution.code source input.reader
      zeroTrue := by
        rw [outputReference]
        exact returnedAssignment_zeroTrue depth input
      futureSelectedFalse := by
        rw [outputReference]
        exact returnedAssignment_futureSelectedFalse depth input
      futureAnchorTrue := by
        rw [outputReference]
        exact returnedAssignment_futureAnchorTrue depth input }
  exact
    { generation := generation
      discoveryRun := recorded
      extractionExact := extractionExact
      discovery := discovery
      discoveryRunFound := found
      discoveryExact := canonicalFound
      discoveryWorkLeCanonical := workLeCanonical
      storedSchedule := storedSchedule
      storedScheduleExact := rfl
      measuredValidation := measuredValidation
      measuredExecution := measuredExecution
      schedule := schedule
      scheduleExact := rfl
      validated := validated
      validatedFromMeasured := HEq.rfl
      execution := execution
      executionFromMeasured := HEq.rfl
      sourceContinuation := source
      sourceAssignmentExact := rfl
      sourceAccepted := sourceAccepted
      application := application
      outputAccepted := application.preservesAccept sourceAccepted
      next := next
      nextAssignmentExact := rfl
      nextReaderExact := HEq.rfl
      nextReaderWorkExact := fun _ => rfl }

/-- Canonical compatibility wrapper retained for reference callers. -/
def executeSequentialStageFromRecorded
    (depth : Nat)
    (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (recordedExact : recorded = stageRecordedDiscoveryRun (depth + 1))
    (discovery :
      EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery) :
    SequentialStageRun depth input :=
  executeSequentialStageFromActiveRecorded depth input generation recorded
    (by rw [recordedExact]) discovery found (by rw [← recordedExact]; exact found)
    (by rw [recordedExact]; exact Nat.le_refl _)

/-- Canonical specialization of the same measured, data-consuming builder. -/
def executeSequentialStage (depth : Nat) (input : SequentialAssignment depth) :
    SequentialStageRun depth input :=
  executeSequentialStageFromRecorded depth input (generateCanonicalStage depth)
    (stageRecordedDiscoveryRun (depth + 1)) rfl
    (canonicalStageDiscovery (depth + 1)) (canonicalStageDiscovery_found (depth + 1))

/-- Reference specialization; the operational traversal supplies its stored run. -/
def executeSequentialStageFromDiscovered
    (depth : Nat) (input : SequentialAssignment depth)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? = some discovery) :
    SequentialStageRun depth input :=
  executeSequentialStageFromRecorded depth input (generateCanonicalStage depth)
    (stageRecordedDiscoveryRun (depth + 1)) rfl discovery found

/-- The next input is literally the assignment returned by code execution. -/
theorem executeSequentialStage_threads_output
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).next.assignment =
      (executeSequentialStage depth input).application.output.1 :=
  (executeSequentialStage depth input).nextAssignmentExact

/-- The bit made current by this stage is read from the transported output. -/
theorem executeSequentialStage_output_selected
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).application.output.1
        (stageSelectedVar (depth + 1)) = true := by
  let run := executeSequentialStage depth input
  have outputExact := run.application.assignment_from_returned_code
  rw [executedDiscoverySchedule_code run.execution] at outputExact
  change
    run.application.output.1 (stageSelectedVar (depth + 1)) = true
  rw [outputExact]
  dsimp [
    ConstitutedLocalWitness.code,
    TransportClosure.ofGenerator,
    TransportCode.ofGenerator,
    TransportCode.eval,
    generatedStructuralFlipAtAction,
    GeneratedStructuralFlipAtRelation.toAcceptingTransport,
    GeneratedStructuralFlipAtRelation.mapContinuation
  ]
  have selected :
      run.schedule.entry.var = stageSelectedVar (depth + 1) := by
    change
      (canonicalStageDiscovery (depth + 1)).var =
        stageSelectedVar (depth + 1)
    exact canonicalStageDiscovery_var (depth + 1)
  rw [selected]
  rw [Assignment.flipAt_selected]
  have sourceAssignment : run.sourceContinuation.1 = input.assignment := by
    rfl
  rw [sourceAssignment]
  rw [input.futureSelectedFalse _ (Nat.le_refl _)]
  rfl

/-- The selected output bit is a property of every positively built stage,
not only of the canonical wrapper used by the reference execution. -/
theorem SequentialStageRun.output_selected
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.application.output.1 run.schedule.entry.var = true := by
  rw [run.application.assignment_from_returned_code,
    executedDiscoverySchedule_code]
  dsimp [
    ConstitutedLocalWitness.code,
    TransportClosure.ofGenerator,
    TransportCode.ofGenerator,
    TransportCode.eval,
    generatedStructuralFlipAtAction,
    GeneratedStructuralFlipAtRelation.toAcceptingTransport,
    GeneratedStructuralFlipAtRelation.mapContinuation
  ]
  rw [Assignment.flipAt_selected, run.sourceAssignmentExact]
  rw [sequentialStage_selected_exact run]
  rw [input.futureSelectedFalse _ (Nat.le_refl _)]
  rfl

/-- Applying the returned atom changes no variable other than its discovered split. -/
theorem executeSequentialStage_preserves_other
    (depth : Nat)
    (input : SequentialAssignment depth)
    (query : Var)
    (different : query ≠ stageSelectedVar (depth + 1)) :
    (executeSequentialStage depth input).next.assignment query =
      input.assignment query := by
  let run := executeSequentialStage depth input
  have threaded := run.nextAssignmentExact
  have outputExact := run.application.assignment_from_returned_code
  have returned := executedDiscoverySchedule_code run.execution
  have selected :
      run.schedule.entry.var = stageSelectedVar (depth + 1) := by
    change
      (canonicalStageDiscovery (depth + 1)).var =
        stageSelectedVar (depth + 1)
    exact canonicalStageDiscovery_var (depth + 1)
  change run.next.assignment query = input.assignment query
  rw [threaded, outputExact, returned]
  dsimp [
    ConstitutedLocalWitness.code,
    TransportClosure.ofGenerator,
    TransportCode.ofGenerator,
    TransportCode.eval,
    generatedStructuralFlipAtAction,
    GeneratedStructuralFlipAtRelation.toAcceptingTransport,
    GeneratedStructuralFlipAtRelation.mapContinuation
  ]
  rw [selected]
  rw [Assignment.flipAt_other]
  · rfl
  · exact different

/-- Statistics projected only from the concrete runs stored in one stage. -/
structure SequentialStageStats where
  generateCalls : Nat
  generatedSteps : Nat
  provenanceUnits : Nat
  generationCertificates : Nat
  extractionClauseVisits : Nat
  extractionLiteralVisits : Nat
  extractedCandidates : Nat
  testedCandidates : Nat
  discoveryAttempts : Nat
  candidateConstructions : Nat
  variableComparisonUnits : Nat
  formulaComparisonLiteralVisits : Nat
  historyComparisonDecisionVisits : Nat
  relationQueries : Nat
  scheduleAtoms : Nat
  validatedAtoms : Nat
  validationPrimitiveQueries : Nat
  executionPrimitiveQueries : Nat
  compositionCandidates : Nat
  appliedCodeAtoms : Nat
  continuationApplications : Nat
  deriving DecidableEq, Repr

/-- No separately supplied cost: every non-structural field reads a run. -/
def SequentialStageRun.stats
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : SequentialStageStats :=
  { generateCalls := run.generation.generateCalls
    generatedSteps := run.generation.generatedSteps
    provenanceUnits := run.generation.provenanceUnits
    generationCertificates := run.generation.certificatesProduced
    extractionClauseVisits :=
      run.discoveryRun.extraction.stats.clauseVisits
    extractionLiteralVisits :=
      run.discoveryRun.extraction.stats.literalVisits
    extractedCandidates :=
      run.discoveryRun.extraction.stats.candidatesEmitted
    testedCandidates :=
      run.discoveryRun.outcome.testedCandidates.length
    discoveryAttempts :=
      run.discoveryRun.outcome.attempts
    candidateConstructions :=
      run.discoveryRun.outcome.candidateConstructions
    variableComparisonUnits :=
      run.discoveryRun.outcome.variableComparisonUnits
    formulaComparisonLiteralVisits :=
      run.discoveryRun.outcome.formulaComparisonLiteralVisits
    historyComparisonDecisionVisits :=
      run.discoveryRun.outcome.historyComparisonDecisionVisits
    relationQueries :=
      run.discoveryRun.outcome.relationQueries
    scheduleAtoms :=
      (runDiscoveryScheduleProduction run.discovery).atomsEmitted
    validatedAtoms := run.validated.run.validatedAtoms
    validationPrimitiveQueries := run.validated.run.primitiveQueries
    executionPrimitiveQueries := run.execution.run.stats.primitiveQueries
    compositionCandidates := run.execution.run.stats.compositionCandidates
    appliedCodeAtoms := run.application.evaluatedAtoms
    continuationApplications := run.application.continuationApplications }

/-- Legacy structural profile sum, not a sum of disjoint executed operations. -/
def SequentialStageStats.total (stats : SequentialStageStats) : Nat :=
  stats.generateCalls +
    stats.generatedSteps +
    stats.provenanceUnits +
    stats.generationCertificates +
    stats.extractionClauseVisits +
    stats.extractionLiteralVisits +
    stats.extractedCandidates +
    stats.testedCandidates +
    stats.discoveryAttempts +
    stats.candidateConstructions +
    stats.variableComparisonUnits +
    stats.formulaComparisonLiteralVisits +
    stats.historyComparisonDecisionVisits +
    stats.relationQueries +
    stats.scheduleAtoms +
    stats.validatedAtoms +
    stats.validationPrimitiveQueries +
    stats.executionPrimitiveQueries +
    stats.compositionCandidates +
    stats.appliedCodeAtoms +
    stats.continuationApplications

/-- Tested candidates and charged attempts are emitted by the same recursion. -/
theorem executeSequentialStage_testedCandidates
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.testedCandidates =
      (executeSequentialStage depth input).stats.discoveryAttempts := by
  exact stageRecordedDiscovery_tested_length (depth + 1)

theorem executeSequentialStage_generationStats
    (depth : Nat)
    (input : SequentialAssignment depth) :
    let stats := (executeSequentialStage depth input).stats
    stats.generateCalls = 1 ∧
      stats.generatedSteps = 1 ∧
      stats.provenanceUnits = 1 ∧
      stats.generationCertificates = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem executeSequentialStage_extractionStats
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.extractionClauseVisits = 3 ∧
      (executeSequentialStage depth input).stats.extractionLiteralVisits =
        2 * depth + 13 := by
  constructor
  · exact (stageRecordedExtractionStats_exact (depth + 1)).1
  · change
      (stageRecordedDiscoveryRun
        (depth + 1)).extraction.stats.literalVisits = 2 * depth + 13
    rw [
      (stageRecordedExtractionStats_exact (depth + 1)).2
    ]
    exact constitutedSearchIndex_next_add_five depth

theorem executeSequentialStage_extractedCandidates
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.extractedCandidates =
      2 * depth + 13 := by
  change
    (stageRecordedDiscoveryRun
      (depth + 1)).extraction.stats.candidatesEmitted = 2 * depth + 13
  change
    (runCandidateExtraction
      (constructStage (depth + 1)).operationalRoot).stats.candidatesEmitted =
        2 * depth + 13
  rw [runCandidateExtraction_candidatesEmitted]
  exact (executeSequentialStage_extractionStats depth input).2

theorem executeSequentialStage_attempts
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.discoveryAttempts =
      2 * depth + 10 := by
  change
    (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts =
      2 * depth + 10
  rw [
    stageRecordedDiscovery_attempts_exact
  ]
  exact constitutedSearchIndex_next_add_two depth

theorem executeSequentialStage_detailedDiscoveryStats
    (depth : Nat)
    (input : SequentialAssignment depth) :
    let stats := (executeSequentialStage depth input).stats
    stats.candidateConstructions = 2 * (2 * depth + 10) ∧
      stats.variableComparisonUnits =
        (2 * depth + 14) * (2 * depth + 10) ∧
      stats.formulaComparisonLiteralVisits =
        (2 * depth + 13) * (2 * depth + 10) ∧
      stats.historyComparisonDecisionVisits = 2 * depth + 10 ∧
      stats.relationQueries = 2 * depth + 10 := by
  have detailed := stageRecordedDiscovery_detailedWork_exact (depth + 1)
  dsimp only [SequentialStageRun.stats] at detailed ⊢
  simpa [
    executeSequentialStage,
    executeSequentialStageFromRecorded,
    executeSequentialStageFromActiveRecorded,
    constructStage,
    constitutedSearchIndex_linear,
    Nat.mul_add,
    Nat.add_assoc
  ] using detailed

/-- All local accounting facts are consequences of the stored executed runs. -/
theorem executeSequentialStage_localStats
    (depth : Nat)
    (input : SequentialAssignment depth) :
    And
      ((executeSequentialStage depth input).stats.scheduleAtoms = 1)
      (And
        ((executeSequentialStage depth input).stats.validationPrimitiveQueries = 1)
        (And
          ((executeSequentialStage depth input).stats.executionPrimitiveQueries = 1)
          (And
            ((executeSequentialStage depth input).stats.compositionCandidates = 0)
            ((executeSequentialStage depth input).stats.appliedCodeAtoms = 1)))) := by
  let run := executeSequentialStage depth input
  have validationQueries :=
    runDiscoveryScheduleValidation_queries run.schedule
  have storedValidationQueries :
      run.validated.run.primitiveQueries = 1 := by
    calc
      run.validated.run.primitiveQueries =
          (runDiscoveryScheduleValidation run.schedule).primitiveQueries :=
        congrArg
          (fun validationRun => validationRun.primitiveQueries)
          run.validated.runExact
      _ = 1 := validationQueries
  have executionStats :
      run.execution.run.stats.primitiveQueries = 1 ∧
        run.execution.run.stats.compositionCandidates = 0 := by
    rw [run.execution.runExact]
    exact run.schedule.entry.executionRun_stats
  have codeSize : run.execution.code.size = 1 := by
    rw [executedDiscoverySchedule_code run.execution]
    exact ConstitutedLocalWitness.code_size run.schedule.entry
  have evaluatedAtoms : run.application.evaluatedAtoms = 1 :=
    Eq.trans run.application.evaluatedAtomsExact codeSize
  dsimp only [SequentialStageRun.stats]
  change
    And
      ((runDiscoveryScheduleProduction run.discovery).atomsEmitted = 1)
      (And
        (run.validated.run.primitiveQueries = 1)
        (And
          (run.execution.run.stats.primitiveQueries = 1)
          (And
            (run.execution.run.stats.compositionCandidates = 0)
            (run.application.evaluatedAtoms = 1))))
  exact
    ⟨runDiscoveryScheduleProduction_atoms run.discovery,
      storedValidationQueries,
      executionStats.1,
      executionStats.2,
      evaluatedAtoms⟩

/-- Local scheduling, validation, execution and application counters depend on
the stored positive stage, not on how its candidate list was filtered. -/
theorem SequentialStageRun.localStats
    {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.stats.scheduleAtoms = 1 ∧
      run.stats.validationPrimitiveQueries = 1 ∧
      run.stats.executionPrimitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 ∧
      run.stats.appliedCodeAtoms = 1 := by
  have validationQueries := runDiscoveryScheduleValidation_queries run.schedule
  have storedValidationQueries : run.validated.run.primitiveQueries = 1 := by
    calc
      run.validated.run.primitiveQueries =
          (runDiscoveryScheduleValidation run.schedule).primitiveQueries :=
        congrArg (fun validationRun => validationRun.primitiveQueries)
          run.validated.runExact
      _ = 1 := validationQueries
  have executionStats :
      run.execution.run.stats.primitiveQueries = 1 ∧
        run.execution.run.stats.compositionCandidates = 0 := by
    rw [run.execution.runExact]
    exact run.schedule.entry.executionRun_stats
  have codeSize : run.execution.code.size = 1 := by
    rw [executedDiscoverySchedule_code run.execution]
    exact ConstitutedLocalWitness.code_size run.schedule.entry
  have evaluatedAtoms : run.application.evaluatedAtoms = 1 :=
    Eq.trans run.application.evaluatedAtomsExact codeSize
  exact
    ⟨runDiscoveryScheduleProduction_atoms run.discovery,
      storedValidationQueries, executionStats.1, executionStats.2, evaluatedAtoms⟩

theorem executeSequentialStage_continuationApplications
    (depth : Nat) (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.continuationApplications = 1 := by
  change (executeSequentialStage depth input).application.continuationApplications = 1
  rw [(executeSequentialStage depth input).application.continuationApplicationsExact]
  rw [executedDiscoverySchedule_code]
  exact ConstitutedLocalWitness.code_size _

theorem executeSequentialStage_validatedAtoms
    (depth : Nat) (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.validatedAtoms = 1 := by
  change (executeSequentialStage depth input).validated.run.validatedAtoms = 1
  rw [(executeSequentialStage depth input).validated.runExact]
  exact runDiscoveryScheduleValidation_validatedAtoms _

/-- Quadratic closed form of the legacy structural profile sum. -/
def sequentialStageSurfacePolynomial : CostPolynomial :=
  let attempts :=
    CostPolynomial.add
      (CostPolynomial.mul (CostPolynomial.constant 2) CostPolynomial.input)
      (CostPolynomial.constant 10)
  let literals :=
    CostPolynomial.add
      (CostPolynomial.mul (CostPolynomial.constant 2) CostPolynomial.input)
      (CostPolynomial.constant 13)
  let variableSurface :=
    CostPolynomial.add
      (CostPolynomial.mul (CostPolynomial.constant 2) CostPolynomial.input)
      (CostPolynomial.constant 14)
  let called := CostPolynomial.constant 1
  let generated := CostPolynomial.add called (CostPolynomial.constant 1)
  let provenance := CostPolynomial.add generated (CostPolynomial.constant 1)
  let certified := CostPolynomial.add provenance (CostPolynomial.constant 1)
  let extractedClauses :=
    CostPolynomial.add certified (CostPolynomial.constant 3)
  let extractedLiterals :=
    CostPolynomial.add
      extractedClauses
      (CostPolynomial.add
        (CostPolynomial.mul (CostPolynomial.constant 2) CostPolynomial.input)
        (CostPolynomial.constant 13))
  let extractedCandidates :=
    CostPolynomial.add extractedLiterals literals
  let tested :=
    CostPolynomial.add
      extractedCandidates
      attempts
  let attempted :=
    CostPolynomial.add
      tested
      attempts
  let constructed :=
    CostPolynomial.add attempted
      (CostPolynomial.mul (CostPolynomial.constant 2) attempts)
  let comparedVariables :=
    CostPolynomial.add constructed
      (CostPolynomial.mul variableSurface attempts)
  let comparedFormulas :=
    CostPolynomial.add comparedVariables
      (CostPolynomial.mul literals attempts)
  let comparedHistories := CostPolynomial.add comparedFormulas attempts
  let queriedRelations := CostPolynomial.add comparedHistories attempts
  let scheduled := CostPolynomial.add queriedRelations (CostPolynomial.constant 1)
  let validatedAtoms := CostPolynomial.add scheduled (CostPolynomial.constant 1)
  let validated := CostPolynomial.add validatedAtoms (CostPolynomial.constant 1)
  let executed := CostPolynomial.add validated (CostPolynomial.constant 1)
  let composed := CostPolynomial.add executed (CostPolynomial.constant 0)
  let applied := CostPolynomial.add composed (CostPolynomial.constant 1)
  CostPolynomial.add applied (CostPolynomial.constant 1)

/-- Exact legacy surface sum. This is not an end-to-end runtime theorem. -/
theorem executeSequentialStage_total
    (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeSequentialStage depth input).stats.total =
      sequentialStageSurfacePolynomial.eval depth := by
  have extraction := executeSequentialStage_extractionStats depth input
  have extractedCandidates := executeSequentialStage_extractedCandidates depth input
  have attempts := executeSequentialStage_attempts depth input
  have tested := executeSequentialStage_testedCandidates depth input
  have detailed := executeSequentialStage_detailedDiscoveryStats depth input
  have localStats := executeSequentialStage_localStats depth input
  have generation := executeSequentialStage_generationStats depth input
  have applications :
      (executeSequentialStage depth input).stats.continuationApplications = 1 :=
    executeSequentialStage_continuationApplications depth input
  have validatedAtoms := executeSequentialStage_validatedAtoms depth input
  unfold SequentialStageStats.total
  rw [
    extraction.1,
    extraction.2,
    extractedCandidates,
    generation.1,
    generation.2.1,
    generation.2.2.1,
    generation.2.2.2,
    tested,
    attempts,
    detailed.1,
    detailed.2.1,
    detailed.2.2.1,
    detailed.2.2.2.1,
    detailed.2.2.2.2,
    localStats.1,
    validatedAtoms,
    localStats.2.1,
    localStats.2.2.1,
    localStats.2.2.2.1,
    localStats.2.2.2.2,
    applications
  ]
  rfl

/-- Canonical single-stage work is input-indexed polynomially bounded exactly. -/
theorem initialSequentialStageCost_polynomial :
    InputPolynomiallyBounded
      (fun depth => depth)
      (fun depth =>
        (executeSequentialStage
          depth
          (initialSequentialAssignment depth)).stats.total) := by
  refine ⟨sequentialStageSurfacePolynomial, ?_⟩
  intro depth
  exact Nat.le_of_eq
    (executeSequentialStage_total
      depth
      (initialSequentialAssignment depth))

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.readAlternatingAssignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.MeasuredTransportApplication
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyMeasuredTransportCode
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyDiscoveryExecution_assignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.sequentialStage_next_from_input
#print axioms ConstitutiveSearch.EndogenousDecomposition.sequentialStage_selected_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStageFromRecorded
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageSelectedVar_strict
#print axioms ConstitutiveSearch.EndogenousDecomposition.canonicalStageDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyDiscoveryExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.AppliedDiscoveryExecution.preservesAccept
#print axioms ConstitutiveSearch.EndogenousDecomposition.sequentialAssignment_satisfies_next_root
#print axioms ConstitutiveSearch.EndogenousDecomposition.sequentialSourceContinuation_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.returnedAssignment_preserves_other
#print axioms ConstitutiveSearch.EndogenousDecomposition.returnedAssignment_futureSelectedFalse
#print axioms ConstitutiveSearch.EndogenousDecomposition.returnedAssignment_futureAnchorTrue
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStageFromDiscovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_threads_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_output_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_preserves_other
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_testedCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialStageRun.stats
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_generationStats
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_extractionStats
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_extractedCandidates
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_attempts
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_detailedDiscoveryStats
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_localStats
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_continuationApplications
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_validatedAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_total
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialSequentialStageCost_polynomial
/- AXIOM_AUDIT_END -/
