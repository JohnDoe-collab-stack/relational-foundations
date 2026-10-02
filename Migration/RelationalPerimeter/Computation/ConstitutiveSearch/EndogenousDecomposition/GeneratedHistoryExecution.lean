import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialHistory

/-!
# Generated history consumed by operational execution

Constitution is completed before discovery begins.  The first recursion below
produces a dependent history of genuine `CanonicalStageGeneration` witnesses.
The second recursion consumes that history.  Its head run stores the precise
generation witness read from the history, while its tail consumes the
assignment returned by the head execution.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

/-- A finite history made only of witnesses returned by the constitutive producer. -/
inductive CanonicalGeneratedHistory : Nat → Nat → Type 2 where
  | nil (startDepth : Nat) : CanonicalGeneratedHistory startDepth 0
  | step
      {startDepth count : Nat}
      (generation : CanonicalStageGeneration startDepth)
      (tail : CanonicalGeneratedHistory (startDepth + 1) count) :
      CanonicalGeneratedHistory startDepth (count + 1)

/-- Produce the complete constitutive history before any operational discovery. -/
def produceCanonicalGeneratedHistory :
    (startDepth count : Nat) → CanonicalGeneratedHistory startDepth count
  | startDepth, 0 => .nil startDepth
  | startDepth, count + 1 =>
      .step
        (generateCanonicalStage startDepth)
        (produceCanonicalGeneratedHistory (startDepth + 1) count)

/-- Thread every produced endpoint directly into the next producer call. -/
def produceThreadedGeneratedHistoryFrom (depth count : Nat)
    (source : StrongPerimetralTurning.PositiveConstitution
      StrongPerimetralTurning.Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    CanonicalGeneratedHistory depth count :=
  match count with
  | 0 => .nil depth
  | count + 1 =>
    let generated := generateCanonicalStageFromSource source sourceExact
    .step generated (produceThreadedGeneratedHistoryFrom (depth + 1) count
      generated.target generated.targetExact)

theorem produceThreadedGeneratedHistoryFrom_exact (depth count : Nat)
    (source : StrongPerimetralTurning.PositiveConstitution
      StrongPerimetralTurning.Example.examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    produceThreadedGeneratedHistoryFrom depth count source sourceExact =
      produceCanonicalGeneratedHistory depth count := by
  induction count generalizing depth source with
  | zero => rfl
  | succ count ih =>
    cases sourceExact
    change CanonicalGeneratedHistory.step (generateCanonicalStage depth)
      (produceThreadedGeneratedHistoryFrom (depth + 1) count
        (generateCanonicalStage depth).target (generateCanonicalStage depth).targetExact) =
      CanonicalGeneratedHistory.step (generateCanonicalStage depth)
        (produceCanonicalGeneratedHistory (depth + 1) count)
    exact congrArg (CanonicalGeneratedHistory.step (generateCanonicalStage depth))
      (ih (depth + 1) (generateCanonicalStage depth).target
        (generateCanonicalStage depth).targetExact)

def SequentialStageRun.withGeneration
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input)
    (generation : CanonicalStageGeneration depth) :
    SequentialStageRun depth input :=
  { generation := generation
    discoveryRun := run.discoveryRun
    extractionExact := run.extractionExact
    discovery := run.discovery
    discoveryRunFound := run.discoveryRunFound
    discoveryExact := run.discoveryExact
    discoveryWorkLeCanonical := run.discoveryWorkLeCanonical
    storedSchedule := run.storedSchedule
    storedScheduleExact := run.storedScheduleExact
    measuredValidation := run.measuredValidation
    measuredExecution := run.measuredExecution
    schedule := run.schedule
    scheduleExact := run.scheduleExact
    validated := run.validated
    validatedFromMeasured := run.validatedFromMeasured
    execution := run.execution
    executionFromMeasured := run.executionFromMeasured
    sourceContinuation := run.sourceContinuation
    sourceAssignmentExact := run.sourceAssignmentExact
    sourceAccepted := run.sourceAccepted
    application := run.application
    outputAccepted := run.outputAccepted
    next := run.next
    nextAssignmentExact := run.nextAssignmentExact
    nextReaderExact := run.nextReaderExact
    nextReaderWorkExact := run.nextReaderWorkExact }

/--
Reference equality for the direct builder, used only in proofs. The executable
builder retains its supplied generation, recorded search and discovery.
-/
theorem executeRecorded_eq_reference
    (depth : Nat) (input : SequentialAssignment depth)
    (generation : CanonicalStageGeneration depth)
    (recorded : RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot)
    (recordedExact : recorded = stageRecordedDiscoveryRun (depth + 1))
    (discovery : SAT.EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : recorded.outcome.discovered? = some discovery) :
    executeSequentialStageFromRecorded depth input generation recorded recordedExact discovery found =
      (executeSequentialStage depth input).withGeneration generation := by
  cases recordedExact
  have same : discovery = canonicalStageDiscovery (depth + 1) :=
    Option.some.inj (Eq.trans found.symm (canonicalStageDiscovery_found _))
  cases same
  rfl

def executeGeneratedHistory :
    {startDepth count : Nat} →
      CanonicalGeneratedHistory startDepth count →
      (input : SequentialAssignment startDepth) →
      SequentialHistory startDepth input count
  | _, _, .nil startDepth, input => .nil startDepth input
  | _, _, .step generation tail, input =>
      let head :=
        (executeSequentialStage _ input).withGeneration generation
      .step head (executeGeneratedHistory tail head.next)

/--
Failure-aware traversal result.  A failure records the constituted depth at
which discovery returned `none`; a success contains the causally threaded
history built from the discoveries returned by the executed runs.
-/
structure GeneratedHistoryTraversalResult
    (startDepth : Nat)
    (input : SequentialAssignment startDepth)
    (count : Nat) where
  execution? : Option (SequentialHistory startDepth input count)
  discoveryRuns : Nat
  successfulDiscoveries : Nat
  failureDepth? : Option Nat
  realizationWork : ComparisonWork

/-- Extract the history only from a traversal whose optional output succeeded. -/
def GeneratedHistoryTraversalResult.successfulHistory
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (traversal : GeneratedHistoryTraversalResult startDepth input count)
    (success : traversal.execution? ≠ none) :
    SequentialHistory startDepth input count :=
  match found : traversal.execution? with
  | none => False.elim (success found)
  | some history => history

theorem GeneratedHistoryTraversalResult.successfulHistory_exact
    {startDepth count : Nat}
    {input : SequentialAssignment startDepth}
    (traversal : GeneratedHistoryTraversalResult startDepth input count)
    (success : traversal.execution? ≠ none) :
    traversal.execution? = some (traversal.successfulHistory success) := by
  unfold GeneratedHistoryTraversalResult.successfulHistory
  split
  · rename_i failed
    exact False.elim (success failed)
  · rename_i history returned
    exact returned

/--
Traverse an already generated history while retaining the possibility of a
discovery failure.  No stage is constructed in the `none` branch.  In the
`some` branch the exact returned discovery is passed to
`executeSequentialStageFromRecorded` before validation and execution.
-/
def discoverGeneratedHistoryTransportPath :
    {startDepth count : Nat} →
      CanonicalGeneratedHistory startDepth count →
      (input : SequentialAssignment startDepth) →
      GeneratedHistoryTraversalResult startDepth input count
  | _, _, .nil startDepth, input =>
      { execution? := some (.nil startDepth input)
        discoveryRuns := 0
        successfulDiscoveries := 0
        failureDepth? := none
        realizationWork := .zero }
  | startDepth, _count + 1, .step generation tail, input =>
      let bundle := measuredGeneratedDiscovery generation
      let recorded := bundle.recorded
      match found :
          recorded.outcome.discovered? with
      | none =>
          { execution? := none
            discoveryRuns := 1
            successfulDiscoveries := 0
            failureDepth? := some (startDepth + 1)
            realizationWork := bundle.realizationWork }
      | some discovery =>
          let head :=
            executeSequentialStageFromRecorded startDepth input generation recorded
              (generatedRecordedDiscoveryRun_exact generation) discovery found
          let tailRun := discoverGeneratedHistoryTransportPath tail head.next
          match tailRun.execution? with
          | none =>
              { execution? := none
                discoveryRuns := tailRun.discoveryRuns + 1
                successfulDiscoveries :=
                  tailRun.successfulDiscoveries + 1
                failureDepth? := tailRun.failureDepth?
                realizationWork := bundle.realizationWork.add tailRun.realizationWork }
          | some tailExecution =>
              { execution? := some (.step head tailExecution)
                discoveryRuns := tailRun.discoveryRuns + 1
                successfulDiscoveries :=
                  tailRun.successfulDiscoveries + 1
                failureDepth? := none
                realizationWork := bundle.realizationWork.add tailRun.realizationWork }

/-- The concrete family closes every optional discovery without bypassing it. -/
theorem discoverGeneratedHistoryTransportPath_exact :
    {startDepth count : Nat} →
      (generated : CanonicalGeneratedHistory startDepth count) →
      (input : SequentialAssignment startDepth) →
      let traversal := discoverGeneratedHistoryTransportPath generated input
      traversal.execution? = some (executeGeneratedHistory generated input) ∧
        traversal.discoveryRuns = count ∧
        traversal.successfulDiscoveries = count ∧
        traversal.failureDepth? = none
  | _, _, .nil startDepth, input => by
      exact ⟨rfl, rfl, rfl, rfl⟩
  | startDepth, count + 1, .step generation tail, input => by
      rw [discoverGeneratedHistoryTransportPath]
      dsimp only
      split
      · rename_i failed
        rw [(measuredGeneratedDiscovery generation).recordedExact] at failed
        exact False.elim ((stageRecordedDiscovery_ne_none _) failed)
      · rename_i discovery found
        erw [executeRecorded_eq_reference]
        have tailExact := discoverGeneratedHistoryTransportPath_exact tail
          ((executeSequentialStage startDepth input).withGeneration generation).next
        dsimp only at tailExact ⊢
        rw [tailExact.1]
        exact ⟨rfl, congrArg (fun value => value + 1) tailExact.2.1,
          congrArg (fun value => value + 1) tailExact.2.2.1, rfl⟩

/-- Canonical production followed by consumption is the canonical execution. -/
theorem executeProducedHistory_exact
    (startDepth count : Nat)
    (input : SequentialAssignment startDepth) :
    executeGeneratedHistory
        (produceCanonicalGeneratedHistory startDepth count)
        input =
      executeSequentialHistory startDepth count input := by
  induction count generalizing startDepth input with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        SequentialHistory.step
            (executeSequentialStage startDepth input)
            (executeGeneratedHistory
              (produceCanonicalGeneratedHistory (startDepth + 1) count)
              (executeSequentialStage startDepth input).next) =
          SequentialHistory.step
            (executeSequentialStage startDepth input)
            (executeSequentialHistory
              (startDepth + 1)
              count
              (executeSequentialStage startDepth input).next)
      rw [inductionHypothesis]

/-- Number of producer witnesses stored in a generated history. -/
def CanonicalGeneratedHistory.stepCount :
    {startDepth count : Nat} → CanonicalGeneratedHistory startDepth count → Nat
  | _, _, .nil _ => 0
  | _, _, .step _ tail => tail.stepCount + 1

theorem producedHistory_stepCount
    (startDepth count : Nat) :
    (produceCanonicalGeneratedHistory startDepth count).stepCount = count := by
  induction count generalizing startDepth with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (produceCanonicalGeneratedHistory
          (startDepth + 1) count).stepCount + 1 = count + 1
      rw [inductionHypothesis]

/-- Every stage stored by the executor carries concrete source and output acceptance. -/
inductive AcceptedSequentialHistory :
    {startDepth count : Nat} →
      {input : SequentialAssignment startDepth} →
      SequentialHistory startDepth input count → Prop where
  | nil
      (startDepth : Nat)
      (input : SequentialAssignment startDepth) :
      AcceptedSequentialHistory (.nil startDepth input)
  | step
      {startDepth count : Nat}
      {input : SequentialAssignment startDepth}
      (head : SequentialStageRun startDepth input)
      (tail : SequentialHistory (startDepth + 1) head.next count)
      (tailAccepted : AcceptedSequentialHistory tail) :
      AcceptedSequentialHistory (.step head tail)

theorem executeGeneratedHistory_accepted :
    {startDepth count : Nat} →
      (generated : CanonicalGeneratedHistory startDepth count) →
      (input : SequentialAssignment startDepth) →
      AcceptedSequentialHistory (executeGeneratedHistory generated input)
  | _, _, .nil startDepth, input => .nil startDepth input
  | _, _, .step _generation tail, _input =>
      .step _ _ (executeGeneratedHistory_accepted tail _)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceThreadedGeneratedHistoryFrom
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceThreadedGeneratedHistoryFrom_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeRecorded_eq_reference
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceCanonicalGeneratedHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeGeneratedHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoverGeneratedHistoryTransportPath
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoverGeneratedHistoryTransportPath_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryTraversalResult.successfulHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryTraversalResult.successfulHistory_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeProducedHistory_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedHistory_stepCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeGeneratedHistory_accepted
/- AXIOM_AUDIT_END -/
