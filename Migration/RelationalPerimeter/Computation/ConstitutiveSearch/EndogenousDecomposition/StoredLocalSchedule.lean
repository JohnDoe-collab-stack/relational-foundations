import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.EndogenousDiscovery

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- A schedule containing the endpoint data retained by discovery. -/
structure StoredLocalSchedule {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) where
  entry : ConstitutedLocalWitness root
  entryExact : entry = (scheduleFromDiscovery discovery).entry

def RecordedDiscoveryOutcome.produceStoredSchedule {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (outcome : RecordedDiscoveryOutcome state)
    (discovery : EndogenousFlipDiscovery state)
    (found : outcome.discovered? = some discovery) : StoredLocalSchedule discovery :=
  match returned : outcome.produced? with
  | none => False.elim (by
    unfold RecordedDiscoveryOutcome.discovered? at found
    rw [returned] at found
    cases found)
  | some produced =>
    have same : (⟨produced.1, produced.2.discovery⟩ : EndogenousFlipDiscovery state) = discovery := by
      unfold RecordedDiscoveryOutcome.discovered? at found
      rw [returned] at found
      exact Option.some.inj found
    { entry := produced.2.entry
      entryExact := by rw [← same]; exact produced.2.entry_exact }

def validationFromMeasuredSearch {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) : SearchableCodeValidationRun :=
  match search.result with
  | none => ⟨false, 1, 1⟩
  | some _ => ⟨true, 1, 1⟩

structure MeasuredScheduleValidation {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) where
  search : MeasuredRelationRun stored.entry.var stored.entry.source stored.entry.target
  searchExact : search = searchMeasuredRelation stored.entry.var stored.entry.source stored.entry.target

def validateStoredSchedule {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    (stored : StoredLocalSchedule discovery) : MeasuredScheduleValidation stored :=
  ⟨searchMeasuredRelation stored.entry.var stored.entry.source stored.entry.target, rfl⟩

def MeasuredScheduleValidation.validated {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    ValidatedDiscoverySchedule (scheduleFromDiscovery discovery) :=
  let run := validationFromMeasuredSearch stored.entry validation.search
  have exactRun : run = runDiscoveryScheduleValidation (scheduleFromDiscovery discovery) := by
    unfold run
    rw [validation.searchExact]
    cases stored with
    | mk entry entryExact =>
      cases entryExact
      unfold validationFromMeasuredSearch
      rw [searchMeasuredRelation_exact]
      unfold runDiscoveryScheduleValidation
      cases (generatedStructuralFlipAtSearch root
        (scheduleFromDiscovery discovery).entry.var).find
          (scheduleFromDiscovery discovery).entry.source
          (scheduleFromDiscovery discovery).entry.target <;> rfl
  { run := run
    runExact := exactRun
    success := by
      rw [exactRun]
      exact (validateDiscoverySchedule (scheduleFromDiscovery discovery)).success }

theorem validatedDiscoverySchedule_unique {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (left right : ValidatedDiscoverySchedule schedule) : left = right := by
  cases left with
  | mk left leftExact leftSuccess =>
    cases right with
    | mk right rightExact rightSuccess =>
      cases leftExact
      cases rightExact
      rfl

theorem MeasuredScheduleValidation.validated_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    validation.validated = validateDiscoverySchedule (scheduleFromDiscovery discovery) :=
  validatedDiscoverySchedule_unique _ _

def executionFromMeasuredSearch {root : Cnf} (entry : ConstitutedLocalWitness root)
    (search : MeasuredRelationRun entry.var entry.source entry.target) :
    ClosureSearchRun (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target :=
  match search.result with
  | none => ⟨none, ⟨1, 0⟩⟩
  | some relation => ⟨some (TransportClosure.ofGenerator relation), ⟨1, 0⟩⟩

theorem executionFromMeasuredSearch_exact {root : Cnf} (entry : ConstitutedLocalWitness root) :
    executionFromMeasuredSearch entry (searchMeasuredRelation entry.var entry.source entry.target) =
      entry.executionRun := by
  unfold executionFromMeasuredSearch
  rw [searchMeasuredRelation_exact]
  unfold ConstitutedLocalWitness.executionRun
  rw [searchTransportClosureBounded]
  cases (generatedStructuralFlipAtSearch root entry.var).find entry.source entry.target <;> rfl

structure MeasuredScheduleExecution {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) where
  search : MeasuredRelationRun stored.entry.var stored.entry.source stored.entry.target
  searchExact : search = searchMeasuredRelation stored.entry.var stored.entry.source stored.entry.target

def executeStoredSchedule {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} (validation : MeasuredScheduleValidation stored) :
    MeasuredScheduleExecution validation :=
  ⟨searchMeasuredRelation stored.entry.var stored.entry.source stored.entry.target, rfl⟩

def MeasuredScheduleExecution.execution {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} {validation : MeasuredScheduleValidation stored}
    (execution : MeasuredScheduleExecution validation) : ExecutedDiscoverySchedule validation.validated :=
  let run := executionFromMeasuredSearch stored.entry execution.search
  let indexedRun := Eq.rec
    (motive := fun entry _ => ClosureSearchRun
      (GeneratedStructuralFlipAtRelation entry.var) entry.source entry.target)
    run stored.entryExact
  have exactRun : indexedRun = (scheduleFromDiscovery discovery).entry.executionRun := by
    cases stored with
    | mk entry entryExact =>
      cases entryExact
      change executionFromMeasuredSearch _ execution.search = _
      rw [execution.searchExact]
      exact executionFromMeasuredSearch_exact _
  match found : indexedRun.code? with
  | none => False.elim (by
    have failed : (scheduleFromDiscovery discovery).entry.executionRun.code? = none := by
      rw [← exactRun]
      exact found
    exact (scheduleFromDiscovery discovery).entry.executionRun_found failed)
  | some code =>
    { run := indexedRun
      runExact := exactRun
      code := code
      codeExact := found
      producedState := stored.entry.target
      producedStateExact := congrArg ConstitutedLocalWitness.target stored.entryExact }

theorem executedDiscoverySchedule_unique {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery} {validation : ValidatedDiscoverySchedule schedule}
    (left right : ExecutedDiscoverySchedule validation) : left = right := by
  cases left with
  | mk leftRun leftRunExact leftCode leftFound leftState leftStateExact =>
    cases right with
    | mk rightRun rightRunExact rightCode rightFound rightState rightStateExact =>
      cases leftRunExact
      cases rightRunExact
      have same : leftCode = rightCode := Option.some.inj (Eq.trans leftFound.symm rightFound)
      cases same
      cases leftStateExact
      cases rightStateExact
      rfl

theorem MeasuredScheduleExecution.execution_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {discovery : EndogenousFlipDiscovery state}
    {stored : StoredLocalSchedule discovery} {validation : MeasuredScheduleValidation stored}
    (execution : MeasuredScheduleExecution validation) :
    execution.execution = executeValidatedDiscoverySchedule validation.validated :=
  executedDiscoverySchedule_unique _ _

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RecordedDiscoveryOutcome.produceStoredSchedule
#print axioms ConstitutiveSearch.EndogenousDecomposition.validateStoredSchedule
#print axioms ConstitutiveSearch.EndogenousDecomposition.MeasuredScheduleValidation.validated
#print axioms ConstitutiveSearch.EndogenousDecomposition.MeasuredScheduleValidation.validated_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executionFromMeasuredSearch_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeStoredSchedule
#print axioms ConstitutiveSearch.EndogenousDecomposition.MeasuredScheduleExecution.execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.MeasuredScheduleExecution.execution_exact
/- AXIOM_AUDIT_END -/
