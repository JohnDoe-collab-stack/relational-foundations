import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialHistory
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.OperationalProjection

/-!
The separator is built from a stage's retained discovered endpoints and its
incoming continuation. Two fresh provenance extensions are generated before
projecting them. Their formula projections coincide; the common ungated engine
accepts the compatible extension and rejects the other. No second input or
independently initialized assignment is used.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

theorem residual_preserves_avoids {marker : Var} {formula : Cnf}
    (avoids : Cnf.AvoidsVar marker formula) (selected : Var) (value : Bool) :
    Cnf.AvoidsVar marker (branchResidual formula selected value) := by
  induction formula with
  | nil => exact True.intro
  | cons clause rest ih =>
    cases hit : Clause.containsLiteral (Literal.forValue selected value) clause with
    | true =>
      rw [branchResidual_cons_hit clause rest selected value hit]
      exact ih avoids.2
    | false =>
      rw [branchResidual_cons_miss clause rest selected value hit]
      exact ⟨avoids.1, ih avoids.2⟩

theorem retained_var_exact {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.storedSchedule.entry.var = stageSelectedVar (depth + 1) := by
  rw [run.storedSchedule.entryExact]
  have selected := sequentialStage_selected_exact run
  rw [run.scheduleExact] at selected
  exact selected

theorem retained_decisions_exact {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.storedSchedule.entry.source.context.decisions = [⟨run.storedSchedule.entry.var, false⟩] ∧
      run.storedSchedule.entry.target.context.decisions = [⟨run.storedSchedule.entry.var, true⟩] := by
  rw [run.storedSchedule.entryExact]
  exact ⟨rfl, rfl⟩

theorem growing_root_avoids_above (index marker : Nat)
    (above : growingDiscoveryAnchorVar index < marker) :
    Cnf.AvoidsVar marker (distinctGrowingDiscoveryFormula index) := by
  have splitBefore : growingDiscoverySplitVar index < growingDiscoveryAnchorVar index :=
    Nat.lt_succ_self _
  have decoysBefore : index + 1 ≤ marker :=
    Nat.le_trans (Nat.le_succ (index + 1)) (Nat.le_of_lt (Nat.lt_trans splitBefore above))
  exact ⟨distinctDecoyClause_avoids_above _ _ decoysBefore,
    ⟨Nat.ne_of_lt (Nat.lt_trans splitBefore above), Nat.ne_of_lt above, True.intro⟩,
    ⟨Nat.ne_of_lt (Nat.lt_trans splitBefore above), Nat.ne_of_lt above, True.intro⟩,
    True.intro⟩

theorem retained_formulas_avoid_future {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 1 < offset) :
    Cnf.AvoidsVar (run.storedSchedule.entry.var + offset) run.storedSchedule.entry.source.context.formula ∧
      Cnf.AvoidsVar (run.storedSchedule.entry.var + offset) run.storedSchedule.entry.target.context.formula := by
  rw [run.storedSchedule.entryExact]
  have selected : run.discovery.var = stageSelectedVar (depth + 1) := by
    have exactVar := retained_var_exact run
    rw [run.storedSchedule.entryExact] at exactVar
    exact exactVar
  have avoided : Cnf.AvoidsVar (run.discovery.var + offset)
      (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex) := by
    apply growing_root_avoids_above
    rw [selected]
    exact Nat.add_lt_add_left positive _
  exact ⟨residual_preserves_avoids avoided _ false,
    residual_preserves_avoids avoided _ true⟩

theorem retained_source_fresh {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 0 < offset) :
    StructuralDecisionsAvoid (run.storedSchedule.entry.var + offset)
      run.storedSchedule.entry.source.context.decisions := by
  rw [(retained_decisions_exact run).1]
  exact ⟨Nat.ne_of_lt (Nat.lt_add_of_pos_right positive), True.intro⟩

theorem retained_target_fresh {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 0 < offset) :
    StructuralDecisionsAvoid (run.storedSchedule.entry.var + offset)
      run.storedSchedule.entry.target.context.decisions := by
  rw [(retained_decisions_exact run).2]
  exact ⟨Nat.ne_of_lt (Nat.lt_add_of_pos_right positive), True.intro⟩

def integratedMarkedSource {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :=
  run.storedSchedule.entry.source.child (run.storedSchedule.entry.var + 2) false
    (retained_source_fresh run 2 (by decide))

def integratedMarkedTarget {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 0 < offset) :=
  run.storedSchedule.entry.target.child (run.storedSchedule.entry.var + offset) false
    (retained_target_fresh run offset positive)

theorem integrated_marked_formula {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (offset : Nat) (positive : 1 < offset) :
    (integratedMarkedTarget run offset (Nat.lt_trans (by decide) positive)).context.formula =
      run.storedSchedule.entry.target.context.formula :=
  Cnf.branchResidual_eq_self (retained_formulas_avoid_future run offset positive).2 false

/-- Provenance differs before any formula projection is compared. -/
theorem integrated_marked_constitutions_distinct {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedMarkedTarget run 2 (by decide)).context.decisions ≠
      (integratedMarkedTarget run 4 (by decide)).context.decisions := by
  intro same
  have heads := congrArg (fun decisions => decisions.head?) same
  have marker := congrArg StructuralBranchDecision.var (Option.some.inj heads)
  exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 2 < 4) _)) marker

theorem integrated_marked_projection_equal {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedMarkedTarget run 2 (by decide)).context.formula =
      (integratedMarkedTarget run 4 (by decide)).context.formula :=
  Eq.trans (integrated_marked_formula run 2 (by decide))
    (integrated_marked_formula run 4 (by decide)).symm

def integratedMarkedRelation {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    GeneratedStructuralFlipAtRelation run.storedSchedule.entry.var
      (integratedMarkedSource run) (integratedMarkedTarget run 2 (by decide)) where
  formulaExact := by
    change branchResidual _ _ false = Cnf.flipAt _ (branchResidual _ _ false)
    rw [Cnf.branchResidual_eq_self (retained_formulas_avoid_future run 2 (by decide)).1,
      Cnf.branchResidual_eq_self (retained_formulas_avoid_future run 2 (by decide)).2]
    exact run.storedSchedule.entry.relation.formulaExact
  decisionsExact := by
    change (⟨_, false⟩ :: run.storedSchedule.entry.target.context.decisions) =
      flipStructuralDecisionsAt _ (⟨_, false⟩ :: run.storedSchedule.entry.source.context.decisions)
    rw [flipStructuralDecisionsAt, StructuralBranchDecision.flipAt,
      if_neg (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 2))),
      run.storedSchedule.entry.relation.decisionsExact]

theorem integrated_marked_incompatible {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedMarkedTarget run 4 (by decide)).context.decisions ≠
      flipStructuralDecisionsAt run.storedSchedule.entry.var
        (integratedMarkedSource run).context.decisions := by
  intro same
  exact integrated_marked_constitutions_distinct run
    (Eq.trans (integratedMarkedRelation run).decisionsExact same.symm)

/-- The new source keeps the incoming assignment of the actual executed stage. -/
abbrev integratedMarkedContinuation {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    GeneratedStructuralBranchContinuation (integratedMarkedSource run) := by
  refine ⟨input.assignment, ?_⟩
  change input.assignment (run.storedSchedule.entry.var + 2) = false ∧
    StructuralDecisionsHold input.assignment run.storedSchedule.entry.source.context.decisions
  rw [(retained_decisions_exact run).1, retained_var_exact]
  refine ⟨?_, input.futureSelectedFalse _ (Nat.le_refl _), True.intro⟩
  rw [← stageSelectedVar_succ]
  exact input.futureSelectedFalse _ (Nat.le_succ _)

structure MeasuredProjectionOutcome where
  terminalBit : Option Bool
  codeAtoms : Nat
  queryWork : ComparisonWork
  readWork : ComparisonWork

/-- Both organizations use this finder and this interpreter without a provenance gate. -/
def runMeasuredProjection {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1) : MeasuredProjectionOutcome :=
  let queried := searchMeasuredRelation selected source target
  match queried.result with
  | none => ⟨none, 0, queried.work, .zero⟩
  | some relation =>
    let code := TransportCode.ofGenerator relation
    let read := readTransportedAssignment selected code continuation reader selected
    ⟨some read.value, code.size, queried.work, read.work⟩

theorem runMeasuredProjection_found {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1)
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (found : (searchMeasuredRelation selected source target).result = some relation) :
    (runMeasuredProjection selected source target continuation reader).terminalBit =
      some (!(continuation.1 selected)) := by
  unfold runMeasuredProjection
  dsimp only
  rw [found]
  exact congrArg some
    (Eq.trans (readTransportedAssignment selected (TransportCode.ofGenerator relation)
      continuation reader selected).valueExact
      (Assignment.flipAt_selected selected continuation.1))

theorem integrated_positive_found {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (searchMeasuredRelation run.storedSchedule.entry.var
      (integratedMarkedSource run) (integratedMarkedTarget run 2 (by decide))).result =
        some (integratedMarkedRelation run) := by
  rw [searchMeasuredRelation_exact]
  dsimp only [generatedStructuralFlipAtSearch]
  rw [dif_pos (integratedMarkedRelation run).formulaExact,
    dif_pos (integratedMarkedRelation run).decisionsExact]

theorem integrated_negative_missed {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (searchMeasuredRelation run.storedSchedule.entry.var
      (integratedMarkedSource run) (integratedMarkedTarget run 4 (by decide))).result = none := by
  rw [searchMeasuredRelation_exact]
  dsimp only [generatedStructuralFlipAtSearch]
  split
  · rw [dif_neg (integrated_marked_incompatible run)]
  · rfl

def integratedOrganizationObservation {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (organization : ProjectionOrganization) :
    MeasuredProjectionOutcome :=
  let target := match organization with
    | .compatible => integratedMarkedTarget run 2 (by decide)
    | .incompatible => integratedMarkedTarget run 4 (by decide)
  runMeasuredProjection run.storedSchedule.entry.var (integratedMarkedSource run) target
    (integratedMarkedContinuation run) input.reader

theorem integrated_positive_result {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedOrganizationObservation run .compatible).terminalBit = some true := by
  change (runMeasuredProjection _ _ _ _ _).terminalBit = _
  dsimp only
  rw [runMeasuredProjection_found _ _ _ _ _ _ (integrated_positive_found run)]
  change some (!(input.assignment run.storedSchedule.entry.var)) = _
  rw [retained_var_exact, input.futureSelectedFalse _ (Nat.le_refl _)]
  rfl

theorem integrated_negative_result {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedOrganizationObservation run .incompatible).terminalBit = none := by
  change (runMeasuredProjection _ _ _ _ _).terminalBit = _
  unfold runMeasuredProjection
  dsimp only
  rw [integrated_negative_missed]

theorem integrated_positive_codeAtoms {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedOrganizationObservation run .compatible).codeAtoms = 1 := by
  change (runMeasuredProjection _ _ _ _ _).codeAtoms = 1
  unfold runMeasuredProjection
  dsimp only
  rw [integrated_positive_found]
  rfl

theorem integrated_negative_codeAtoms {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedOrganizationObservation run .incompatible).codeAtoms = 0 := by
  change (runMeasuredProjection _ _ _ _ _).codeAtoms = 0
  unfold runMeasuredProjection
  dsimp only
  rw [integrated_negative_missed]

/-- Executable reference semantics of the §3.1 primitives: search the exact
generated relation, turn the witness into finite code, apply that code, and
read the returned continuation. This is independent of all measured helpers. -/
def runSection31ReferenceProjection {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root)
    (continuation : GeneratedStructuralBranchContinuation source) : Option Bool × Nat :=
  match (generatedStructuralFlipAtSearch root selected).find source target with
  | none => (none, 0)
  | some relation =>
    let code := TransportCode.ofGenerator relation
    let returned := (code.eval (generatedStructuralFlipAtAction root selected)).map continuation
    (some (returned.1 selected), code.size)

/-- The measured implementation refines the unmeasured §3.1 semantics for
every source, target and continuation, not only for the concrete benchmark. -/
theorem runMeasuredProjection_refines_section31 {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1) :
    ((runMeasuredProjection selected source target continuation reader).terminalBit,
      (runMeasuredProjection selected source target continuation reader).codeAtoms) =
      runSection31ReferenceProjection selected source target continuation := by
  unfold runMeasuredProjection runSection31ReferenceProjection
  generalize measuredExact : searchMeasuredRelation selected source target = measured
  have resultExact := searchMeasuredRelation_exact selected source target
  rw [measuredExact] at resultExact
  dsimp only
  rw [resultExact]
  generalize found :
    (generatedStructuralFlipAtSearch root selected).find source target = relation?
  cases relation? with
  | none => rfl
  | some relation =>
      dsimp only
      rw [(readTransportedAssignment selected (TransportCode.ofGenerator relation)
        continuation reader selected).valueExact]

/-- Formal justification for replacing the historical §3.1 instrumentation:
the integrated experiment uses an implementation that refines its complete
search/apply/read semantics, while additionally emitting measured work. -/
structure Section31PrimitiveRaccord {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : Prop where
  positiveAgreement :
    ((integratedOrganizationObservation run .compatible).terminalBit,
      (integratedOrganizationObservation run .compatible).codeAtoms) =
    runSection31ReferenceProjection run.storedSchedule.entry.var
      (integratedMarkedSource run) (integratedMarkedTarget run 2 (by decide))
      (integratedMarkedContinuation run)
  negativeAgreement :
    ((integratedOrganizationObservation run .incompatible).terminalBit,
      (integratedOrganizationObservation run .incompatible).codeAtoms) =
    runSection31ReferenceProjection run.storedSchedule.entry.var
      (integratedMarkedSource run) (integratedMarkedTarget run 4 (by decide))
      (integratedMarkedContinuation run)

theorem integrated_section31_primitiveRaccord {depth : Nat}
    {input : SequentialAssignment depth} (run : SequentialStageRun depth input) :
    Section31PrimitiveRaccord run := by
  exact ⟨runMeasuredProjection_refines_section31 _ _ _ _ _,
    runMeasuredProjection_refines_section31 _ _ _ _ _⟩

/-- The successful marked run reads the bit produced by the main stage's action. -/
theorem integrated_positive_agrees_with_main {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (integratedOrganizationObservation run .compatible).terminalBit =
      some (run.application.output.1 run.schedule.entry.var) := by
  rw [integrated_positive_result]
  have applied := sequentialStage_next_from_input run
  rw [run.nextAssignmentExact] at applied
  rw [applied, Assignment.flipAt_selected, sequentialStage_selected_exact,
    input.futureSelectedFalse _ (Nat.le_refl _)]
  rfl

def runMeasuredProjectionFromData {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (sourceData : MeasuredValue source) (targetData : MeasuredValue target)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1) : MeasuredProjectionOutcome :=
  let incoming : Sigma fun continuation : GeneratedStructuralBranchContinuation source =>
      MeasuredAssignment continuation.1 := ⟨continuation, reader⟩
  let indexed := Eq.rec (motive := fun state _ =>
    Sigma fun continuation : GeneratedStructuralBranchContinuation state =>
      MeasuredAssignment continuation.1) incoming sourceData.valueExact.symm
  runMeasuredProjection selected sourceData.value targetData.value indexed.1 indexed.2

theorem runMeasuredProjectionFromData_exact {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (sourceData : MeasuredValue source) (targetData : MeasuredValue target)
    (continuation : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment continuation.1) :
    runMeasuredProjectionFromData selected sourceData targetData continuation reader =
      runMeasuredProjection selected source target continuation reader := by
  cases sourceData with
  | mk source exactSource sourceWork =>
    cases exactSource
    cases targetData with
    | mk target exactTarget targetWork => cases exactTarget; rfl

structure IntegratedProjectionExperiment {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) where
  source : MeasuredValue (integratedMarkedSource run)
  positiveTarget : MeasuredValue (integratedMarkedTarget run 2 (by decide))
  negativeTarget : MeasuredValue (integratedMarkedTarget run 4 (by decide))
  positiveRun : MeasuredProjectionOutcome
  positiveRunExact : positiveRun = integratedOrganizationObservation run .compatible
  positiveCodeAtoms : positiveRun.codeAtoms = 1
  negativeRun : MeasuredProjectionOutcome
  negativeRunExact : negativeRun = integratedOrganizationObservation run .incompatible
  negativeCodeAtoms : negativeRun.codeAtoms = 0
  section31Raccord : Section31PrimitiveRaccord run
  constructionWork : ComparisonWork
  constructionWorkExact : constructionWork = (source.work.add positiveTarget.work).add negativeTarget.work

def runIntegratedProjectionExperiment {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : IntegratedProjectionExperiment run :=
  let source := constructMeasuredChild run.storedSchedule.entry.source
    (run.storedSchedule.entry.var + 2) false (retained_source_fresh run 2 (by decide))
  let positiveTarget := constructMeasuredChild run.storedSchedule.entry.target
    (run.storedSchedule.entry.var + 2) false (retained_target_fresh run 2 (by decide))
  let negativeTarget := constructMeasuredChild run.storedSchedule.entry.target
    (run.storedSchedule.entry.var + 4) false (retained_target_fresh run 4 (by decide))
  { source := source
    positiveTarget := positiveTarget
    negativeTarget := negativeTarget
    positiveRun := runMeasuredProjectionFromData run.storedSchedule.entry.var source positiveTarget
      (integratedMarkedContinuation run) input.reader
    positiveRunExact := runMeasuredProjectionFromData_exact _ _ _ _ _
    positiveCodeAtoms := Eq.trans
      (congrArg (fun outcome => outcome.codeAtoms)
        (runMeasuredProjectionFromData_exact _ _ _ _ _))
      (integrated_positive_codeAtoms run)
    negativeRun := runMeasuredProjectionFromData run.storedSchedule.entry.var source negativeTarget
      (integratedMarkedContinuation run) input.reader
    negativeRunExact := runMeasuredProjectionFromData_exact _ _ _ _ _
    negativeCodeAtoms := Eq.trans
      (congrArg (fun outcome => outcome.codeAtoms)
        (runMeasuredProjectionFromData_exact _ _ _ _ _))
      (integrated_negative_codeAtoms run)
    section31Raccord := integrated_section31_primitiveRaccord run
    constructionWork := (source.work.add positiveTarget.work).add negativeTarget.work
    constructionWorkExact := rfl }

def integratedInputProjection {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) (organization : ProjectionOrganization) : Nat × Cnf :=
  (depth, match organization with
    | .compatible => (integratedMarkedTarget run 2 (by decide)).context.formula
    | .incompatible => (integratedMarkedTarget run 4 (by decide)).context.formula)

theorem integrated_projection_not_factors {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    ¬ ValueFactorsThrough (integratedInputProjection run)
      (fun organization => (integratedOrganizationObservation run organization).terminalBit) := by
  apply value_not_factors_of_same_projection _ _ .compatible .incompatible
  · exact congrArg (fun formula => (depth, formula)) (integrated_marked_projection_equal run)
  · rw [integrated_positive_result, integrated_negative_result]
    intro impossible
    cases impossible

def SequentialHistory.firstStage? {depth count : Nat} {input : SequentialAssignment depth} :
    SequentialHistory depth input count → Option (SequentialStageRun depth input)
  | .nil _ _ => none
  | .step head _ => some head

theorem SequentialHistory.firstStage_none {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) : history.firstStage? = none → count = 0 := by
  cases history with
  | nil => intro _; rfl
  | step head tail => intro impossible; cases impossible

def SequentialHistory.firstStage {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input (count + 1)) : SequentialStageRun depth input :=
  match found : history.firstStage? with
  | none => False.elim (Nat.noConfusion (history.firstStage_none found))
  | some head => head

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.residual_preserves_avoids
#print axioms ConstitutiveSearch.EndogenousDecomposition.retained_var_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.retained_decisions_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.growing_root_avoids_above
#print axioms ConstitutiveSearch.EndogenousDecomposition.retained_formulas_avoid_future
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedMarkedSource
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedMarkedTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_marked_constitutions_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_marked_projection_equal
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedMarkedRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_marked_incompatible
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedMarkedContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.runMeasuredProjection
#print axioms ConstitutiveSearch.EndogenousDecomposition.runMeasuredProjection_found
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_positive_found
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_negative_missed
#print axioms ConstitutiveSearch.EndogenousDecomposition.integratedOrganizationObservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_positive_result
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_negative_result
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_positive_codeAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_negative_codeAtoms
#print axioms ConstitutiveSearch.EndogenousDecomposition.runSection31ReferenceProjection
#print axioms ConstitutiveSearch.EndogenousDecomposition.runMeasuredProjection_refines_section31
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_section31_primitiveRaccord
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_positive_agrees_with_main
#print axioms ConstitutiveSearch.EndogenousDecomposition.runMeasuredProjectionFromData
#print axioms ConstitutiveSearch.EndogenousDecomposition.runMeasuredProjectionFromData_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.runIntegratedProjectionExperiment
#print axioms ConstitutiveSearch.EndogenousDecomposition.integrated_projection_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.firstStage
/- AXIOM_AUDIT_END -/
