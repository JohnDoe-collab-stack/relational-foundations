import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
open SAT RelationalFoundations RelationalFoundations.CertifiedGrouping

def completed {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles) (data : RoleProfilePayload p) :
    (q : RoleOccurrenceProfile roles) × RoleProfilePayload q := ⟨history.selected p, history.transform p data⟩

theorem completed_cast {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q : RoleOccurrenceProfile roles}
    (same : p = q) (data : RoleProfilePayload p) :
    completed history q (same ▸ data) = completed history p data := by
  cases same
  rfl

def liftCompleted {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state} {tail : CausalConstitutiveExecutionHistory count head.next}
    {role : RelationalConstitutiveRoleStage head} {roles : RelationalConstitutiveRoleHistory tail}
    (status : RoleStatus.Status role) (occurrence : RoleConstitutedOccurrence role) (data : RoleOpeningPayload occurrence)
    (packed : (q : RoleOccurrenceProfile roles) × RoleProfilePayload q) :
    (q : RoleOccurrenceProfile (.step role roles)) × RoleProfilePayload q :=
  ⟨(RoleStatus.target status occurrence, packed.1), (RoleStatus.act status occurrence data, packed.2)⟩

theorem coded_completed : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → {p q : Binary.Profile (roleShape roles)} →
    (step : Binary.Move (mask history) p q) → (data : RoleProfilePayload (decode roles p)) →
    completed history (decode roles p) data = completed history (decode roles q) (codedAction history step data)
  | _, _, _, _, .nil, _, _, step, _ => nomatch step
  | _, _, _, _, @RoleStatus.History.step _ _ _ _ role roles none rest, p, _, step, data => by
      let occurrence := (decode (.step role roles) p).1
      cases step with
      | tail child =>
          exact congrArg (liftCompleted (roles := roles) none occurrence data.1)
            (coded_completed rest child data.2)
  | _, _, _, _, @RoleStatus.History.step _ _ _ _ role roles (some transport) rest, p, _, step, data => by
      let occurrence := (decode (.step role roles) p).1
      cases step with
      | head => rfl
      | tail child =>
          exact congrArg (liftCompleted (roles := roles) (some transport) occurrence data.1)
            (coded_completed rest child data.2)


theorem completed_step {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (step : (rules history).Step p q) (data : RoleProfilePayload p) :
    completed history p data = completed history q (act history step data) :=
  (completed_cast history (decode_encode roles p).symm data).symm.trans
    ((coded_completed history step.down _).trans (completed_cast history (decode_encode roles q) _).symm)

theorem completed_trace {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (trace : Trace (rules history).Step p q) (data : RoleProfilePayload p) :
    completed history p data = completed history q ((normative history).transport trace data) := by
  induction trace with
  | nil => rfl
  | cons step tail ih => exact (completed_step history step data).trans (ih (act history step data))

theorem selected_completed : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → (p : RoleOccurrenceProfile roles) →
    (data : RoleProfilePayload (history.selected p)) →
    completed history (history.selected p) data = ⟨history.selected p, data⟩
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, @RoleStatus.History.step _ _ _ _ _ roles none rest, p, data =>
      congrArg (liftCompleted (roles := roles) none p.1 data.1) (selected_completed rest p.2 data.2)
  | _, _, _, _, @RoleStatus.History.step _ _ _ _ role roles (some transport) rest, p, data =>
      congrArg (liftCompleted (roles := roles) (some transport) (roleConstitutedOccurrenceAt role .right) data.1)
        (selected_completed rest p.2 data.2)


theorem every_normalizing_trace {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles)
    (trace : Trace (rules history).Step p (history.selected p)) (data : RoleProfilePayload p) :
    (normative history).transport trace data = history.transform p data := by
  have same := (completed_trace history trace data).trans (selected_completed history p _)
  exact (eq_of_heq (Sigma.mk.inj same).2).symm

theorem normalization_coherent {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles)
    (first second : Trace (rules history).Step p (history.selected p)) (data : RoleProfilePayload p) :
    (normative history).transport first data = (normative history).transport second data :=
  (every_normalizing_trace history p first data).trans
    (every_normalizing_trace history p second data).symm

theorem executed_trace_output {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p : RoleOccurrenceProfile roles)
    (trace : Trace (rules (RoleStatus.executed reduction)).Step p
      ((RoleStatus.executed reduction).selected p)) :
    RoleStatus.executedPayloadOutput reduction p
      ((normative (RoleStatus.executed reduction)).transport trace (canonicalRoleProfilePayload roles p)) =
      retainedExecutedOperationalTargetProfile reduction := by
  rw [every_normalizing_trace]
  exact canonical_output reduction p
end ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.coded_completed
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.completed_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.completed_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.selected_completed
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.every_normalizing_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normalization_coherent
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.executed_trace_output
/- AXIOM_AUDIT_END -/
