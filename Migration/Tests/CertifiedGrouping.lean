import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.HistoricalRoleGrouping
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleGroupingSemantics
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests
open SAT RelationalFoundations RelationalFoundations.CertifiedGrouping CertifiedRoleGrouping

theorem entire_history {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p q : RoleOccurrenceProfile roles) :
    (rules history).normal p = history.selected p ∧
    ((rolewiseCarry history.policy p = rolewiseCarry history.policy q) ↔
      Nonempty (Chain (rules history).Step p q)) ∧
    (FiniteImage.frontier (rules history) (finiteSource roles)).length = 2 ^ history.pendingCount :=
  ⟨normal_selected history p, carry_fibres history p q, exhaustive_width history⟩

theorem arbitrary_payload {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (path : Trace (rules history).Step p q)
    (data : RoleProfilePayload p) (accepted : RoleSemantics.ProfileAccept p data) :
    RoleSemantics.ProfileAccept q ((normative history).transport path data) :=
  all_trace_acceptance history path data accepted

theorem composed_execution {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p q : RoleOccurrenceProfile roles) :
    (rules (RoleStatus.executed reduction)).normal p = retainedRoleProfile reduction ∧
    Nonempty (ProjectionFamily.Path (projection (RoleStatus.executed reduction)) p q) ∧
    (composed (RoleStatus.executed reduction)).frontier.length = 1 := by
  refine ⟨executed_normal reduction p, ⟨executed_path reduction p q⟩, ?_⟩
  rw [composed_width, RoleStatus.executed_pendingCount]

theorem arbitrary_normalization {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles)
    (first second : Trace (rules history).Step p (history.selected p)) (data : RoleProfilePayload p) :
    (normative history).transport first data = history.transform p data ∧
    (normative history).transport first data = (normative history).transport second data :=
  ⟨every_normalizing_trace history p first data, normalization_coherent history p first second data⟩
end ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests.entire_history
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests.arbitrary_payload
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests.composed_execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedGroupingTests.arbitrary_normalization
/- AXIOM_AUDIT_END -/
