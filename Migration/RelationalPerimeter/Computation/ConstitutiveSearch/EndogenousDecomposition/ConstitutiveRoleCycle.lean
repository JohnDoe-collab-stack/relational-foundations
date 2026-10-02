import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFullStep

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- The four roles are projections of one produced stage, not four unrelated
algorithms and not complexity-class identifications. -/
structure ConstitutiveRoleStage {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) where
  searchState : GeneratedStructuralBranchContext
    (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
  searchStateExact : searchState = (constructStage (depth + 1)).operationalRoot
  structuralOpening : AcceptingExactBinarySplit
    (generatedStructuralBranchSystem (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
    searchState
    (searchState.child run.discovery.var false (by rw [searchStateExact]; exact run.discovery.fresh))
    (searchState.child run.discovery.var true (by rw [searchStateExact]; exact run.discovery.fresh))
  selectedDecision : StructuralBranchDecision
  selectedDecisionExact : selectedDecision = ⟨run.discovery.var, true⟩
  reconstructedRelation : GeneratedStructuralFlipAtRelation run.storedSchedule.entry.var
    run.storedSchedule.entry.source run.storedSchedule.entry.target
  reconstructedRelationExact : reconstructedRelation = run.storedSchedule.entry.relation
  completeExecution : FullStageExecution run
  outputBecomesNextCondition : completeExecution.output.1 = run.next.assignment

def constitutiveRoleStage {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : ConstitutiveRoleStage run :=
  let searchState := (constructStage (depth + 1)).operationalRoot
  { searchState := searchState
    searchStateExact := rfl
    structuralOpening := generatedStructuralSplit searchState run.discovery.var run.discovery.fresh
    selectedDecision := ⟨run.discovery.var, true⟩
    selectedDecisionExact := rfl
    reconstructedRelation := run.storedSchedule.entry.relation
    reconstructedRelationExact := rfl
    completeExecution := fullStageExecution run
    outputBecomesNextCondition := (fullStageExecution run).nextAssignmentExact }

/-- Every tail is indexed by the preceding stage's produced `next`, so the
cycle cannot consume an independently supplied replacement state. -/
inductive ConstitutiveRoleHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → Type where
  | nil (depth : Nat) (input : SequentialAssignment depth) :
      ConstitutiveRoleHistory (.nil depth input)
  | step {depth count : Nat} {input : SequentialAssignment depth}
      (head : SequentialStageRun depth input)
      (tail : SequentialHistory (depth + 1) head.next count)
      (roles : ConstitutiveRoleStage head)
      (nextRoles : ConstitutiveRoleHistory tail) :
      ConstitutiveRoleHistory (.step head tail)

def buildConstitutiveRoleHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    (history : SequentialHistory depth input count) → ConstitutiveRoleHistory history
  | _, _, _, .nil depth input => .nil depth input
  | _, _, _, .step head tail =>
      .step head tail (constitutiveRoleStage head) (buildConstitutiveRoleHistory tail)

theorem roleStage_relation_is_discovered {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    HEq (constitutiveRoleStage run).reconstructedRelation run.discovery.relation := by
  rw [(constitutiveRoleStage run).reconstructedRelationExact]
  rw [run.storedSchedule.entryExact]
  rfl

theorem roleStage_complete_operation_is_next {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (constitutiveRoleStage run).completeExecution.output.1 = run.next.assignment :=
  (constitutiveRoleStage run).outputBecomesNextCondition

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveRoleStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveRoleStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleStage_relation_is_discovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleStage_complete_operation_is_next
/- AXIOM_AUDIT_END -/
