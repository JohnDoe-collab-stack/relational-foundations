import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialHistory
import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierPreservation

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Opening followed by absorption is the complete operation from the parent
state to the retained right child. The local sibling transport is only its
middle component. -/
def EndogenousFlipDiscovery.fullStepPreservation {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    AcceptedFrontierPreservation (generatedStructuralBranchSystem root)
      [state] [state.child discovery.var true discovery.fresh] :=
  (generatedStructuralExpansion state discovery.var discovery.fresh).trans
    (AcceptedFrontierPreservation.absorbFirstIntoSecond discovery.relation.toAcceptingTransport)

/-- Execute the complete parent-to-retained-child step on an arbitrary
structural continuation. No accepted continuation is required as input. -/
def applyFullConstitutiveStep {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation : GeneratedStructuralBranchContinuation state) :
    GeneratedStructuralBranchContinuation
      (state.child discovery.var true discovery.fresh) :=
  if valueFalse : continuation.1 discovery.var = false then
    discovery.relation.mapContinuation
      ⟨continuation.1, ⟨valueFalse, continuation.2⟩⟩
  else
    ⟨continuation.1,
      ⟨bool_true_of_not_false_for_split (continuation.1 discovery.var) valueFalse,
        continuation.2⟩⟩

theorem applyFullConstitutiveStep_preservesAccept {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation : GeneratedStructuralBranchContinuation state)
    (accepted : GeneratedStructuralBranchAccept state continuation) :
    GeneratedStructuralBranchAccept (state.child discovery.var true discovery.fresh)
      (applyFullConstitutiveStep discovery continuation) := by
  by_cases valueFalse : continuation.1 discovery.var = false
  · unfold applyFullConstitutiveStep
    rw [dif_pos valueFalse]
    apply discovery.relation.mapContinuation_accept
    exact (branchWeakening state.context.formula discovery.var false).preservesSatisfaction accepted
  · unfold applyFullConstitutiveStep
    rw [dif_neg valueFalse]
    exact (branchWeakening state.context.formula discovery.var true).preservesSatisfaction accepted

/-- The assignment returned by a complete step is computed by the branch
actually selected during opening. -/
theorem applyFullConstitutiveStep_assignment {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation : GeneratedStructuralBranchContinuation state) :
    (applyFullConstitutiveStep discovery continuation).1 =
      if continuation.1 discovery.var = false
      then Assignment.flipAt discovery.var continuation.1
      else continuation.1 := by
  by_cases valueFalse : continuation.1 discovery.var = false
  · unfold applyFullConstitutiveStep
    rw [dif_pos valueFalse, if_pos valueFalse]
    exact discovery.relation.mapContinuation_assignment _
  · unfold applyFullConstitutiveStep
    rw [dif_neg valueFalse, if_neg valueFalse]

def stageParentContinuation (depth : Nat) (input : SequentialAssignment depth) :
    GeneratedStructuralBranchContinuation (constructStage (depth + 1)).operationalRoot :=
  ⟨input.assignment, True.intro⟩

/-- The public stage's selected variable is still undetermined on entry. -/
theorem stageParent_selected_false (depth : Nat) (input : SequentialAssignment depth) :
    (stageParentContinuation depth input).1 (canonicalStageDiscovery (depth + 1)).var = false := by
  rw [canonicalStageDiscovery_var]
  exact input.futureSelectedFalse (depth + 1) (Nat.le_refl _)

def executeFullConstitutiveStage (depth : Nat) (input : SequentialAssignment depth) :
    GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        (canonicalStageDiscovery (depth + 1)).var true
        (canonicalStageDiscovery (depth + 1)).fresh) :=
  applyFullConstitutiveStep (canonicalStageDiscovery (depth + 1))
    (stageParentContinuation depth input)

/-- The old execution is exactly the left-branch case of the complete
parental step; the opening operation is no longer left outside the theorem. -/
theorem executeFullConstitutiveStage_assignment (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeFullConstitutiveStage depth input).1 =
      (executeSequentialStage depth input).application.output.1 := by
  unfold executeFullConstitutiveStage
  rw [applyFullConstitutiveStep_assignment, stageParent_selected_false]
  rw [if_pos rfl]
  rw [AppliedDiscoveryExecution.assignment_from_returned_code]
  rw [executedDiscoverySchedule_code]
  rfl

theorem executeFullConstitutiveStage_is_next (depth : Nat)
    (input : SequentialAssignment depth) :
    (executeFullConstitutiveStage depth input).1 =
      (executeSequentialStage depth input).next.assignment := by
  rw [executeFullConstitutiveStage_assignment]
  exact (executeSequentialStage depth input).nextAssignmentExact.symm

/-- Data-level refinement of one retained operational stage by its complete
parental opening-and-absorption operation. -/
structure FullStageExecution {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) where
  parent : GeneratedStructuralBranchContinuation (constructStage (depth + 1)).operationalRoot
  parentExact : parent = stageParentContinuation depth input
  output : GeneratedStructuralBranchContinuation
    ((constructStage (depth + 1)).operationalRoot.child run.discovery.var true run.discovery.fresh)
  outputExact : output = applyFullConstitutiveStep run.discovery parent
  nextAssignmentExact : output.1 = run.next.assignment

def fullStageExecution {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : FullStageExecution run :=
  let parent := stageParentContinuation depth input
  let output := applyFullConstitutiveStep run.discovery parent
  have selectedFalse : parent.1 run.discovery.var = false := by
    change input.assignment run.discovery.var = false
    have entryVar : run.schedule.entry.var = run.discovery.var := by
      rw [run.scheduleExact]
      rfl
    have same : run.discovery.var = stageSelectedVar (depth + 1) :=
      Eq.trans entryVar.symm (sequentialStage_selected_exact run)
    rw [same]
    exact input.futureSelectedFalse (depth + 1) (Nat.le_refl _)
  have assignmentExact : output.1 = run.next.assignment := by
    rw [applyFullConstitutiveStep_assignment, selectedFalse, if_pos rfl]
    change Assignment.flipAt run.discovery.var input.assignment = run.next.assignment
    have entryVar : run.schedule.entry.var = run.discovery.var := by
      rw [run.scheduleExact]
      rfl
    rw [← entryVar]
    rw [sequentialStage_next_from_input run]
  ⟨parent, rfl, output, rfl, assignmentExact⟩

inductive FullHistoryExecution : {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → Type where
  | nil (depth : Nat) (input : SequentialAssignment depth) :
      FullHistoryExecution (.nil depth input)
  | step {depth count : Nat} {input : SequentialAssignment depth}
      (head : SequentialStageRun depth input)
      (tail : SequentialHistory (depth + 1) head.next count)
      (executedHead : FullStageExecution head)
      (executedTail : FullHistoryExecution tail) :
      FullHistoryExecution (.step head tail)

def executeFullHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    (history : SequentialHistory depth input count) → FullHistoryExecution history
  | _, _, _, .nil depth input => .nil depth input
  | _, _, _, .step head tail => .step head tail (fullStageExecution head) (executeFullHistory tail)

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.EndogenousFlipDiscovery.fullStepPreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyFullConstitutiveStep
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyFullConstitutiveStep_preservesAccept
#print axioms ConstitutiveSearch.EndogenousDecomposition.applyFullConstitutiveStep_assignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageParentContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeFullConstitutiveStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeFullConstitutiveStage_assignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeFullConstitutiveStage_is_next
#print axioms ConstitutiveSearch.EndogenousDecomposition.fullStageExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeFullHistory
/- AXIOM_AUDIT_END -/
