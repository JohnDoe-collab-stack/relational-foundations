import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredStateConstruction

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

def unaryListSize {α : Type} (size : α → Nat) : List α → Nat
  | [] => 1
  | head :: tail => size head + unaryListSize size tail + 1

def unaryLiteralSize : Literal → Nat
  | .positive label => label + 2
  | .negative label => label + 2

def unaryClauseSize := unaryListSize unaryLiteralSize
def unaryCnfSize := unaryListSize unaryClauseSize

theorem compareUnary_nodes (left right : Nat) : (compareUnary left right).work.nodes = 0 := by
  cases left <;> cases right <;> rfl

theorem compareUnary_total_le (left right : Nat) :
    (compareUnary left right).work.total ≤ left + 1 := by
  unfold ComparisonWork.total
  rw [compareUnary_nodes, Nat.zero_add]
  exact compareUnary_steps_le left right

theorem compareMeasuredList_bound {α : Type}
    (compare : (left right : α) → MeasuredEquality left right)
    (size : α → Nat)
    (bound : ∀ left right, (compare left right).work.total ≤ size left)
    (left right : List α) :
    (compareMeasuredList compare left right).work.total ≤ unaryListSize size left := by
  induction left generalizing right with
  | nil => cases right <;> exact Nat.le_refl 1
  | cons head tail ih =>
    cases right with
    | nil => exact Nat.succ_le_succ (Nat.zero_le _)
    | cons other rest =>
      unfold compareMeasuredList
      dsimp only
      split
      · change (compare head other).work.visit.total ≤ size head + unaryListSize size tail + 1
        rw [ComparisonWork.total_visit]
        exact Nat.add_le_add_right
          (Nat.le_trans (bound head other) (Nat.le_add_right _ _)) 1
      · change ((compare head other).work.add
          (compareMeasuredList compare tail rest).work).visit.total ≤ _
        rw [ComparisonWork.total_visit, ComparisonWork.total_add]
        exact Nat.add_le_add_right (Nat.add_le_add (bound head other) (ih rest)) 1

theorem compareMeasuredLiteral_bound (left right : Literal) :
    (compareMeasuredLiteral left right).work.total ≤ unaryLiteralSize left := by
  cases left with
  | positive label =>
    cases right with
    | negative other => exact Nat.succ_le_succ (Nat.zero_le _)
    | positive other =>
      change (compareUnary label other).work.visit.total ≤ label + 2
      rw [ComparisonWork.total_visit]
      exact Nat.add_le_add_right (compareUnary_total_le label other) 1
  | negative label =>
    cases right with
    | positive other => exact Nat.succ_le_succ (Nat.zero_le _)
    | negative other =>
      change (compareUnary label other).work.visit.total ≤ label + 2
      rw [ComparisonWork.total_visit]
      exact Nat.add_le_add_right (compareUnary_total_le label other) 1

theorem compareMeasuredCnf_bound (left right : Cnf) :
    (compareMeasuredCnf left right).work.total ≤ unaryCnfSize left :=
  compareMeasuredList_bound _ _
    (compareMeasuredList_bound _ _ compareMeasuredLiteral_bound) left right

theorem flipMeasuredLiteral_bound (selected : Var) (literal : Literal) :
    (flipMeasuredLiteral selected literal).work.total ≤ unaryLiteralSize literal := by
  cases literal with
  | positive label =>
    unfold flipMeasuredLiteral
    dsimp only
    split <;>
      change (compareUnary label selected).work.visit.total ≤ label + 2 <;>
      rw [ComparisonWork.total_visit] <;>
      exact Nat.add_le_add_right (compareUnary_total_le label selected) 1
  | negative label =>
    unfold flipMeasuredLiteral
    dsimp only
    split <;>
      change (compareUnary label selected).work.visit.total ≤ label + 2 <;>
      rw [ComparisonWork.total_visit] <;>
      exact Nat.add_le_add_right (compareUnary_total_le label selected) 1

theorem flipMeasuredClause_bound (selected : Var) (clause : Clause) :
    (flipMeasuredClause selected clause).work.total ≤ unaryClauseSize clause := by
  induction clause with
  | nil => exact Nat.le_refl 1
  | cons literal rest ih =>
    change ((flipMeasuredLiteral selected literal).work.add
      (flipMeasuredClause selected rest).work).visit.total ≤ _
    rw [ComparisonWork.total_visit, ComparisonWork.total_add]
    exact Nat.add_le_add_right (Nat.add_le_add (flipMeasuredLiteral_bound _ _) ih) 1

theorem flipMeasuredCnf_bound (selected : Var) (formula : Cnf) :
    (flipMeasuredCnf selected formula).work.total ≤ unaryCnfSize formula := by
  induction formula with
  | nil => exact Nat.le_refl 1
  | cons clause rest ih =>
    change ((flipMeasuredClause selected clause).work.add
      (flipMeasuredCnf selected rest).work).visit.total ≤ _
    rw [ComparisonWork.total_visit, ComparisonWork.total_add]
    exact Nat.add_le_add_right (Nat.add_le_add (flipMeasuredClause_bound _ _) ih) 1

theorem containsMeasuredLiteral_bound (target : Literal) (clause : Clause) :
    (containsMeasuredLiteral target clause).work.total ≤ unaryClauseSize clause := by
  induction clause with
  | nil => exact Nat.le_refl 1
  | cons literal rest ih =>
    unfold containsMeasuredLiteral
    dsimp only
    split
    · change (compareMeasuredLiteral literal target).work.visit.total ≤ _
      rw [ComparisonWork.total_visit]
      exact Nat.add_le_add_right
        (Nat.le_trans (compareMeasuredLiteral_bound _ _) (Nat.le_add_right _ _)) 1
    · change ((compareMeasuredLiteral literal target).work.add
        (containsMeasuredLiteral target rest).work).visit.total ≤ _
      rw [ComparisonWork.total_visit, ComparisonWork.total_add]
      exact Nat.add_le_add_right (Nat.add_le_add (compareMeasuredLiteral_bound _ _) ih) 1

theorem constructMeasuredResidual_bound (selected : Var) (value : Bool) (formula : Cnf) :
    (constructMeasuredResidual selected value formula).work.total ≤ unaryCnfSize formula := by
  induction formula with
  | nil => exact Nat.le_refl 1
  | cons clause rest ih =>
    unfold constructMeasuredResidual
    dsimp only
    split <;>
      change ((constructMeasuredResidual selected value rest).work.add
        (containsMeasuredLiteral (Literal.forValue selected value) clause).work).visit.total ≤ _ <;>
      rw [ComparisonWork.total_visit, ComparisonWork.total_add] <;>
      exact Nat.le_trans
        (Nat.add_le_add_right (Nat.add_le_add ih (containsMeasuredLiteral_bound _ _)) 1)
        (Nat.le_of_eq (congrArg (fun n => n + 1) (Nat.add_comm _ _)))

theorem constructMeasuredChild_bound {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) (selected : Var) (value : Bool)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    (constructMeasuredChild parent selected value fresh).work.total ≤
      unaryCnfSize parent.context.formula + 1 := by
  change (constructMeasuredResidual selected value parent.context.formula).work.visit.total ≤ _
  rw [ComparisonWork.total_visit]
  exact Nat.add_le_add_right (constructMeasuredResidual_bound _ _ _) 1

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareUnary_total_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredList_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredLiteral_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredCnf_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredLiteral_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredClause_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredCnf_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.containsMeasuredLiteral_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredResidual_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredChild_bound
/- AXIOM_AUDIT_END -/
