import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalStage

/-!
Executable comparisons whose evidence and work are returned by one recursion.
Structural-node visits and unary-label constructor steps are disjoint units.
This module measures these operations, not the host evaluator or proof checking.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

structure ComparisonWork where
  nodes : Nat
  labelSteps : Nat
  deriving DecidableEq, Repr

def ComparisonWork.zero : ComparisonWork := ⟨0, 0⟩

def ComparisonWork.add (left right : ComparisonWork) : ComparisonWork :=
  ⟨left.nodes + right.nodes, left.labelSteps + right.labelSteps⟩

def ComparisonWork.visit (work : ComparisonWork) : ComparisonWork :=
  ⟨work.nodes + 1, work.labelSteps⟩

def ComparisonWork.total (work : ComparisonWork) : Nat := work.nodes + work.labelSteps

/-- Total work is additive across the semantic composition of two runs. -/
theorem ComparisonWork.total_add (first second : ComparisonWork) :
    (first.add second).total = first.total + second.total :=
  Nat.add_add_add_comm _ _ _ _

/-- Visiting one structural node adds exactly one unit of total work. -/
theorem ComparisonWork.total_visit (work : ComparisonWork) :
    work.visit.total = work.total + 1 := by
  change (work.nodes + 1) + work.labelSteps = (work.nodes + work.labelSteps) + 1
  rw [Nat.add_assoc, Nat.add_comm 1 work.labelSteps, ← Nat.add_assoc]

structure MeasuredEquality {α : Type} (left right : α) where
  result : Decidable (left = right)
  work : ComparisonWork

def compareUnary : (left right : Nat) → MeasuredEquality left right
  | 0, 0 => ⟨.isTrue rfl, ⟨0, 1⟩⟩
  | 0, _ + 1 => ⟨.isFalse (by intro h; cases h), ⟨0, 1⟩⟩
  | _ + 1, 0 => ⟨.isFalse (by intro h; cases h), ⟨0, 1⟩⟩
  | left + 1, right + 1 =>
    let prior := compareUnary left right
    let result := match prior.result with
      | .isTrue equal => .isTrue (congrArg Nat.succ equal)
      | .isFalse different => .isFalse (fun equal => different (Nat.succ.inj equal))
    ⟨result, ⟨0, prior.work.labelSteps + 1⟩⟩

theorem compareUnary_steps_le (left right : Nat) :
    (compareUnary left right).work.labelSteps ≤ left + 1 := by
  induction left generalizing right with
  | zero => cases right <;> exact Nat.le_refl 1
  | succ left ih =>
    cases right with
    | zero => exact Nat.succ_le_succ (Nat.zero_le _)
    | succ right => exact Nat.add_le_add_right (ih right) 1

theorem compareUnary_self_steps (value : Nat) :
    (compareUnary value value).work.labelSteps = value + 1 := by
  induction value with
  | zero => rfl
  | succ value ih => exact congrArg (fun n => n + 1) ih

def compareMeasuredList {α : Type}
    (compare : (left right : α) → MeasuredEquality left right) :
    (left right : List α) → MeasuredEquality left right
  | [], [] => ⟨.isTrue rfl, ⟨1, 0⟩⟩
  | [], _ :: _ => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩
  | _ :: _, [] => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩
  | left :: leftRest, right :: rightRest =>
    let head := compare left right
    match head.result with
    | .isFalse different =>
      ⟨.isFalse (fun equal => different (List.cons.inj equal).1), head.work.visit⟩
    | .isTrue same =>
      let tail := compareMeasuredList compare leftRest rightRest
      let result := match tail.result with
        | .isTrue restSame => .isTrue (by cases same; cases restSame; rfl)
        | .isFalse restDifferent =>
          .isFalse (fun equal => restDifferent (List.cons.inj equal).2)
      ⟨result, (head.work.add tail.work).visit⟩

def compareMeasuredLiteral : (left right : Literal) → MeasuredEquality left right
  | .positive left, .positive right =>
    let compared := compareUnary left right
    let result := match compared.result with
      | .isTrue same => .isTrue (congrArg Literal.positive same)
      | .isFalse different => .isFalse (by intro h; cases h; exact different rfl)
    ⟨result, compared.work.visit⟩
  | .negative left, .negative right =>
    let compared := compareUnary left right
    let result := match compared.result with
      | .isTrue same => .isTrue (congrArg Literal.negative same)
      | .isFalse different => .isFalse (by intro h; cases h; exact different rfl)
    ⟨result, compared.work.visit⟩
  | .positive _, .negative _ => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩
  | .negative _, .positive _ => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩

def compareMeasuredCnf : (left right : Cnf) → MeasuredEquality left right :=
  compareMeasuredList (compareMeasuredList compareMeasuredLiteral)

def compareMeasuredBool : (left right : Bool) → MeasuredEquality left right
  | false, false => ⟨.isTrue rfl, ⟨1, 0⟩⟩
  | true, true => ⟨.isTrue rfl, ⟨1, 0⟩⟩
  | false, true => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩
  | true, false => ⟨.isFalse (by intro h; cases h), ⟨1, 0⟩⟩

def compareMeasuredDecision (left right : StructuralBranchDecision) :
    MeasuredEquality left right :=
  let labels := compareUnary left.var right.var
  match labels.result with
  | .isFalse different =>
    ⟨.isFalse (fun same => different (congrArg StructuralBranchDecision.var same)),
      labels.work.visit⟩
  | .isTrue labelSame =>
    let values := compareMeasuredBool left.value right.value
    let result := match values.result with
      | .isTrue valueSame => .isTrue (by
        cases left; cases right; cases labelSame; cases valueSame; rfl)
      | .isFalse different =>
        .isFalse (fun same => different (congrArg StructuralBranchDecision.value same))
    ⟨result, (labels.work.add values.work).visit⟩

def compareMeasuredHistory := compareMeasuredList compareMeasuredDecision

/-- A failed first literal prevents visiting the rest of either clause. -/
theorem measuredComparison_short_circuits (leftRest rightRest : Clause) :
    (compareMeasuredList compareMeasuredLiteral
      (.positive 0 :: leftRest) (.negative 0 :: rightRest)).work = ⟨2, 0⟩ := rfl

/-- Growing equal unary labels have genuinely growing executed comparison work. -/
theorem measuredComparison_label_work_grows (value : Nat) :
    (compareUnary value value).work.labelSteps <
      (compareUnary (value + 1) (value + 1)).work.labelSteps := by
  rw [compareUnary_self_steps, compareUnary_self_steps]
  exact Nat.lt_succ_self _

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ComparisonWork.total_add
#print axioms ConstitutiveSearch.EndogenousDecomposition.ComparisonWork.total_visit
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareUnary
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareUnary_steps_le
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareUnary_self_steps
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredList
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredLiteral
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredCnf
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.compareMeasuredHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredComparison_short_circuits
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredComparison_label_work_grows
/- AXIOM_AUDIT_END -/
