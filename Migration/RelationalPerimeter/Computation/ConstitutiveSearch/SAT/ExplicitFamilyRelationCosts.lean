import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyTransportCosts

/-!
# Relation-verification surface for the explicit SAT family

This module introduces a transparent structural cost model for the direct global
flip search.

For one sibling comparison, the verification surface counts:
* literal positions in both residual formulas,
* constituted decisions in both histories,
* one unit for the selected flip variable.

This is a representation-level upper surface, not a machine-runtime theorem.
In particular, the bit-cost of natural-number equality and Lean proof checking
are not charged here.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Cnf

/-- Weak branch residual never increases the structural literal count. -/
theorem branchResidual_literalCount_le
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    literalCount (branchResidual formula var value) ≤
      literalCount formula := by
  induction formula with
  | nil =>
      exact Nat.le_refl 0
  | cons clause rest inductionHypothesis =>
      cases hit :
          Clause.containsLiteral
            (Literal.forValue var value)
            clause with
      | false =>
          rw [
            branchResidual_cons_miss
              clause rest var value hit
          ]
          change
            clause.length +
                literalCount (branchResidual rest var value) ≤
              clause.length + literalCount rest
          exact
            Nat.add_le_add_left
              inductionHypothesis
              clause.length
      | true =>
          rw [
            branchResidual_cons_hit
              clause rest var value hit
          ]
          change
            literalCount (branchResidual rest var value) ≤
              clause.length + literalCount rest
          exact
            Nat.le_trans
              inductionHypothesis
              (Nat.le_add_left
                (literalCount rest)
                clause.length)

end Cnf

namespace GeneratedStructuralBranchContext

/-- One generated child never has a larger residual literal count than its parent. -/
theorem child_literalCount_le
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    Cnf.literalCount
        (child parent var value fresh).context.formula ≤
      Cnf.literalCount parent.context.formula := by
  change
    Cnf.literalCount
        (branchResidual parent.context.formula var value) ≤
      Cnf.literalCount parent.context.formula
  exact
    Cnf.branchResidual_literalCount_le
      parent.context.formula
      var
      value

end GeneratedStructuralBranchContext

/--
Exact representation surface inspected by one sibling flip relation.

The formula and history of both children are counted explicitly.
-/
def siblingRelationVerificationSurface
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    Nat :=
  let left :=
    GeneratedStructuralBranchContext.child
      parent var false fresh
  let right :=
    GeneratedStructuralBranchContext.child
      parent var true fresh
  Cnf.literalCount left.context.formula +
    Cnf.literalCount right.context.formula +
      (left.provenanceSize +
        right.provenanceSize + 1)

/-- Uniform one-comparison budget from formula and provenance bounds. -/
def uniformRelationVerificationUnit
    (formulaBound provenanceBound : Nat) :
    Nat :=
  formulaBound + formulaBound +
    (provenanceBound + provenanceBound + 1)

/--
One sibling comparison is bounded by the declared formula/provenance envelope.
-/
theorem siblingRelationVerificationSurface_le
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (formulaBound provenanceBound : Nat)
    (parentFormulaLe :
      Cnf.literalCount parent.context.formula ≤
        formulaBound)
    (childProvenanceLe :
      (GeneratedStructuralBranchContext.child
        parent var true fresh).provenanceSize ≤
          provenanceBound) :
    siblingRelationVerificationSurface
        parent var fresh ≤
      uniformRelationVerificationUnit
        formulaBound provenanceBound := by
  let left :=
    GeneratedStructuralBranchContext.child
      parent var false fresh
  let right :=
    GeneratedStructuralBranchContext.child
      parent var true fresh
  have leftFormulaLe :
      Cnf.literalCount left.context.formula ≤
        formulaBound :=
    Nat.le_trans
      (GeneratedStructuralBranchContext.child_literalCount_le
        parent var false fresh)
      parentFormulaLe
  have rightFormulaLe :
      Cnf.literalCount right.context.formula ≤
        formulaBound :=
    Nat.le_trans
      (GeneratedStructuralBranchContext.child_literalCount_le
        parent var true fresh)
      parentFormulaLe
  have leftProvenanceEq :
      left.provenanceSize =
        parent.provenanceSize + 1 :=
    GeneratedStructuralBranchContext.child_provenanceSize
      parent var false fresh
  have rightProvenanceEq :
      right.provenanceSize =
        parent.provenanceSize + 1 :=
    GeneratedStructuralBranchContext.child_provenanceSize
      parent var true fresh
  have rightProvenanceLe :
      right.provenanceSize ≤ provenanceBound :=
    childProvenanceLe
  have leftProvenanceLe :
      left.provenanceSize ≤ provenanceBound := by
    exact
      Eq.mp
        (congrArg
          (fun value => value ≤ provenanceBound)
          (Eq.trans
            leftProvenanceEq
            rightProvenanceEq.symm))
        rightProvenanceLe
  unfold siblingRelationVerificationSurface
  unfold uniformRelationVerificationUnit
  dsimp [left, right]
  exact
    Nat.add_le_add
      (Nat.add_le_add
        leftFormulaLe
        rightFormulaLe)
      (Nat.add_le_add
        (Nat.add_le_add
          leftProvenanceLe
          rightProvenanceLe)
        (Nat.le_refl 1)
        )

namespace FlipSymmetricTrajectory

/-- Sum of direct sibling-relation verification surfaces along a trajectory. -/
def relationVerificationSurface
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      Nat
  | .done _ =>
      0
  | .step var fresh _symmetric tail =>
      siblingRelationVerificationSurface
        _
        var
        fresh +
      tail.relationVerificationSurface

/--
Uniform bound for the complete direct-relation verification surface.

The formula bound is required at the trajectory start; residual monotonicity
propagates it.  The provenance bound is required at the final state; exact
provenance growth propagates it backwards to every child.
-/
theorem relationVerificationSurface_le_uniform
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    ∀ (formulaBound provenanceBound : Nat),
      Cnf.literalCount start.context.formula ≤ formulaBound →
      finish.provenanceSize ≤ provenanceBound →
      trajectory.relationVerificationSurface ≤
        length *
          uniformRelationVerificationUnit
            formulaBound provenanceBound := by
  induction trajectory with
  | done state =>
      intro formulaBound provenanceBound _formulaLe _provenanceLe
      rw [show
        (FlipSymmetricTrajectory.done state).relationVerificationSurface =
          0 from rfl]
      exact Nat.zero_le _
  | @step parent finish length var fresh symmetric tail inductionHypothesis =>
      intro formulaBound provenanceBound parentFormulaLe finishProvenanceLe
      let child :=
        GeneratedStructuralBranchContext.child
          parent var true fresh
      have childFormulaLe :
          Cnf.literalCount child.context.formula ≤
            formulaBound :=
        Nat.le_trans
          (GeneratedStructuralBranchContext.child_literalCount_le
            parent var true fresh)
          parentFormulaLe
      have finishFromChild :
          finish.provenanceSize =
            child.provenanceSize + length :=
        FlipSymmetricTrajectory.finish_provenanceSize_eq
          tail
      have childProvenanceLeFinish :
          child.provenanceSize ≤
            finish.provenanceSize := by
        rw [finishFromChild]
        exact
          Nat.le_add_right
            child.provenanceSize
            length
      have childProvenanceLe :
          child.provenanceSize ≤
            provenanceBound :=
        Nat.le_trans
          childProvenanceLeFinish
          finishProvenanceLe
      have localLe :
          siblingRelationVerificationSurface
              parent var fresh ≤
            uniformRelationVerificationUnit
              formulaBound provenanceBound :=
        siblingRelationVerificationSurface_le
          parent
          var
          fresh
          formulaBound
          provenanceBound
          parentFormulaLe
          childProvenanceLe
      have tailLe :
          tail.relationVerificationSurface ≤
            length *
              uniformRelationVerificationUnit
                formulaBound provenanceBound :=
        inductionHypothesis
          formulaBound
          provenanceBound
          childFormulaLe
          finishProvenanceLe
      calc
        (FlipSymmetricTrajectory.step
          var fresh symmetric tail).relationVerificationSurface
            =
          siblingRelationVerificationSurface
              parent var fresh +
            tail.relationVerificationSurface :=
              rfl
        _ ≤
          uniformRelationVerificationUnit
              formulaBound provenanceBound +
            length *
              uniformRelationVerificationUnit
                formulaBound provenanceBound :=
              Nat.add_le_add localLe tailLe
        _ =
          (length + 1) *
            uniformRelationVerificationUnit
              formulaBound provenanceBound := by
              rw [Nat.succ_mul]
              exact
                Nat.add_comm
                  (uniformRelationVerificationUnit
                    formulaBound provenanceBound)
                  (length *
                    uniformRelationVerificationUnit
                      formulaBound provenanceBound)

end FlipSymmetricTrajectory

/-- Closed-family direct-relation verification budget. -/
def explicitFamilyRelationVerificationBudget
    (count : Nat) :
    Nat :=
  count *
    uniformRelationVerificationUnit
      (4 * count)
      count

/--
The direct sibling-flip checks used by F(n) stay within the explicit quadratic
representation-surface budget.
-/
theorem explicitFamilyRelationVerificationSurface_le
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).trajectory.relationVerificationSurface ≤
      explicitFamilyRelationVerificationBudget count := by
  apply
    FlipSymmetricTrajectory.relationVerificationSurface_le_uniform
      (explicitFamilyResourceTrajectory count).trajectory
      (4 * count)
      count
  · change
      Cnf.literalCount
          (explicitStackedSymmetricFamily count) ≤
        4 * count
    change
      Cnf.literalCount
          (stackedSymmetricBlocks count count) ≤
        4 * count
    exact
      Nat.le_of_eq
        (stackedSymmetricBlocks_literalCount
          count count)
  · exact
      Nat.le_of_eq
        (explicitFamilyEndpoint_provenanceSize count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_literalCount_le
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.child_literalCount_le
#print axioms ConstitutiveSearch.SAT.siblingRelationVerificationSurface
#print axioms ConstitutiveSearch.SAT.uniformRelationVerificationUnit
#print axioms ConstitutiveSearch.SAT.siblingRelationVerificationSurface_le
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.relationVerificationSurface
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.relationVerificationSurface_le_uniform
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationVerificationBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationVerificationSurface_le
/- AXIOM_AUDIT_END -/
