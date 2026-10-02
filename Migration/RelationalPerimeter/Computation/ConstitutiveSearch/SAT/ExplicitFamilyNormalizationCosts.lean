import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyRelationCosts

/-!
# Effective generic-search and normalization counts for the explicit SAT family

Earlier modules build the sibling flip witness directly from certified symmetry.
This module reconnects the closed family to the generic executable
`RelationSearch.find` / `normalizeAcceptedFrontier` path.

The counts below are source-level control-flow counts:
* each pair classification invokes `find` in both directions;
* every flip-symmetric level normalizes exactly one two-state sibling frontier.

They are not wall-clock runtime claims.  Equality comparison bit-cost,
allocation, proof checking, and compiler/runtime overhead remain separate.
-/

namespace ConstitutiveSearch

universe uRelation

namespace SAT

/--
The generic exact flip search really finds the certified sibling relation.
This is the bridge from the direct witness construction to executable search.
-/
theorem generatedStructuralFlipAtSearch_sibling_found
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    (generatedStructuralFlipAtSearch rootFormula var).find
        (GeneratedStructuralBranchContext.child
          parent var false fresh)
        (GeneratedStructuralBranchContext.child
          parent var true fresh) ≠
      none := by
  let relation :=
    flipSymmetricSiblingRelation
      parent
      var
      fresh
      symmetric
  have formulaExact :
      (GeneratedStructuralBranchContext.child
        parent var true fresh).context.formula =
        Cnf.flipAt var
          (GeneratedStructuralBranchContext.child
            parent var false fresh).context.formula :=
    relation.formulaExact
  have decisionsExact :
      (GeneratedStructuralBranchContext.child
        parent var true fresh).context.decisions =
        flipStructuralDecisionsAt var
          (GeneratedStructuralBranchContext.child
            parent var false fresh).context.decisions :=
    relation.decisionsExact
  dsimp [generatedStructuralFlipAtSearch]
  rw [dif_pos formulaExact]
  rw [dif_pos decisionsExact]
  intro impossible
  cases impossible

namespace FlipSymmetricTrajectory

/--
Exact number of generic `RelationSearch.find` invocations prescribed by the
pair-classification control flow along the announced trajectory.

One two-state normalization performs one pair classification, and the certified
classifier evaluates both directions, hence two calls per level.
-/
def normalizationFindCallCount
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      Nat
  | .done _ =>
      0
  | .step _var _fresh _symmetric tail =>
      2 + tail.normalizationFindCallCount

/-- Exactly two generic relation-search calls are prescribed per level. -/
theorem normalizationFindCallCount_eq
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.normalizationFindCallCount =
      2 * length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      rw [show
        (FlipSymmetricTrajectory.step
          var fresh symmetric tail).normalizationFindCallCount =
            2 + tail.normalizationFindCallCount from rfl]
      rw [inductionHypothesis]
      rw [Nat.mul_succ]
      exact Nat.add_comm 2 (2 * _)

/--
Representation surface inspected by both directed searches used by each
pair classification along the trajectory.
-/
def normalizationRelationVerificationSurface
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
        siblingRelationVerificationSurface
          _
          var
          fresh +
        tail.normalizationRelationVerificationSurface

/--
Uniform bound for the complete generic-normalization relation-verification
surface.  The factor two is the two directed `find` invocations per level.
-/
theorem normalizationRelationVerificationSurface_le_uniform
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    ∀ (formulaBound provenanceBound : Nat),
      Cnf.literalCount start.context.formula ≤ formulaBound →
      finish.provenanceSize ≤ provenanceBound →
      trajectory.normalizationRelationVerificationSurface ≤
        length *
          (uniformRelationVerificationUnit
              formulaBound provenanceBound +
            uniformRelationVerificationUnit
              formulaBound provenanceBound) := by
  induction trajectory with
  | done state =>
      intro formulaBound provenanceBound _formulaLe _provenanceLe
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
          child.provenanceSize ≤ finish.provenanceSize := by
        rw [finishFromChild]
        exact
          Nat.le_add_right
            child.provenanceSize
            length
      have childProvenanceLe :
          child.provenanceSize ≤ provenanceBound :=
        Nat.le_trans
          childProvenanceLeFinish
          finishProvenanceLe
      have localOne :
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
          tail.normalizationRelationVerificationSurface ≤
            length *
              (uniformRelationVerificationUnit
                  formulaBound provenanceBound +
                uniformRelationVerificationUnit
                  formulaBound provenanceBound) :=
        inductionHypothesis
          formulaBound
          provenanceBound
          childFormulaLe
          finishProvenanceLe
      let unit :=
        uniformRelationVerificationUnit
          formulaBound provenanceBound
      have localTwo :
          siblingRelationVerificationSurface parent var fresh +
              siblingRelationVerificationSurface parent var fresh ≤
            unit + unit :=
        Nat.add_le_add localOne localOne
      change
        (siblingRelationVerificationSurface parent var fresh +
          siblingRelationVerificationSurface parent var fresh) +
            tail.normalizationRelationVerificationSurface ≤
          (length + 1) * (unit + unit)
      calc
        (siblingRelationVerificationSurface parent var fresh +
          siblingRelationVerificationSurface parent var fresh) +
            tail.normalizationRelationVerificationSurface
            ≤
          (unit + unit) +
            length * (unit + unit) :=
              Nat.add_le_add localTwo tailLe
        _ =
          length * (unit + unit) +
            (unit + unit) :=
              Nat.add_comm
                (unit + unit)
                (length * (unit + unit))
        _ =
          (length + 1) * (unit + unit) :=
              (Nat.succ_mul length (unit + unit)).symm


end FlipSymmetricTrajectory

/-- Exact generic-search call count for the closed family `F(n)`. -/
theorem explicitFamilyNormalizationFindCallCount
    (count : Nat) :
    FlipSymmetricTrajectory.normalizationFindCallCount
        (explicitFamilyResourceTrajectory count).trajectory =
      2 * count :=
  FlipSymmetricTrajectory.normalizationFindCallCount_eq
    (explicitFamilyResourceTrajectory count).trajectory

/-- Closed-family budget for both directed checks of every sibling pair. -/
def explicitFamilyNormalizationVerificationBudget
    (count : Nat) : Nat :=
  count *
    (uniformRelationVerificationUnit
        (4 * count)
        count +
      uniformRelationVerificationUnit
        (4 * count)
        count)

/--
The actual generic pair-search control flow on the explicit family stays within
the declared normalization verification-surface budget.
-/
theorem explicitFamilyNormalizationVerificationSurface_le
    (count : Nat) :
    FlipSymmetricTrajectory.normalizationRelationVerificationSurface
        (explicitFamilyResourceTrajectory count).trajectory ≤
      explicitFamilyNormalizationVerificationBudget count := by
  apply
    FlipSymmetricTrajectory.normalizationRelationVerificationSurface_le_uniform
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
#print axioms ConstitutiveSearch.SAT.generatedStructuralFlipAtSearch_sibling_found
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.normalizationFindCallCount
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.normalizationFindCallCount_eq
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.normalizationRelationVerificationSurface
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.normalizationRelationVerificationSurface_le_uniform
#print axioms ConstitutiveSearch.SAT.explicitFamilyNormalizationFindCallCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyNormalizationVerificationBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyNormalizationVerificationSurface_le
/- AXIOM_AUDIT_END -/
