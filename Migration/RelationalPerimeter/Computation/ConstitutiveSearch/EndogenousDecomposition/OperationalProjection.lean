import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.EndogenousDiscovery
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveProjectionNonFactorization

/-!
# Same-input operational non-factorization

This module constructs two generated organizations from the same constitutive
input.  Their projected residual formula is identical, but their retained
decision provenance is positively different.  The executable relation finder
succeeds on the provenance-compatible organization and fails on the other.
When it succeeds, the returned transport code is actually evaluated before the
terminal bit is read.

The separator therefore concerns an operational result of the constituted
procedure.  It is not obtained by comparing witnesses that live over different
inputs, and it does not replace positive constitution by a negative premise.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- Selected variable read from the already constituted operational stage. -/
def projectionSplitVar (depth : Nat) : Var :=
  (constructStage depth).searchIndex + 2

/-- Anchor variable of the symmetric root formula. -/
def projectionAnchorVar (depth : Nat) : Var :=
  (constructStage depth).searchIndex + 3

/-- Old provenance marker of the compatible organization. -/
def compatibleMarker : Var := 0

/-- Distinct old provenance marker of the incompatible organization. -/
def incompatibleMarker : Var := 1

/-- Root syntax shared by both organizations at one and the same input. -/
def projectionRootFormula (depth : Nat) : Cnf :=
  symmetricBlockFamily
    (projectionSplitVar depth)
    (projectionAnchorVar depth)
    []

/-- The projected experiment's selected variable is read from constitution. -/
theorem projectionSplitVar_from_constitution (depth : Nat) :
    projectionSplitVar depth =
      growingDiscoverySplitVar (constitutedSearchIndex depth) :=
  rfl

/-- The experiment root is built from the same constituted operational index. -/
theorem projectionRootFormula_from_constitution (depth : Nat) :
    projectionRootFormula depth =
      symmetricBlockFamily
        (growingDiscoverySplitVar (constitutedSearchIndex depth))
        (growingDiscoveryAnchorVar (constitutedSearchIndex depth))
        [] :=
  rfl

theorem projectionSplitVar_lt_anchor (depth : Nat) :
    projectionSplitVar depth < projectionAnchorVar depth := by
  unfold projectionSplitVar projectionAnchorVar
  exact Nat.lt_succ_self _

theorem projectionSplitVar_positive (depth : Nat) :
    0 < projectionSplitVar depth := by
  unfold projectionSplitVar
  exact Nat.zero_lt_succ _

theorem projectionSplitVar_gt_one (depth : Nat) :
    1 < projectionSplitVar depth := by
  unfold projectionSplitVar
  exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

theorem projectionAnchorVar_positive (depth : Nat) :
    0 < projectionAnchorVar depth :=
  Nat.lt_trans
    (projectionSplitVar_positive depth)
    (projectionSplitVar_lt_anchor depth)

theorem projectionAnchorVar_gt_one (depth : Nat) :
    1 < projectionAnchorVar depth :=
  Nat.lt_trans
    (projectionSplitVar_gt_one depth)
    (projectionSplitVar_lt_anchor depth)

theorem projectionRoot_avoids_compatibleMarker (depth : Nat) :
    Cnf.AvoidsVar compatibleMarker (projectionRootFormula depth) := by
  refine ⟨⟨?_, ?_, True.intro⟩, ⟨?_, ?_, True.intro⟩, True.intro⟩
  · exact Nat.ne_of_gt (projectionSplitVar_positive depth)
  · exact Nat.ne_of_gt (projectionAnchorVar_positive depth)
  · exact Nat.ne_of_gt (projectionSplitVar_positive depth)
  · exact Nat.ne_of_gt (projectionAnchorVar_positive depth)

theorem projectionRoot_avoids_incompatibleMarker (depth : Nat) :
    Cnf.AvoidsVar incompatibleMarker (projectionRootFormula depth) := by
  refine ⟨⟨?_, ?_, True.intro⟩, ⟨?_, ?_, True.intro⟩, True.intro⟩
  · exact Nat.ne_of_gt (projectionSplitVar_gt_one depth)
  · exact Nat.ne_of_gt (projectionAnchorVar_gt_one depth)
  · exact Nat.ne_of_gt (projectionSplitVar_gt_one depth)
  · exact Nat.ne_of_gt (projectionAnchorVar_gt_one depth)

/-- Compatible parent, positively generated with marker `0`. -/
def compatibleParent (depth : Nat) :
    GeneratedStructuralBranchContext (projectionRootFormula depth) :=
  GeneratedStructuralBranchContext.child
    (GeneratedStructuralBranchContext.root (projectionRootFormula depth))
    compatibleMarker
    false
    True.intro

/-- Incompatible parent, positively generated with marker `1`. -/
def incompatibleParent (depth : Nat) :
    GeneratedStructuralBranchContext (projectionRootFormula depth) :=
  GeneratedStructuralBranchContext.child
    (GeneratedStructuralBranchContext.root (projectionRootFormula depth))
    incompatibleMarker
    false
    True.intro

theorem projectionSplit_fresh_compatible (depth : Nat) :
    StructuralDecisionsAvoid
      (projectionSplitVar depth)
      (compatibleParent depth).context.decisions := by
  exact
    ⟨Nat.ne_of_lt (projectionSplitVar_positive depth), True.intro⟩

theorem projectionSplit_fresh_incompatible (depth : Nat) :
    StructuralDecisionsAvoid
      (projectionSplitVar depth)
      (incompatibleParent depth).context.decisions := by
  exact
    ⟨Nat.ne_of_lt (projectionSplitVar_gt_one depth), True.intro⟩

/-- Source branch of the operational comparison. -/
def projectedSource (depth : Nat) :
    GeneratedStructuralBranchContext (projectionRootFormula depth) :=
  GeneratedStructuralBranchContext.child
    (compatibleParent depth)
    (projectionSplitVar depth)
    false
    (projectionSplit_fresh_compatible depth)

/-- Target with the exactly flipped generated provenance. -/
def compatibleTarget (depth : Nat) :
    GeneratedStructuralBranchContext (projectionRootFormula depth) :=
  GeneratedStructuralBranchContext.child
    (compatibleParent depth)
    (projectionSplitVar depth)
    true
    (projectionSplit_fresh_compatible depth)

/-- Target with the same projected syntax but a different old provenance. -/
def incompatibleTarget (depth : Nat) :
    GeneratedStructuralBranchContext (projectionRootFormula depth) :=
  GeneratedStructuralBranchContext.child
    (incompatibleParent depth)
    (projectionSplitVar depth)
    true
    (projectionSplit_fresh_incompatible depth)

theorem compatibleParent_formula (depth : Nat) :
    (compatibleParent depth).context.formula = projectionRootFormula depth := by
  exact
    Cnf.branchResidual_eq_self
      (projectionRoot_avoids_compatibleMarker depth)
      false

theorem incompatibleParent_formula (depth : Nat) :
    (incompatibleParent depth).context.formula = projectionRootFormula depth := by
  exact
    Cnf.branchResidual_eq_self
      (projectionRoot_avoids_incompatibleMarker depth)
      false

theorem projectionRoot_flipSymmetric (depth : Nat) :
    FlipSymmetricAt
      (projectionRootFormula depth)
      (projectionSplitVar depth) := by
  exact
    symmetricBlockFamily_flipSymmetric
      (Nat.ne_of_gt (projectionSplitVar_lt_anchor depth))
      True.intro

theorem compatible_formula_exact (depth : Nat) :
    (compatibleTarget depth).context.formula =
      Cnf.flipAt
        (projectionSplitVar depth)
        (projectedSource depth).context.formula := by
  change
    branchResidual
        (compatibleParent depth).context.formula
        (projectionSplitVar depth)
        true =
      Cnf.flipAt
        (projectionSplitVar depth)
        (branchResidual
          (compatibleParent depth).context.formula
          (projectionSplitVar depth)
          false)
  rw [compatibleParent_formula]
  exact projectionRoot_flipSymmetric depth

theorem same_projected_formula (depth : Nat) :
    (compatibleTarget depth).context.formula =
      (incompatibleTarget depth).context.formula := by
  change
    branchResidual
        (compatibleParent depth).context.formula
        (projectionSplitVar depth)
        true =
      branchResidual
        (incompatibleParent depth).context.formula
        (projectionSplitVar depth)
        true
  rw [compatibleParent_formula, incompatibleParent_formula]

theorem compatible_decisions_exact (depth : Nat) :
    (compatibleTarget depth).context.decisions =
      flipStructuralDecisionsAt
        (projectionSplitVar depth)
        (projectedSource depth).context.decisions := by
  unfold compatibleTarget projectedSource compatibleParent
  dsimp [
    GeneratedStructuralBranchContext.child,
    structuralChildContext,
    compatibleMarker
  ]
  rw [flipStructuralDecisionsAt]
  rw [StructuralBranchDecision.flipAt, if_pos rfl]
  rw [flipStructuralDecisionsAt]
  rw [StructuralBranchDecision.flipAt]
  rw [if_neg (Nat.ne_of_lt (projectionSplitVar_positive depth))]
  rfl

theorem incompatible_decisions_not_exact (depth : Nat) :
    (incompatibleTarget depth).context.decisions ≠
      flipStructuralDecisionsAt
        (projectionSplitVar depth)
        (projectedSource depth).context.decisions := by
  intro impossible
  unfold incompatibleTarget incompatibleParent projectedSource compatibleParent at impossible
  dsimp [
    GeneratedStructuralBranchContext.child,
    structuralChildContext,
    compatibleMarker,
    incompatibleMarker
  ] at impossible
  rw [flipStructuralDecisionsAt] at impossible
  rw [StructuralBranchDecision.flipAt, if_pos rfl] at impossible
  rw [flipStructuralDecisionsAt] at impossible
  rw [StructuralBranchDecision.flipAt] at impossible
  rw [if_neg (Nat.ne_of_lt (projectionSplitVar_positive depth))] at impossible
  injection impossible with _ markerEquality
  injection markerEquality with variableEquality _
  cases variableEquality

/-- The compatible relation is produced from the generated histories. -/
def compatibleRelation (depth : Nat) :
    GeneratedStructuralFlipAtRelation
      (rootFormula := projectionRootFormula depth)
      (projectionSplitVar depth)
      (projectedSource depth)
      (compatibleTarget depth) :=
  { formulaExact := compatible_formula_exact depth
    decisionsExact := compatible_decisions_exact depth }

theorem compatible_search_found (depth : Nat) :
    (generatedStructuralFlipAtSearch
      (projectionRootFormula depth)
      (projectionSplitVar depth)).find
        (projectedSource depth)
        (compatibleTarget depth) =
      some (compatibleRelation depth) := by
  unfold compatibleRelation
  dsimp only [generatedStructuralFlipAtSearch]
  rw [dif_pos (compatible_formula_exact depth)]
  rw [dif_pos (compatible_decisions_exact depth)]

theorem incompatible_search_missed (depth : Nat) :
    (generatedStructuralFlipAtSearch
      (projectionRootFormula depth)
      (projectionSplitVar depth)).find
        (projectedSource depth)
        (incompatibleTarget depth) = none := by
  dsimp only [generatedStructuralFlipAtSearch]
  rw [dif_pos]
  · rw [dif_neg (incompatible_decisions_not_exact depth)]
  · rw [← same_projected_formula depth]
    exact compatible_formula_exact depth

/-- Concrete source continuation used only after the finder returns a relation. -/
def projectedSourceContinuation (depth : Nat) :
    GeneratedStructuralBranchContinuation (projectedSource depth) := by
  refine ⟨(fun _variable => false), ?_⟩
  exact ⟨rfl, rfl, True.intro⟩

/-- Observable result of the actual relation-search and transport-code run. -/
structure ProjectedOperationalRun where
  relationFound : Bool
  terminalBit : Option Bool
  executedCodeAtoms : Nat
  deriving DecidableEq, Repr

/--
Run relation search against a supplied generated target.  The successful branch
builds and evaluates the code returned by that exact relation before observing
the terminal bit.
-/
def runProjectedOrganization
    (depth : Nat)
    (target :
      GeneratedStructuralBranchContext (projectionRootFormula depth)) :
    ProjectedOperationalRun :=
  match
    (generatedStructuralFlipAtSearch
      (projectionRootFormula depth)
      (projectionSplitVar depth)).find
        (projectedSource depth)
        target with
  | none =>
      { relationFound := false
        terminalBit := none
        executedCodeAtoms := 0 }
  | some relation =>
      let code := TransportCode.ofGenerator relation
      let transported :=
        (code.eval
          (generatedStructuralFlipAtAction
            (projectionRootFormula depth)
            (projectionSplitVar depth))).map
          (projectedSourceContinuation depth)
      { relationFound := true
        terminalBit := some (transported.1 (projectionSplitVar depth))
        executedCodeAtoms := code.size }

/-- Positive execution evaluates exactly one relation atom and reads `true`. -/
theorem compatible_run_exact (depth : Nat) :
    runProjectedOrganization depth (compatibleTarget depth) =
      { relationFound := true
        terminalBit := some true
        executedCodeAtoms := 1 } := by
  unfold runProjectedOrganization
  rw [compatible_search_found]
  dsimp [
    TransportCode.ofGenerator,
    TransportCode.eval,
    generatedStructuralFlipAtAction,
    GeneratedStructuralFlipAtRelation.toAcceptingTransport,
    GeneratedStructuralFlipAtRelation.mapContinuation,
    projectedSourceContinuation,
    TransportCode.size
  ]
  rw [Assignment.flipAt_selected]
  rfl

/-- Incompatible provenance reaches the explicit finder-failure branch. -/
theorem incompatible_run_exact (depth : Nat) :
    runProjectedOrganization depth (incompatibleTarget depth) =
      { relationFound := false
        terminalBit := none
        executedCodeAtoms := 0 } := by
  unfold runProjectedOrganization
  rw [incompatible_search_missed]

/-- Both organizations and both executions produced for one unchanged input. -/
structure OperationalProjectionExperiment (input : Nat) where
  positiveTarget :
    GeneratedStructuralBranchContext (projectionRootFormula input)
  positiveTargetExact : positiveTarget = compatibleTarget input
  negativeTarget :
    GeneratedStructuralBranchContext (projectionRootFormula input)
  negativeTargetExact : negativeTarget = incompatibleTarget input
  positiveRun : ProjectedOperationalRun
  positiveRunExact :
    positiveRun = runProjectedOrganization input positiveTarget
  negativeRun : ProjectedOperationalRun
  negativeRunExact :
    negativeRun = runProjectedOrganization input negativeTarget

/-- Construct the complete comparison without accepting either target as input. -/
def runOperationalProjectionExperiment
    (input : Nat) : OperationalProjectionExperiment input :=
  { positiveTarget := compatibleTarget input
    positiveTargetExact := rfl
    negativeTarget := incompatibleTarget input
    negativeTargetExact := rfl
    positiveRun := runProjectedOrganization input (compatibleTarget input)
    positiveRunExact := rfl
    negativeRun := runProjectedOrganization input (incompatibleTarget input)
    negativeRunExact := rfl }

theorem projectionExperiment_runs_exact (input : Nat) :
    (runOperationalProjectionExperiment input).positiveRun.terminalBit = some true ∧
      (runOperationalProjectionExperiment input).negativeRun.terminalBit = none := by
  change
    (runProjectedOrganization input (compatibleTarget input)).terminalBit = some true ∧
      (runProjectedOrganization input (incompatibleTarget input)).terminalBit = none
  rw [compatible_run_exact, incompatible_run_exact]
  exact ⟨rfl, rfl⟩

/-- Two organizations over the same input have different retained provenance. -/
theorem organizations_constitutively_distinct (depth : Nat) :
    (compatibleTarget depth).context.decisions ≠
      (incompatibleTarget depth).context.decisions := by
  intro impossible
  unfold compatibleTarget compatibleParent incompatibleTarget incompatibleParent at impossible
  dsimp [GeneratedStructuralBranchContext.child, structuralChildContext] at impossible
  injection impossible with _ markerEquality
  injection markerEquality with variableEquality _
  cases variableEquality

/-- Choice of organization while the external input `depth` remains fixed. -/
inductive ProjectionOrganization where
  | compatible
  | incompatible
  deriving DecidableEq

/-- Generated target selected by the organization, not by changing the input. -/
def organizationTarget
    (depth : Nat) : ProjectionOrganization →
      GeneratedStructuralBranchContext (projectionRootFormula depth)
  | .compatible => compatibleTarget depth
  | .incompatible => incompatibleTarget depth

/-- Output-only projection that forgets constituted decision provenance. -/
def organizationProjection
    (depth : Nat)
    (organization : ProjectionOrganization) : Cnf :=
  (organizationTarget depth organization).context.formula

/-- Operational observation produced after exact relation search and execution. -/
def organizationObservation
    (depth : Nat)
    (organization : ProjectionOrganization) : Option Bool :=
  (runProjectedOrganization depth
    (organizationTarget depth organization)).terminalBit

theorem organization_projection_equal (depth : Nat) :
    organizationProjection depth .compatible =
      organizationProjection depth .incompatible :=
  same_projected_formula depth

theorem organization_observation_different (depth : Nat) :
    organizationObservation depth .compatible ≠
      organizationObservation depth .incompatible := by
  rw [organizationObservation, organizationTarget, compatible_run_exact]
  rw [organizationObservation, organizationTarget, incompatible_run_exact]
  intro impossible
  cases impossible

/--
For every constituted input, the operational observation does not factor
through the output-only formula projection.
-/
theorem operational_observation_not_factors (depth : Nat) :
    ¬ ValueFactorsThrough
        (organizationProjection depth)
        (organizationObservation depth) :=
  value_not_factors_of_same_projection
    (organizationProjection depth)
    (organizationObservation depth)
    .compatible
    .incompatible
    (organization_projection_equal depth)
    (organization_observation_different depth)

/-- Projection that exposes both the unchanged external input and residual syntax. -/
def organizationInputProjection
    (depth : Nat)
    (organization : ProjectionOrganization) : Nat × Cnf :=
  (depth, organizationProjection depth organization)

theorem organization_input_projection_equal (depth : Nat) :
    organizationInputProjection depth .compatible =
      organizationInputProjection depth .incompatible := by
  exact congrArg (fun formula => (depth, formula))
    (organization_projection_equal depth)

/-- Even the pair `(input, projected syntax)` cannot recover the observation. -/
theorem operational_observation_not_factors_through_input
    (depth : Nat) :
    ¬ ValueFactorsThrough
        (organizationInputProjection depth)
        (organizationObservation depth) :=
  value_not_factors_of_same_projection
    (organizationInputProjection depth)
    (organizationObservation depth)
    .compatible
    .incompatible
    (organization_input_projection_equal depth)
    (organization_observation_different depth)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.same_projected_formula
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectionSplitVar_from_constitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectionRootFormula_from_constitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.compatible_search_found
#print axioms ConstitutiveSearch.EndogenousDecomposition.incompatible_search_missed
#print axioms ConstitutiveSearch.EndogenousDecomposition.compatible_run_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.incompatible_run_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.runOperationalProjectionExperiment
#print axioms ConstitutiveSearch.EndogenousDecomposition.projectionExperiment_runs_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.organizations_constitutively_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.operational_observation_not_factors
#print axioms ConstitutiveSearch.EndogenousDecomposition.operational_observation_not_factors_through_input
/- AXIOM_AUDIT_END -/
