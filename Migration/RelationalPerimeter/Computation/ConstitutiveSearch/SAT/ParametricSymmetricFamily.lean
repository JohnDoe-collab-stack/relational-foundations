import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-!
# Parametric SAT family with one-step constitutive width one

This module gives a first unbounded positive family. A symmetric two-clause
block is placed in front of an arbitrary background CNF that does not mention
the selected branch variable.

For every such background, the false and true children are related by the
hardened global flip. Hence the exact two-child frontier admits a certified
reduction to one retained state without any satisfiability query.

The background is arbitrary, so this is a genuinely parametric family rather
than a finite regression.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

def AvoidsVar (var : Var) : Literal → Prop
  | .positive query => query ≠ var
  | .negative query => query ≠ var

theorem flipAt_eq_self
    {var : Var}
    {literal : Literal}
    (avoids : AvoidsVar var literal) :
    flipAt var literal = literal := by
  cases literal with
  | positive query =>
      change query ≠ var at avoids
      rw [flipAt, if_neg avoids]
  | negative query =>
      change query ≠ var at avoids
      rw [flipAt, if_neg avoids]

end Literal

namespace Clause

def AvoidsVar (var : Var) : Clause → Prop
  | [] => True
  | literal :: rest =>
      Literal.AvoidsVar var literal ∧
        AvoidsVar var rest

theorem contains_forValue_false
    {var : Var}
    {clause : Clause}
    (avoids : AvoidsVar var clause)
    (value : Bool) :
    containsLiteral (Literal.forValue var value) clause = false := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rcases avoids with ⟨literalAvoids, restAvoids⟩
      have tailFalse :=
        inductionHypothesis restAvoids
      by_cases same :
          literal = Literal.forValue var value
      · subst literal
        cases value with
        | false =>
            change var ≠ var at literalAvoids
            exact False.elim (literalAvoids rfl)
        | true =>
            change var ≠ var at literalAvoids
            exact False.elim (literalAvoids rfl)
      · rw [containsLiteral, if_neg same]
        exact tailFalse

theorem flipAt_eq_self
    {var : Var}
    {clause : Clause}
    (avoids : AvoidsVar var clause) :
    flipAt var clause = clause := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest inductionHypothesis =>
      rcases avoids with ⟨literalAvoids, restAvoids⟩
      dsimp [flipAt]
      rw [Literal.flipAt_eq_self literalAvoids]
      rw [inductionHypothesis restAvoids]

end Clause

namespace Cnf

def AvoidsVar (var : Var) : Cnf → Prop
  | [] => True
  | clause :: rest =>
      Clause.AvoidsVar var clause ∧
        AvoidsVar var rest

theorem branchResidual_eq_self
    {formula : Cnf}
    {var : Var}
    (avoids : AvoidsVar var formula)
    (value : Bool) :
    branchResidual formula var value = formula := by
  induction formula with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      rcases avoids with ⟨clauseAvoids, restAvoids⟩
      have miss :=
        Clause.contains_forValue_false
          clauseAvoids
          value
      rw [
        branchResidual_cons_miss
          clause rest var value miss
      ]
      rw [inductionHypothesis restAvoids]

theorem flipAt_eq_self
    {formula : Cnf}
    {var : Var}
    (avoids : AvoidsVar var formula) :
    flipAt var formula = formula := by
  induction formula with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      rcases avoids with ⟨clauseAvoids, restAvoids⟩
      dsimp [flipAt]
      rw [Clause.flipAt_eq_self clauseAvoids]
      rw [inductionHypothesis restAvoids]

end Cnf

def FlipSymmetricAt
    (formula : Cnf)
    (var : Var) : Prop :=
  branchResidual formula var true =
    Cnf.flipAt var
      (branchResidual formula var false)

def symmetricPositiveClause
    (var anchor : Var) : Clause :=
  [Literal.positive var, Literal.positive anchor]

def symmetricNegativeClause
    (var anchor : Var) : Clause :=
  [Literal.negative var, Literal.positive anchor]

def symmetricBlockFamily
    (var anchor : Var)
    (background : Cnf) : Cnf :=
  symmetricPositiveClause var anchor ::
    symmetricNegativeClause var anchor ::
      background

theorem symmetricPositiveClause_flip
    {var anchor : Var}
    (anchorDifferent : anchor ≠ var) :
    Clause.flipAt var
        (symmetricPositiveClause var anchor) =
      symmetricNegativeClause var anchor := by
  unfold symmetricPositiveClause symmetricNegativeClause
  dsimp [Clause.flipAt]
  have selected :
      Literal.flipAt var (Literal.positive var) =
        Literal.negative var := by
    rw [Literal.flipAt, if_pos rfl]
  have anchorPreserved :
      Literal.flipAt var (Literal.positive anchor) =
        Literal.positive anchor := by
    rw [Literal.flipAt, if_neg anchorDifferent]
  rw [selected, anchorPreserved]

theorem symmetricBlockFamily_flipSymmetric
    {var anchor : Var}
    {background : Cnf}
    (anchorDifferent : anchor ≠ var)
    (backgroundAvoids : Cnf.AvoidsVar var background) :
    FlipSymmetricAt
      (symmetricBlockFamily var anchor background)
      var := by
  let positiveClause :=
    symmetricPositiveClause var anchor
  let negativeClause :=
    symmetricNegativeClause var anchor
  have falsePositiveMiss :
      Clause.containsLiteral
        (Literal.forValue var false)
        positiveClause = false := by
    rfl
  have falseNegativeHit :
      Clause.containsLiteral
        (Literal.forValue var false)
        negativeClause = true := by
    unfold negativeClause symmetricNegativeClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have truePositiveHit :
      Clause.containsLiteral
        (Literal.forValue var true)
        positiveClause = true := by
    unfold positiveClause symmetricPositiveClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have trueNegativeMiss :
      Clause.containsLiteral
        (Literal.forValue var true)
        negativeClause = false := by
    unfold negativeClause symmetricNegativeClause
    dsimp [Literal.forValue]
    have firstDifferent :
        Literal.negative var ≠ Literal.positive var := by
      intro impossible
      cases impossible
    have secondDifferent :
        Literal.positive anchor ≠ Literal.positive var := by
      intro impossible
      have exactVar : anchor = var :=
        Literal.positive.inj impossible
      exact anchorDifferent exactVar
    rw [Clause.containsLiteral, if_neg firstDifferent]
    rw [Clause.containsLiteral, if_neg secondDifferent]
    rfl
  have backgroundFalse :
      branchResidual background var false = background :=
    Cnf.branchResidual_eq_self
      backgroundAvoids
      false
  have backgroundTrue :
      branchResidual background var true = background :=
    Cnf.branchResidual_eq_self
      backgroundAvoids
      true
  have backgroundFlip :
      Cnf.flipAt var background = background :=
    Cnf.flipAt_eq_self backgroundAvoids
  have falseResidual :
      branchResidual
          (symmetricBlockFamily var anchor background)
          var
          false =
        positiveClause :: background := by
    unfold symmetricBlockFamily
    rw [
      branchResidual_cons_miss
        positiveClause
        (negativeClause :: background)
        var false falsePositiveMiss
    ]
    rw [
      branchResidual_cons_hit
        negativeClause
        background
        var false falseNegativeHit
    ]
    rw [backgroundFalse]
  have trueResidual :
      branchResidual
          (symmetricBlockFamily var anchor background)
          var
          true =
        negativeClause :: background := by
    unfold symmetricBlockFamily
    rw [
      branchResidual_cons_hit
        positiveClause
        (negativeClause :: background)
        var true truePositiveHit
    ]
    rw [
      branchResidual_cons_miss
        negativeClause
        background
        var true trueNegativeMiss
    ]
    rw [backgroundTrue]
  unfold FlipSymmetricAt
  rw [falseResidual, trueResidual]
  change
    negativeClause :: background =
      Clause.flipAt var positiveClause ::
        Cnf.flipAt var background
  rw [backgroundFlip]
  have positiveFlip :
      Clause.flipAt var positiveClause =
        negativeClause := by
    exact symmetricPositiveClause_flip anchorDifferent
  rw [positiveFlip]

theorem flipStructuralDecisionsAt_eq_self
    {var : Var}
    {decisions : List StructuralBranchDecision}
    (avoids : StructuralDecisionsAvoid var decisions) :
    flipStructuralDecisionsAt var decisions = decisions := by
  induction decisions with
  | nil =>
      rfl
  | cons decision rest inductionHypothesis =>
      rcases avoids with ⟨headDifferent, restAvoids⟩
      dsimp [flipStructuralDecisionsAt]
      rw [StructuralBranchDecision.flipAt, if_neg headDifferent]
      rw [inductionHypothesis restAvoids]

def flipSymmetricSiblingRelation
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    GeneratedStructuralFlipAtRelation
      var
      (GeneratedStructuralBranchContext.child
        parent var false fresh)
      (GeneratedStructuralBranchContext.child
        parent var true fresh) :=
  { formulaExact := symmetric
    decisionsExact := by
      change
        ({ var := var, value := true } ::
          parent.context.decisions) =
        flipStructuralDecisionsAt
          var
          ({ var := var, value := false } ::
            parent.context.decisions)
      dsimp [
        flipStructuralDecisionsAt,
        StructuralBranchDecision.flipAt
      ]
      rw [if_pos rfl]
      rw [flipStructuralDecisionsAt_eq_self fresh]
      rfl }

def reduceFlipSymmetricSiblings
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    AcceptedIrreducibleFrontierReduction
      (system := generatedStructuralBranchSystem rootFormula)
      (generatedStructuralFlipAtSearch rootFormula var)
      [GeneratedStructuralBranchContext.child
          parent var false fresh,
        GeneratedStructuralBranchContext.child
          parent var true fresh] :=
  let relation :=
    flipSymmetricSiblingRelation
      parent var fresh symmetric
  { retained :=
      [GeneratedStructuralBranchContext.child
        parent var true fresh]
    preservation :=
      AcceptedFrontierPreservation.absorbFirstIntoSecond
        relation.toAcceptingTransport
    irreducible :=
      SearchIrreducible.singleton
        (generatedStructuralFlipAtSearch rootFormula var)
        (GeneratedStructuralBranchContext.child
          parent var true fresh) }

theorem reduceFlipSymmetricSiblings_width
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    (reduceFlipSymmetricSiblings
      parent var fresh symmetric).width = 1 := by
  rfl

theorem symmetricBlockFamily_root_width_one
    {var anchor : Var}
    {background : Cnf}
    (anchorDifferent : anchor ≠ var)
    (backgroundAvoids : Cnf.AvoidsVar var background) :
    let formula :=
      symmetricBlockFamily var anchor background
    let root :=
      GeneratedStructuralBranchContext.root formula
    (reduceFlipSymmetricSiblings
      root
      var
      True.intro
      (symmetricBlockFamily_flipSymmetric
        anchorDifferent
        backgroundAvoids)).width = 1 := by
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.AvoidsVar
#print axioms ConstitutiveSearch.SAT.Literal.flipAt_eq_self
#print axioms ConstitutiveSearch.SAT.Clause.AvoidsVar
#print axioms ConstitutiveSearch.SAT.Clause.contains_forValue_false
#print axioms ConstitutiveSearch.SAT.Clause.flipAt_eq_self
#print axioms ConstitutiveSearch.SAT.Cnf.AvoidsVar
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_eq_self
#print axioms ConstitutiveSearch.SAT.Cnf.flipAt_eq_self
#print axioms ConstitutiveSearch.SAT.FlipSymmetricAt
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily
#print axioms ConstitutiveSearch.SAT.symmetricPositiveClause_flip
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily_flipSymmetric
#print axioms ConstitutiveSearch.SAT.flipStructuralDecisionsAt_eq_self
#print axioms ConstitutiveSearch.SAT.flipSymmetricSiblingRelation
#print axioms ConstitutiveSearch.SAT.reduceFlipSymmetricSiblings
#print axioms ConstitutiveSearch.SAT.reduceFlipSymmetricSiblings_width
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily_root_width_one
/- AXIOM_AUDIT_END -/
