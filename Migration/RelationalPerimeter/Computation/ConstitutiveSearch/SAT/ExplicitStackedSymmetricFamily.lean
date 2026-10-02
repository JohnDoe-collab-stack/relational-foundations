import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ParametricSymmetricTrajectory

/-!
# Explicit stacked symmetric SAT family

This module closes the gap between an arbitrary certified flip-symmetric
trajectory and a concrete CNF family indexed by a natural number.

For `n`, the formula contains `n` symmetric two-clause blocks over the
decision variables `0, ..., n-1` and uses `n` itself as a common anchor.
The announced strategy decides variables in descending order.  Because the
current residual is the weak branch residual, each true decision retains the
negative sibling clause.  Those retained clauses form an explicit accumulated.

The constructor below tracks that accumulated, proves each next variable fresh,
proves each current residual flip-symmetric, and builds a
`FlipSymmetricTrajectory` of length exactly `n`.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Cnf

/-- Avoidance is preserved by CNF append. -/
theorem avoidsVar_append
    {var : Var}
    {left right : Cnf}
    (leftAvoids : AvoidsVar var left)
    (rightAvoids : AvoidsVar var right) :
    AvoidsVar var (left ++ right) := by
  induction left with
  | nil =>
      exact rightAvoids
  | cons clause rest inductionHypothesis =>
      rcases leftAvoids with
        ⟨clauseAvoids, restAvoids⟩
      exact
        ⟨clauseAvoids,
          inductionHypothesis restAvoids⟩

/-- Weak branch residual distributes over CNF append. -/
theorem branchResidual_append
    (left right : Cnf)
    (var : Var)
    (value : Bool) :
    branchResidual (left ++ right) var value =
      branchResidual left var value ++
        branchResidual right var value := by
  induction left with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      change
        branchResidual
            (clause :: (rest ++ right))
            var
            value =
          branchResidual
              (clause :: rest)
              var
              value ++
            branchResidual right var value
      cases hit :
          Clause.containsLiteral
            (Literal.forValue var value)
            clause with
      | false =>
          rw [
            branchResidual_cons_miss
              clause
              (rest ++ right)
              var
              value
              hit,
            branchResidual_cons_miss
              clause
              rest
              var
              value
              hit,
            inductionHypothesis
          ]
          rfl
      | true =>
          rw [
            branchResidual_cons_hit
              clause
              (rest ++ right)
              var
              value
              hit,
            branchResidual_cons_hit
              clause
              rest
              var
              value
              hit,
            inductionHypothesis
          ]

/-- Polarity flip distributes over CNF append. -/
theorem flipAt_append
    (var : Var)
    (left right : Cnf) :
    flipAt var (left ++ right) =
      flipAt var left ++ flipAt var right := by
  induction left with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      dsimp [flipAt]
      rw [inductionHypothesis]

end Cnf

namespace FlipSymmetricAt

/--
An accumulated prefix that avoids the selected variable can be placed in front of a
flip-symmetric body without destroying the symmetry.
-/
theorem prepend_avoiding
    {accumulated body : Cnf}
    {var : Var}
    (accumulatedAvoids : Cnf.AvoidsVar var accumulated)
    (bodySymmetric : FlipSymmetricAt body var) :
    FlipSymmetricAt (accumulated ++ body) var := by
  unfold FlipSymmetricAt at bodySymmetric ⊢
  rw [
    Cnf.branchResidual_append,
    Cnf.branchResidual_append,
    Cnf.branchResidual_eq_self
      accumulatedAvoids
      true,
    Cnf.branchResidual_eq_self
      accumulatedAvoids
      false,
    Cnf.flipAt_append,
    Cnf.flipAt_eq_self accumulatedAvoids,
    bodySymmetric
  ]

end FlipSymmetricAt

/-- Exact true residual of one symmetric block over an avoiding background. -/
theorem symmetricBlockFamily_trueResidual
    {var anchor : Var}
    {background : Cnf}
    (anchorDifferent : anchor ≠ var)
    (backgroundAvoids : Cnf.AvoidsVar var background) :
    branchResidual
        (symmetricBlockFamily var anchor background)
        var
        true =
      symmetricNegativeClause var anchor ::
        background := by
  have positiveHit :
      Clause.containsLiteral
        (Literal.forValue var true)
        (symmetricPositiveClause var anchor) =
          true := by
    unfold symmetricPositiveClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have negativeMiss :
      Clause.containsLiteral
        (Literal.forValue var true)
        (symmetricNegativeClause var anchor) =
          false := by
    unfold symmetricNegativeClause
    dsimp [Literal.forValue]
    have firstDifferent :
        Literal.negative var ≠ Literal.positive var := by
      intro impossible
      cases impossible
    have secondDifferent :
        Literal.positive anchor ≠
          Literal.positive var := by
      intro impossible
      exact
        anchorDifferent
          (Literal.positive.inj impossible)
    rw [Clause.containsLiteral, if_neg firstDifferent]
    rw [Clause.containsLiteral, if_neg secondDifferent]
    rfl
  unfold symmetricBlockFamily
  rw [
    branchResidual_cons_hit
      (symmetricPositiveClause var anchor)
      (symmetricNegativeClause var anchor ::
        background)
      var
      true
      positiveHit,
    branchResidual_cons_miss
      (symmetricNegativeClause var anchor)
      background
      var
      true
      negativeMiss,
    Cnf.branchResidual_eq_self
      backgroundAvoids
      true
  ]

/--
Stack `count` symmetric blocks.  Block variables are
`count-1, ..., 0`; `anchor` is shared by every block.
-/
def stackedSymmetricBlocks :
    Nat → Var → Cnf
  | 0, _anchor =>
      []
  | count + 1, anchor =>
      symmetricBlockFamily
        count
        anchor
        (stackedSymmetricBlocks count anchor)

/-- Closed family: the common anchor is exactly the block count. -/
def explicitStackedSymmetricFamily
    (count : Nat) : Cnf :=
  stackedSymmetricBlocks count count

/-- The explicit family has exactly two clauses per level. -/
theorem stackedSymmetricBlocks_length
    (count : Nat)
    (anchor : Var) :
    (stackedSymmetricBlocks count anchor).length =
      2 * count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      dsimp [
        stackedSymmetricBlocks,
        symmetricBlockFamily
      ]
      rw [inductionHypothesis]
      rw [Nat.mul_succ]

/--
All variables in a stack of size `count` avoid every query at least
`count`, provided the common anchor is not that query.
-/
theorem stackedSymmetricBlocks_avoids_of_le
    {count query anchor : Nat}
    (countLeQuery : count ≤ query)
    (queryDifferentAnchor : query ≠ anchor) :
    Cnf.AvoidsVar
      query
      (stackedSymmetricBlocks count anchor) := by
  induction count with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      have countLtQuery : count < query :=
        Nat.lt_of_lt_of_le
          (Nat.lt_succ_self count)
          countLeQuery
      have countDifferentQuery : count ≠ query :=
        Nat.ne_of_lt countLtQuery
      have anchorDifferentQuery : anchor ≠ query :=
        queryDifferentAnchor.symm
      have tailAvoids :
          Cnf.AvoidsVar
            query
            (stackedSymmetricBlocks count anchor) :=
        inductionHypothesis
          (Nat.le_trans
            (Nat.le_succ count)
            countLeQuery)
      change
        Clause.AvoidsVar
            query
            (symmetricPositiveClause count anchor) ∧
          Clause.AvoidsVar
            query
            (symmetricNegativeClause count anchor) ∧
          Cnf.AvoidsVar
            query
            (stackedSymmetricBlocks count anchor)
      constructor
      · exact
          ⟨countDifferentQuery,
            ⟨anchorDifferentQuery, True.intro⟩⟩
      · exact
          ⟨⟨countDifferentQuery,
              ⟨anchorDifferentQuery, True.intro⟩⟩,
            tailAvoids⟩

/--
An accumulated prefix is safe for the remaining `count` levels when it avoids every
decision variable strictly below `count`.
-/
def PrefixAvoidsBelow
    (count : Nat)
    (accumulated : Cnf) : Prop :=
  ∀ query : Var,
    query < count →
      Cnf.AvoidsVar query accumulated

/--
A decision history is safe for the remaining `count` levels when all those
future decision variables are fresh.
-/
def DecisionsAvoidBelow
    (count : Nat)
    (decisions : List StructuralBranchDecision) : Prop :=
  ∀ query : Var,
    query < count →
      StructuralDecisionsAvoid query decisions

/--
The true residual of the head block in a nonempty stack leaves exactly its
negative sibling clause followed by the remaining stack.
-/
theorem stackedSymmetricBlocks_trueResidual
    {count anchor : Nat}
    (countSuccLeAnchor : count + 1 ≤ anchor) :
    branchResidual
        (stackedSymmetricBlocks (count + 1) anchor)
        count
        true =
      symmetricNegativeClause count anchor ::
        stackedSymmetricBlocks count anchor := by
  have currentLtAnchor : count < anchor :=
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self count)
      countSuccLeAnchor
  have anchorDifferentCurrent : anchor ≠ count :=
    (Nat.ne_of_lt currentLtAnchor).symm
  have tailAvoidsCurrent :
      Cnf.AvoidsVar
        count
        (stackedSymmetricBlocks count anchor) :=
    stackedSymmetricBlocks_avoids_of_le
      (Nat.le_refl count)
      (Nat.ne_of_lt currentLtAnchor)
  change
    branchResidual
        (symmetricBlockFamily
          count
          anchor
          (stackedSymmetricBlocks count anchor))
        count
        true =
      symmetricNegativeClause count anchor ::
        stackedSymmetricBlocks count anchor
  exact
    symmetricBlockFamily_trueResidual
      anchorDifferentCurrent
      tailAvoidsCurrent

/--
One explicit stacked stage is flip-symmetric at its current decision variable.
-/
theorem stackedStage_flipSymmetric
    {count anchor : Nat}
    {accumulated : Cnf}
    (accumulatedSafe :
      PrefixAvoidsBelow (count + 1) accumulated)
    (countSuccLeAnchor : count + 1 ≤ anchor) :
    FlipSymmetricAt
      (accumulated ++
        stackedSymmetricBlocks (count + 1) anchor)
      count := by
  have currentLtAnchor : count < anchor :=
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self count)
      countSuccLeAnchor
  have anchorDifferentCurrent : anchor ≠ count :=
    (Nat.ne_of_lt currentLtAnchor).symm
  have tailAvoidsCurrent :
      Cnf.AvoidsVar
        count
        (stackedSymmetricBlocks count anchor) :=
    stackedSymmetricBlocks_avoids_of_le
      (Nat.le_refl count)
      (Nat.ne_of_lt currentLtAnchor)
  have bodySymmetric :
      FlipSymmetricAt
        (symmetricBlockFamily
          count
          anchor
          (stackedSymmetricBlocks count anchor))
        count :=
    symmetricBlockFamily_flipSymmetric
      anchorDifferentCurrent
      tailAvoidsCurrent
  have accumulatedAvoidsCurrent :
      Cnf.AvoidsVar count accumulated :=
    accumulatedSafe
      count
      (Nat.lt_succ_self count)
  change
    FlipSymmetricAt
      (accumulated ++
        symmetricBlockFamily
          count
          anchor
          (stackedSymmetricBlocks count anchor))
      count
  exact
    FlipSymmetricAt.prepend_avoiding
      accumulatedAvoidsCurrent
      bodySymmetric

/--
The true branch of one explicit stacked stage appends exactly one retained
negative clause to the accumulated prefix.
-/
theorem append_singleton_cons
    (accumulated : Cnf)
    (clause : Clause)
    (tail : Cnf) :
    accumulated ++ (clause :: tail) =
      (accumulated ++ [clause]) ++ tail := by
  induction accumulated with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      change
        head :: (rest ++ (clause :: tail)) =
          head :: ((rest ++ [clause]) ++ tail)
      exact
        congrArg
          (List.cons head)
          inductionHypothesis

/--
Before reassociation, the true residual is the accumulated prefix followed by
one retained negative clause and the remaining stack.
-/
theorem stackedStage_trueResidual_preAssoc
    {count anchor : Nat}
    {accumulated : Cnf}
    (accumulatedAvoidsCurrent :
      Cnf.AvoidsVar count accumulated)
    (countSuccLeAnchor : count + 1 ≤ anchor) :
    branchResidual
        (accumulated ++
          stackedSymmetricBlocks (count + 1) anchor)
        count
        true =
      accumulated ++
        (symmetricNegativeClause count anchor ::
          stackedSymmetricBlocks count anchor) := by
  exact
    calc
      branchResidual
          (accumulated ++
            stackedSymmetricBlocks (count + 1) anchor)
          count
          true =
        branchResidual accumulated count true ++
          branchResidual
            (stackedSymmetricBlocks (count + 1) anchor)
            count
            true :=
        Cnf.branchResidual_append
          accumulated
          (stackedSymmetricBlocks (count + 1) anchor)
          count
          true
      _ =
        accumulated ++
          branchResidual
            (stackedSymmetricBlocks (count + 1) anchor)
            count
            true :=
        congrArg
          (fun left =>
            left ++
              branchResidual
                (stackedSymmetricBlocks (count + 1) anchor)
                count
                true)
          (Cnf.branchResidual_eq_self
            accumulatedAvoidsCurrent
            true)
      _ =
        accumulated ++
          (symmetricNegativeClause count anchor ::
            stackedSymmetricBlocks count anchor) :=
        congrArg
          (fun right => accumulated ++ right)
          (stackedSymmetricBlocks_trueResidual
            countSuccLeAnchor)

/-- Exact next-stage residual in the accumulated-prefix representation. -/
theorem stackedStage_trueResidual
    {count anchor : Nat}
    {accumulated : Cnf}
    (accumulatedSafe :
      PrefixAvoidsBelow (count + 1) accumulated)
    (countSuccLeAnchor : count + 1 ≤ anchor) :
    branchResidual
        (accumulated ++
          stackedSymmetricBlocks (count + 1) anchor)
        count
        true =
      (accumulated ++
        [symmetricNegativeClause count anchor]) ++
          stackedSymmetricBlocks count anchor := by
  have accumulatedAvoidsCurrent :
      Cnf.AvoidsVar count accumulated :=
    accumulatedSafe
      count
      (Nat.lt_succ_self count)
  exact
    Eq.trans
      (stackedStage_trueResidual_preAssoc
        accumulatedAvoidsCurrent
        countSuccLeAnchor)
      (append_singleton_cons
        accumulated
        (symmetricNegativeClause count anchor)
        (stackedSymmetricBlocks count anchor))

namespace PrefixAvoidsBelow

theorem nil
    (count : Nat) :
    PrefixAvoidsBelow count [] := by
  intro _query _queryLt
  exact True.intro

/--
After deciding `count`, append its retained negative clause.  The resulting
accumulated is safe for every smaller future variable.
-/
theorem append_negative
    {count anchor : Nat}
    {accumulated : Cnf}
    (safe :
      PrefixAvoidsBelow (count + 1) accumulated)
    (countLtAnchor : count < anchor) :
    PrefixAvoidsBelow
      count
      (accumulated ++
        [symmetricNegativeClause count anchor]) := by
  intro query queryLtCount
  have queryLtSucc :
      query < count + 1 :=
    Nat.lt_trans
      queryLtCount
      (Nat.lt_succ_self count)
  have accumulatedAvoids :=
    safe query queryLtSucc
  have countDifferentQuery : count ≠ query :=
    (Nat.ne_of_lt queryLtCount).symm
  have queryLtAnchor :
      query < anchor :=
    Nat.lt_trans queryLtCount countLtAnchor
  have anchorDifferentQuery : anchor ≠ query :=
    (Nat.ne_of_lt queryLtAnchor).symm
  have clauseAvoids :
      Clause.AvoidsVar
        query
        (symmetricNegativeClause count anchor) := by
    exact
      ⟨countDifferentQuery,
        ⟨anchorDifferentQuery, True.intro⟩⟩
  exact
    Cnf.avoidsVar_append
      accumulatedAvoids
      ⟨clauseAvoids, True.intro⟩

end PrefixAvoidsBelow

namespace DecisionsAvoidBelow

theorem nil
    (count : Nat) :
    DecisionsAvoidBelow count [] := by
  intro _query _queryLt
  exact True.intro

/--
After deciding `count`, the extended history remains fresh for all smaller
future decision variables.
-/
theorem cons_current
    {count : Nat}
    {decisions : List StructuralBranchDecision}
    (safe :
      DecisionsAvoidBelow
        (count + 1)
        decisions) :
    DecisionsAvoidBelow
      count
      ({ var := count, value := true } ::
        decisions) := by
  intro query queryLtCount
  constructor
  · exact
      (Nat.ne_of_lt queryLtCount).symm
  · exact
      safe
        query
        (Nat.lt_trans
          queryLtCount
          (Nat.lt_succ_self count))

end DecisionsAvoidBelow

/-- Result of constructing an explicit stacked trajectory from one state. -/
structure StackedTrajectoryResult
    {rootFormula : Cnf}
    (start : GeneratedStructuralBranchContext rootFormula)
    (length : Nat) where
  finish : GeneratedStructuralBranchContext rootFormula
  trajectory :
    FlipSymmetricTrajectory start finish length

/--
Construct the complete flip-symmetric path through an explicit stack.

The current formula is tracked as `accumulated ++ stackedSymmetricBlocks count
anchor`.  The weak residual retains one negative clause after every true
decision, and that clause is appended to `accumulated`.
-/
def buildStackedTrajectory
    {rootFormula : Cnf}
    (anchor : Var) :
    (count : Nat) →
      (state : GeneratedStructuralBranchContext rootFormula) →
      (accumulated : Cnf) →
      state.context.formula =
        accumulated ++ stackedSymmetricBlocks count anchor →
      PrefixAvoidsBelow count accumulated →
      DecisionsAvoidBelow count state.context.decisions →
      count ≤ anchor →
      StackedTrajectoryResult state count
  | 0, state, _accumulated, _formulaExact, _accumulatedSafe,
      _decisionsSafe, _countLeAnchor =>
      { finish := state
        trajectory := .done state }
  | count + 1, state, accumulated, formulaExact, accumulatedSafe,
      decisionsSafe, countSuccLeAnchor =>
      let currentVar : Var := count
      have currentLtAnchor : currentVar < anchor :=
        Nat.lt_of_lt_of_le
          (Nat.lt_succ_self count)
          countSuccLeAnchor
      have fresh :
          StructuralDecisionsAvoid
            currentVar
            state.context.decisions :=
        decisionsSafe
          currentVar
          (Nat.lt_succ_self count)
      have explicitSymmetric :
          FlipSymmetricAt
            (accumulated ++
              stackedSymmetricBlocks (count + 1) anchor)
            currentVar :=
        stackedStage_flipSymmetric
          accumulatedSafe
          countSuccLeAnchor
      have stateSymmetric :
          FlipSymmetricAt
            state.context.formula
            currentVar :=
        Eq.mp
          (congrArg
            (fun formula =>
              FlipSymmetricAt formula currentVar)
            formulaExact.symm)
          explicitSymmetric
      let child :=
        GeneratedStructuralBranchContext.child
          state
          currentVar
          true
          fresh
      let nextPrefix : Cnf :=
        accumulated ++
          [symmetricNegativeClause currentVar anchor]
      have childFormulaExact :
          child.context.formula =
            nextPrefix ++
              stackedSymmetricBlocks count anchor := by
        change
          branchResidual
              state.context.formula
              currentVar
              true =
            nextPrefix ++
              stackedSymmetricBlocks count anchor
        unfold nextPrefix
        calc
          branchResidual
              state.context.formula
              currentVar
              true =
            branchResidual
              (accumulated ++
                stackedSymmetricBlocks (count + 1) anchor)
              currentVar
              true :=
            congrArg
              (fun formula =>
                branchResidual formula currentVar true)
              formulaExact
          _ =
            (accumulated ++
              [symmetricNegativeClause currentVar anchor]) ++
                stackedSymmetricBlocks count anchor :=
            stackedStage_trueResidual
              accumulatedSafe
              countSuccLeAnchor
      have nextPrefixSafe :
          PrefixAvoidsBelow count nextPrefix := by
        unfold nextPrefix
        exact
          PrefixAvoidsBelow.append_negative
            accumulatedSafe
            currentLtAnchor
      have nextDecisionsSafe :
          DecisionsAvoidBelow
            count
            child.context.decisions := by
        change
          DecisionsAvoidBelow
            count
            ({ var := currentVar, value := true } ::
              state.context.decisions)
        exact
          DecisionsAvoidBelow.cons_current
            decisionsSafe
      have countLeAnchor : count ≤ anchor :=
        Nat.le_trans
          (Nat.le_succ count)
          countSuccLeAnchor
      let tail :=
        buildStackedTrajectory
          anchor
          count
          child
          nextPrefix
          childFormulaExact
          nextPrefixSafe
          nextDecisionsSafe
          countLeAnchor
      { finish := tail.finish
        trajectory :=
          .step
            currentVar
            fresh
            stateSymmetric
            tail.trajectory }

/-- Canonical root of the closed family. -/
abbrev explicitStackedRoot
    (count : Nat) :
    GeneratedStructuralBranchContext
      (explicitStackedSymmetricFamily count) :=
  GeneratedStructuralBranchContext.root
    (explicitStackedSymmetricFamily count)

/-- Construct the trajectory directly from the closed CNF `F(count)`. -/
def explicitStackedTrajectory
    (count : Nat) :
    StackedTrajectoryResult
      (explicitStackedRoot count)
      count :=
  buildStackedTrajectory
    count
    count
    (explicitStackedRoot count)
    []
    rfl
    (PrefixAvoidsBelow.nil count)
    (DecisionsAvoidBelow.nil count)
    (Nat.le_refl count)

/-- The explicit closed family has a trace of exactly two entries per split plus the final singleton. -/
theorem explicitStackedTrajectory_length
    (count : Nat) :
    (explicitStackedTrajectory count).trajectory.widthTrace.length =
      2 * count + 1 :=
  (explicitStackedTrajectory count).trajectory.widthTrace_length

/-- Uniform width bound for the concrete CNF family `F(n)`. -/
theorem explicitStackedTrajectory_width_le_two
    (count : Nat)
    (width : Nat)
    (member :
      width ∈
        (explicitStackedTrajectory count).trajectory.widthTrace) :
    width ≤ 2 :=
  (explicitStackedTrajectory count).trajectory.width_le_two
    width
    member

/-- End-to-end viability is preserved for the concrete family. -/
theorem explicitStackedTrajectory_viable_iff
    (count : Nat) :
    FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [explicitStackedRoot count] ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [(explicitStackedTrajectory count).finish] :=
  (explicitStackedTrajectory count).trajectory.viable_iff

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Cnf.avoidsVar_append
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_append
#print axioms ConstitutiveSearch.SAT.Cnf.flipAt_append
#print axioms ConstitutiveSearch.SAT.FlipSymmetricAt.prepend_avoiding
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily_trueResidual
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks
#print axioms ConstitutiveSearch.SAT.explicitStackedSymmetricFamily
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_length
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_avoids_of_le
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_trueResidual
#print axioms ConstitutiveSearch.SAT.stackedStage_flipSymmetric
#print axioms ConstitutiveSearch.SAT.append_singleton_cons
#print axioms ConstitutiveSearch.SAT.stackedStage_trueResidual_preAssoc
#print axioms ConstitutiveSearch.SAT.stackedStage_trueResidual
#print axioms ConstitutiveSearch.SAT.PrefixAvoidsBelow
#print axioms ConstitutiveSearch.SAT.DecisionsAvoidBelow
#print axioms ConstitutiveSearch.SAT.StackedTrajectoryResult
#print axioms ConstitutiveSearch.SAT.buildStackedTrajectory
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_length
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_width_le_two
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_viable_iff
/- AXIOM_AUDIT_END -/
