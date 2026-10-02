import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitStackedSymmetricFamily
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralProgress

/-!
# Exact decision resources for the explicit stacked SAT family

The explicit family already constructs a certified flip-symmetric trajectory of
length `n`.  This module equips the same announced strategy with an exact
finite decision resource.

The resource is not the raw list of all literal occurrences.  It is the exact
list of decision variables consumed by the strategy:

  n - 1, ..., 1, 0.

A combined builder constructs both the flip-symmetric trajectory and a
`ResourceGeneratedFrom` witness ending with the empty resource.  Hence width,
depth, and structural terminality are certified on one and the same endpoint.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Exact descending resource consumed by the explicit stacked strategy. -/
def stackedDecisionResource : Nat → List Var
  | 0 => []
  | count + 1 =>
      count :: stackedDecisionResource count

/-- One additional level contributes exactly one resource variable. -/
theorem stackedDecisionResource_succ
    (count : Nat) :
    stackedDecisionResource (count + 1) =
      count :: stackedDecisionResource count :=
  rfl

/-- The decision resource contains exactly one entry per stacked level. -/
theorem stackedDecisionResource_length
    (count : Nat) :
    (stackedDecisionResource count).length =
      count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        Nat.succ
          (stackedDecisionResource count).length =
        Nat.succ count
      exact
        congrArg Nat.succ inductionHypothesis

namespace Cnf

/-- Structural literal count of one CNF. -/
def literalCount : Cnf → Nat
  | [] =>
      0
  | clause :: rest =>
      clause.length + literalCount rest

end Cnf

/-- Positive symmetric clauses contain exactly two literals. -/
theorem symmetricPositiveClause_length
    (var anchor : Var) :
    (symmetricPositiveClause var anchor).length =
      2 := by
  unfold symmetricPositiveClause
  rfl

/-- Negative symmetric clauses contain exactly two literals. -/
theorem symmetricNegativeClause_length
    (var anchor : Var) :
    (symmetricNegativeClause var anchor).length =
      2 := by
  unfold symmetricNegativeClause
  rfl

/-- One symmetric block contributes exactly four literals. -/
theorem symmetricBlockFamily_literalCount
    (var anchor : Var)
    (background : Cnf) :
    Cnf.literalCount
      (symmetricBlockFamily var anchor background) =
        4 + Cnf.literalCount background := by
  have formulaStep :
      symmetricBlockFamily var anchor background =
        symmetricPositiveClause var anchor ::
          symmetricNegativeClause var anchor ::
            background :=
    rfl
  calc
    Cnf.literalCount
        (symmetricBlockFamily var anchor background)
        =
      Cnf.literalCount
        (symmetricPositiveClause var anchor ::
          symmetricNegativeClause var anchor ::
            background) :=
        congrArg Cnf.literalCount formulaStep
    _ =
      (symmetricPositiveClause var anchor).length +
        ((symmetricNegativeClause var anchor).length +
          Cnf.literalCount background) :=
        rfl
    _ =
      2 +
        ((symmetricNegativeClause var anchor).length +
          Cnf.literalCount background) :=
        congrArg
          (fun value =>
            value +
              ((symmetricNegativeClause var anchor).length +
                Cnf.literalCount background))
          (symmetricPositiveClause_length var anchor)
    _ =
      2 + (2 + Cnf.literalCount background) :=
        congrArg
          (Nat.add 2)
          (congrArg
            (fun value =>
              value + Cnf.literalCount background)
            (symmetricNegativeClause_length var anchor))
    _ = (2 + 2) + Cnf.literalCount background :=
        (Nat.add_assoc 2 2 (Cnf.literalCount background)).symm
    _ = 4 + Cnf.literalCount background :=
        rfl

/-- The stacked family has exactly four literals per level. -/
theorem stackedSymmetricBlocks_literalCount
    (count : Nat)
    (anchor : Var) :
    Cnf.literalCount
      (stackedSymmetricBlocks count anchor) =
        4 * count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have stackStep :
          stackedSymmetricBlocks (count + 1) anchor =
            symmetricBlockFamily
              count
              anchor
              (stackedSymmetricBlocks count anchor) :=
        rfl
      calc
        Cnf.literalCount
            (stackedSymmetricBlocks (count + 1) anchor)
            =
          Cnf.literalCount
            (symmetricBlockFamily
              count
              anchor
              (stackedSymmetricBlocks count anchor)) :=
            congrArg Cnf.literalCount stackStep
        _ =
          4 +
            Cnf.literalCount
              (stackedSymmetricBlocks count anchor) :=
            symmetricBlockFamily_literalCount
              count
              anchor
              (stackedSymmetricBlocks count anchor)
        _ = 4 + (4 * count) :=
            congrArg
              (Nat.add 4)
              inductionHypothesis
        _ = 4 * count + 4 :=
            Nat.add_comm 4 (4 * count)
        _ = 4 * (count + 1) :=
            (Nat.mul_succ 4 count).symm

/--
Combined output: one explicit flip-symmetric trajectory and one resource
accounting witness reaching the same final generated SAT context.
-/
structure ResourceAlignedStackedTrajectoryResult
    {rootFormula : Cnf}
    (initial : List Var)
    (start : GeneratedStructuralBranchContext rootFormula)
    (length : Nat) where
  finish : GeneratedStructuralBranchContext rootFormula
  trajectory :
    FlipSymmetricTrajectory start finish length
  generated :
    ResourceGeneratedFrom
      rootFormula
      initial
      []
      finish

/--
Build the explicit stacked trajectory while consuming exactly one decision
resource entry at each level.

The current resource is definitionally `stackedDecisionResource count`.
At a successor step its head is exactly the current decision variable.
-/
def buildResourceAlignedStackedTrajectory
    {rootFormula : Cnf}
    (initial : List Var)
    (anchor : Var) :
    (count : Nat) →
      (state : GeneratedStructuralBranchContext rootFormula) →
      (accumulated : Cnf) →
      state.context.formula =
        accumulated ++ stackedSymmetricBlocks count anchor →
      PrefixAvoidsBelow count accumulated →
      DecisionsAvoidBelow count state.context.decisions →
      count ≤ anchor →
      ResourceGeneratedFrom
        rootFormula
        initial
        (stackedDecisionResource count)
        state →
      ResourceAlignedStackedTrajectoryResult
        initial
        state
        count
  | 0, state, _accumulated, _formulaExact, _accumulatedSafe,
      _decisionsSafe, _countLeAnchor, generated =>
      { finish := state
        trajectory := .done state
        generated := generated }
  | count + 1, state, accumulated, formulaExact, accumulatedSafe,
      decisionsSafe, countSuccLeAnchor, generated =>
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
      let nextAccumulated : Cnf :=
        accumulated ++
          [symmetricNegativeClause currentVar anchor]
      have childFormulaExact :
          child.context.formula =
            nextAccumulated ++
              stackedSymmetricBlocks count anchor := by
        change
          branchResidual
              state.context.formula
              currentVar
              true =
            nextAccumulated ++
              stackedSymmetricBlocks count anchor
        unfold nextAccumulated
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
      have nextAccumulatedSafe :
          PrefixAvoidsBelow count nextAccumulated := by
        unfold nextAccumulated
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
      have consumed :
          ResourceGeneratedFrom
            rootFormula
            initial
            (stackedDecisionResource count)
            child :=
        ResourceGeneratedFrom.child
          generated
          currentVar
          true
          fresh
          (VarRemoval.head
            (stackedDecisionResource count))
      let tail :=
        buildResourceAlignedStackedTrajectory
          initial
          anchor
          count
          child
          nextAccumulated
          childFormulaExact
          nextAccumulatedSafe
          nextDecisionsSafe
          countLeAnchor
          consumed
      { finish := tail.finish
        trajectory :=
          .step
            currentVar
            fresh
            stateSymmetric
            tail.trajectory
        generated := tail.generated }

/-- The exact decision resource for the closed family `F(n)`. -/
def explicitFamilyDecisionResource
    (count : Nat) : List Var :=
  stackedDecisionResource count

/-- The exact decision resource has size `n`. -/
theorem explicitFamilyDecisionResource_length
    (count : Nat) :
    (explicitFamilyDecisionResource count).length =
      count :=
  stackedDecisionResource_length count

/--
Root generation witness with the complete decision resource still available.
-/
def explicitFamilyResourceRoot
    (count : Nat) :
    ResourceGeneratedFrom
      (explicitStackedSymmetricFamily count)
      (explicitFamilyDecisionResource count)
      (explicitFamilyDecisionResource count)
      (explicitStackedRoot count) :=
  .root

/--
Construct one resource-aligned trajectory directly from the closed family.
-/
def explicitFamilyResourceTrajectory
    (count : Nat) :
    ResourceAlignedStackedTrajectoryResult
      (explicitFamilyDecisionResource count)
      (explicitStackedRoot count)
      count :=
  buildResourceAlignedStackedTrajectory
    (explicitFamilyDecisionResource count)
    count
    count
    (explicitStackedRoot count)
    []
    rfl
    (PrefixAvoidsBelow.nil count)
    (DecisionsAvoidBelow.nil count)
    (Nat.le_refl count)
    (explicitFamilyResourceRoot count)

/-- The combined trajectory retains the uniform operational width bound. -/
theorem explicitFamilyResourceTrajectory_width_le_two
    (count width : Nat)
    (member :
      width ∈
        (explicitFamilyResourceTrajectory count).trajectory.widthTrace) :
    width ≤ 2 :=
  (explicitFamilyResourceTrajectory count).trajectory.width_le_two
    width
    member

/-- Resource exhaustion forces exact final generated depth `n`. -/
theorem explicitFamilyEndpoint_depth
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).finish.depth =
      count := by
  have exactDepth :
      (explicitFamilyResourceTrajectory count).finish.depth =
        (explicitFamilyDecisionResource count).length :=
    ResourceGeneratedFrom.depth_eq_initial_of_exhausted
      (explicitFamilyResourceTrajectory count).generated
  exact
    Eq.trans
      exactDepth
      (explicitFamilyDecisionResource_length count)

/-- The same final endpoint is structurally terminal for the exhausted resource. -/
theorem explicitFamilyEndpoint_terminal
    (count : Nat) :
    ResourceTerminal
      (explicitFamilyResourceTrajectory count).finish
      [] :=
  ResourceGeneratedFrom.terminal_of_exhausted
    (explicitFamilyResourceTrajectory count).generated

/-- No further resource-consuming decision exists at the final endpoint. -/
theorem explicitFamilyEndpoint_no_next_decision
    (count : Nat) :
    ResourceDecision
        (explicitFamilyResourceTrajectory count).finish
        [] →
      False :=
  explicitFamilyEndpoint_terminal count

/-- End-to-end viability remains equivalent on the resource-aligned path. -/
theorem explicitFamilyResourceTrajectory_viable_iff
    (count : Nat) :
    FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [explicitStackedRoot count] ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [(explicitFamilyResourceTrajectory count).finish] :=
  (explicitFamilyResourceTrajectory count).trajectory.viable_iff

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.stackedDecisionResource
#print axioms ConstitutiveSearch.SAT.stackedDecisionResource_succ
#print axioms ConstitutiveSearch.SAT.stackedDecisionResource_length
#print axioms ConstitutiveSearch.SAT.Cnf.literalCount
#print axioms ConstitutiveSearch.SAT.symmetricPositiveClause_length
#print axioms ConstitutiveSearch.SAT.symmetricNegativeClause_length
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily_literalCount
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_literalCount
#print axioms ConstitutiveSearch.SAT.ResourceAlignedStackedTrajectoryResult
#print axioms ConstitutiveSearch.SAT.buildResourceAlignedStackedTrajectory
#print axioms ConstitutiveSearch.SAT.explicitFamilyDecisionResource
#print axioms ConstitutiveSearch.SAT.explicitFamilyDecisionResource_length
#print axioms ConstitutiveSearch.SAT.explicitFamilyResourceRoot
#print axioms ConstitutiveSearch.SAT.explicitFamilyResourceTrajectory
#print axioms ConstitutiveSearch.SAT.explicitFamilyResourceTrajectory_width_le_two
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_depth
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_terminal
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_no_next_decision
#print axioms ConstitutiveSearch.SAT.explicitFamilyResourceTrajectory_viable_iff
/- AXIOM_AUDIT_END -/
