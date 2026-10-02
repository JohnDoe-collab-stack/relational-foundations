import RelationalPerimeter.Computation.ConstitutiveSearch.RepresentationCost
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyComplexity

/-!
# Binary representation bounds for the explicit SAT family

This module defines a concrete prefix-tag representation size for SAT syntax and
constituted decision histories.

Encoding convention:
* one tag bit selects literal polarity;
* natural variables use BinaryRepresentation.natBitSize;
* lists use one constructor/terminator tag bit per node.

The resulting budgets are explicit recursive functions.  They are representation
sizes, not machine execution times.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Concrete bit size of one encoded literal. -/
def binarySize : Literal → Nat
  | .positive var =>
      Nat.succ
        (BinaryRepresentation.natBitSize var)
  | .negative var =>
      Nat.succ
        (BinaryRepresentation.natBitSize var)

/-- The literal variable fits below the declared maximum. -/
def VarBoundedBy
    (maximum : Var) : Literal → Prop
  | .positive var =>
      var ≤ maximum
  | .negative var =>
      var ≤ maximum

/-- Coarse bound for one literal under a maximum variable index. -/
theorem binarySize_le_of_varBoundedBy
    {maximum : Var}
    {literal : Literal}
    (bounded :
      VarBoundedBy maximum literal) :
    binarySize literal ≤ maximum + 2 := by
  cases literal with
  | positive var =>
      have bitLe :
          BinaryRepresentation.natBitSize var ≤
            maximum + 1 :=
        Nat.le_trans
          (BinaryRepresentation.natBitSize_le_succ var)
          (Nat.add_le_add_right bounded 1)
      change
        Nat.succ
            (BinaryRepresentation.natBitSize var) ≤
          Nat.succ (maximum + 1)
      exact Nat.succ_le_succ bitLe
  | negative var =>
      have bitLe :
          BinaryRepresentation.natBitSize var ≤
            maximum + 1 :=
        Nat.le_trans
          (BinaryRepresentation.natBitSize_le_succ var)
          (Nat.add_le_add_right bounded 1)
      change
        Nat.succ
            (BinaryRepresentation.natBitSize var) ≤
          Nat.succ (maximum + 1)
      exact Nat.succ_le_succ bitLe

end Literal

namespace Clause

/-- Prefix-tag serialization size of one clause. -/
def binarySize : Clause → Nat
  | [] =>
      1
  | literal :: rest =>
      Nat.succ
        (literal.binarySize +
          binarySize rest)

/-- Every literal variable in the clause is bounded by maximum. -/
def VarsBoundedBy
    (maximum : Var) : Clause → Prop
  | [] =>
      True
  | literal :: rest =>
      literal.VarBoundedBy maximum ∧
        VarsBoundedBy maximum rest

/-- Recursive clause-size budget for a given literal count. -/
def binaryBudget
    (maximum : Var) : Nat → Nat
  | 0 =>
      1
  | count + 1 =>
      Nat.succ
        ((maximum + 2) +
          binaryBudget maximum count)

/-- A bounded clause fits its recursive serialization budget. -/
theorem binarySize_le_budget
    {maximum : Var}
    {clause : Clause}
    (bounded :
      VarsBoundedBy maximum clause) :
    binarySize clause ≤
      binaryBudget maximum clause.length := by
  induction clause with
  | nil =>
      exact Nat.le_refl 1
  | cons literal rest inductionHypothesis =>
      rcases bounded with
        ⟨literalBounded, restBounded⟩
      have literalLe :
          literal.binarySize ≤
            maximum + 2 :=
        Literal.binarySize_le_of_varBoundedBy
          literalBounded
      have restLe :
          binarySize rest ≤
            binaryBudget maximum rest.length :=
        inductionHypothesis restBounded
      exact
        Nat.succ_le_succ
          (Nat.add_le_add
            literalLe
            restLe)

end Clause

namespace Cnf

/-- Prefix-tag serialization size of one complete CNF. -/
def binarySize : Cnf → Nat
  | [] =>
      1
  | clause :: rest =>
      Nat.succ
        (clause.binarySize +
          binarySize rest)

/-- Every variable occurring in the CNF is bounded by maximum. -/
def VarsBoundedBy
    (maximum : Var) : Cnf → Prop
  | [] =>
      True
  | clause :: rest =>
      clause.VarsBoundedBy maximum ∧
        VarsBoundedBy maximum rest

/-- Formula-specific serialization budget under one maximum variable index. -/
def binaryBudget
    (maximum : Var) : Cnf → Nat
  | [] =>
      1
  | clause :: rest =>
      Nat.succ
        (Clause.binaryBudget maximum clause.length +
          binaryBudget maximum rest)

/-- A bounded CNF fits the formula-specific recursive serialization budget. -/
theorem binarySize_le_budget
    {maximum : Var}
    {formula : Cnf}
    (bounded :
      VarsBoundedBy maximum formula) :
    binarySize formula ≤
      binaryBudget maximum formula := by
  induction formula with
  | nil =>
      exact Nat.le_refl 1
  | cons clause rest inductionHypothesis =>
      rcases bounded with
        ⟨clauseBounded, restBounded⟩
      have clauseLe :
          clause.binarySize ≤
            Clause.binaryBudget
              maximum
              clause.length :=
        Clause.binarySize_le_budget
          clauseBounded
      have restLe :
          binarySize rest ≤
            binaryBudget maximum rest :=
        inductionHypothesis restBounded
      exact
        Nat.succ_le_succ
          (Nat.add_le_add
            clauseLe
            restLe)

end Cnf

/-- Every variable in the stacked blocks is at most the common anchor. -/
theorem stackedSymmetricBlocks_varsBoundedBy
    (count anchor : Nat)
    (countLeAnchor : count ≤ anchor) :
    Cnf.VarsBoundedBy
      anchor
      (stackedSymmetricBlocks count anchor) := by
  induction count generalizing anchor with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      have currentLeAnchor :
          count ≤ anchor :=
        Nat.le_trans
          (Nat.le_succ count)
          countLeAnchor
      have tailBounded :
          Cnf.VarsBoundedBy
            anchor
            (stackedSymmetricBlocks count anchor) :=
        inductionHypothesis
          anchor
          currentLeAnchor
      change
        Clause.VarsBoundedBy
            anchor
            (symmetricPositiveClause count anchor) ∧
          (Clause.VarsBoundedBy
              anchor
              (symmetricNegativeClause count anchor) ∧
            Cnf.VarsBoundedBy
              anchor
              (stackedSymmetricBlocks count anchor))
      constructor
      · change
          count ≤ anchor ∧
            (anchor ≤ anchor ∧ True)
        exact
          ⟨currentLeAnchor,
            ⟨Nat.le_refl anchor,
              True.intro⟩⟩
      · constructor
        · change
            count ≤ anchor ∧
              (anchor ≤ anchor ∧ True)
          exact
            ⟨currentLeAnchor,
              ⟨Nat.le_refl anchor,
                True.intro⟩⟩
        · exact tailBounded

/-- All variables in F(n) fit below its anchor n. -/
theorem explicitStackedSymmetricFamily_varsBoundedBy
    (count : Nat) :
    Cnf.VarsBoundedBy
      count
      (explicitStackedSymmetricFamily count) :=
  stackedSymmetricBlocks_varsBoundedBy
    count
    count
    (Nat.le_refl count)

/-- Closed recursive serialization budget for stacked blocks. -/
def stackedSymmetricBinaryBudget
    (anchor : Var) : Nat → Nat
  | 0 =>
      1
  | count + 1 =>
      Nat.succ
        (Clause.binaryBudget anchor 2 +
          Nat.succ
            (Clause.binaryBudget anchor 2 +
              stackedSymmetricBinaryBudget
                anchor
                count))

/-- The formula-specific generic budget reduces to the closed stacked budget. -/
theorem stackedSymmetricBlocks_binaryBudget_eq
    (count anchor : Nat) :
    Cnf.binaryBudget
        anchor
        (stackedSymmetricBlocks count anchor) =
      stackedSymmetricBinaryBudget
        anchor
        count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      unfold stackedSymmetricBlocks
      unfold symmetricBlockFamily
      unfold symmetricPositiveClause
      unfold symmetricNegativeClause
      change
        Nat.succ
            (Clause.binaryBudget anchor 2 +
              Nat.succ
                (Clause.binaryBudget anchor 2 +
                  Cnf.binaryBudget
                    anchor
                    (stackedSymmetricBlocks count anchor))) =
          Nat.succ
            (Clause.binaryBudget anchor 2 +
              Nat.succ
                (Clause.binaryBudget anchor 2 +
                  stackedSymmetricBinaryBudget
                    anchor
                    count))
      exact
        congrArg
          (fun value =>
            Nat.succ
              (Clause.binaryBudget anchor 2 +
                Nat.succ
                  (Clause.binaryBudget anchor 2 +
                    value)))
          inductionHypothesis

/-- Concrete binary-size budget attached to the closed family F(n). -/
def explicitFamilyBinaryBudget
    (count : Nat) : Nat :=
  stackedSymmetricBinaryBudget
    count
    count

/-- The concrete serialization size of F(n) is bounded by its closed budget. -/
theorem explicitFamily_binarySize_le_budget
    (count : Nat) :
    Cnf.binarySize
        (explicitStackedSymmetricFamily count) ≤
      explicitFamilyBinaryBudget count := by
  calc
    Cnf.binarySize
        (explicitStackedSymmetricFamily count)
        ≤
      Cnf.binaryBudget
        count
        (explicitStackedSymmetricFamily count) :=
      Cnf.binarySize_le_budget
        (explicitStackedSymmetricFamily_varsBoundedBy
          count)
    _ =
      explicitFamilyBinaryBudget count :=
      stackedSymmetricBlocks_binaryBudget_eq
        count
        count

namespace StructuralBranchDecision

/-- Concrete binary size of one constituted SAT decision. -/
def binarySize
    (decision : StructuralBranchDecision) : Nat :=
  Nat.succ
    (BinaryRepresentation.natBitSize
      decision.var)

/-- Decision variable fits under the declared maximum. -/
def VarBoundedBy
    (maximum : Var)
    (decision : StructuralBranchDecision) : Prop :=
  decision.var ≤ maximum

/-- Coarse binary-size bound for one decision. -/
theorem binarySize_le_of_varBoundedBy
    {maximum : Var}
    {decision : StructuralBranchDecision}
    (bounded :
      decision.VarBoundedBy maximum) :
    decision.binarySize ≤ maximum + 2 := by
  have bitLe :
      BinaryRepresentation.natBitSize decision.var ≤
        maximum + 1 :=
    Nat.le_trans
      (BinaryRepresentation.natBitSize_le_succ
        decision.var)
      (Nat.add_le_add_right bounded 1)
  change
    Nat.succ
        (BinaryRepresentation.natBitSize decision.var) ≤
      Nat.succ (maximum + 1)
  exact Nat.succ_le_succ bitLe

end StructuralBranchDecision

/-- Every resource variable is bounded by maximum. -/
def VarListBoundedBy
    (maximum : Var) : List Var → Prop
  | [] =>
      True
  | var :: rest =>
      var ≤ maximum ∧
        VarListBoundedBy maximum rest

namespace VarListBoundedBy

theorem mono
    {lower upper : Var}
    (lowerLeUpper : lower ≤ upper) :
    ∀ {vars : List Var},
      VarListBoundedBy lower vars →
        VarListBoundedBy upper vars := by
  intro vars bounded
  induction vars with
  | nil =>
      exact True.intro
  | cons var rest inductionHypothesis =>
      rcases bounded with
        ⟨headLe, tailLe⟩
      exact
        ⟨Nat.le_trans headLe lowerLeUpper,
          inductionHypothesis tailLe⟩

end VarListBoundedBy

/-- Every decision variable in a history is bounded by maximum. -/
def StructuralDecisionsVarsBoundedBy
    (maximum : Var) :
    List StructuralBranchDecision → Prop
  | [] =>
      True
  | decision :: rest =>
      decision.VarBoundedBy maximum ∧
        StructuralDecisionsVarsBoundedBy
          maximum
          rest

namespace StructuralDecisionHistory

/-- Prefix-tag serialization size of one structural decision history. -/
def binarySize :
    List StructuralBranchDecision → Nat
  | [] =>
      1
  | decision :: rest =>
      Nat.succ
        (decision.binarySize +
          binarySize rest)

/-- Recursive history budget from maximum variable and decision count. -/
def binaryBudget
    (maximum : Var) : Nat → Nat
  | 0 =>
      1
  | count + 1 =>
      Nat.succ
        ((maximum + 2) +
          binaryBudget maximum count)

/-- Bounded histories fit the recursive history budget. -/
theorem binarySize_le_budget
    {maximum : Var}
    {decisions : List StructuralBranchDecision}
    (bounded :
      StructuralDecisionsVarsBoundedBy
        maximum
        decisions) :
    binarySize decisions ≤
      binaryBudget maximum decisions.length := by
  induction decisions with
  | nil =>
      exact Nat.le_refl 1
  | cons decision rest inductionHypothesis =>
      rcases bounded with
        ⟨decisionBounded, restBounded⟩
      have decisionLe :
          decision.binarySize ≤
            maximum + 2 :=
        StructuralBranchDecision.binarySize_le_of_varBoundedBy
          decisionBounded
      have restLe :
          binarySize rest ≤
            binaryBudget maximum rest.length :=
        inductionHypothesis restBounded
      exact
        Nat.succ_le_succ
          (Nat.add_le_add
            decisionLe
            restLe)

end StructuralDecisionHistory

namespace VarRemoval

/-- Removing one occurrence preserves a maximum-variable bound. -/
theorem target_bounded
    {maximum var : Var}
    {source target : List Var}
    (removed :
      VarRemoval var source target)
    (sourceBounded :
      VarListBoundedBy maximum source) :
    VarListBoundedBy maximum target := by
  induction removed with
  | head rest =>
      exact sourceBounded.2
  | tail skipped removed inductionHypothesis =>
      exact
        ⟨sourceBounded.1,
          inductionHypothesis sourceBounded.2⟩

/-- The variable consumed by a removal also satisfies the source bound. -/
theorem removed_var_le
    {maximum var : Var}
    {source target : List Var}
    (removed :
      VarRemoval var source target)
    (sourceBounded :
      VarListBoundedBy maximum source) :
    var ≤ maximum := by
  induction removed with
  | head rest =>
      exact sourceBounded.1
  | tail skipped removed inductionHypothesis =>
      exact
        inductionHypothesis sourceBounded.2

end VarRemoval

namespace ResourceGeneratedFrom

/--
Resource-bounded generation preserves both the remaining-resource bound and the
bound on every constituted decision variable.
-/
theorem resource_and_decisions_bounded
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    {maximum : Var}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state)
    (initialBounded :
      VarListBoundedBy maximum initial) :
    VarListBoundedBy maximum remaining ∧
      StructuralDecisionsVarsBoundedBy
        maximum
        state.context.decisions := by
  induction generated with
  | root =>
      exact
        ⟨initialBounded,
          True.intro⟩
  | @child available remaining parent parentGenerated var value fresh removed inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨availableBounded,
          parentDecisionsBounded⟩
      have remainingBounded :
          VarListBoundedBy maximum remaining :=
        removed.target_bounded
          availableBounded
      have varLe :
          var ≤ maximum :=
        removed.removed_var_le
          availableBounded
      exact
        ⟨remainingBounded,
          ⟨varLe,
            parentDecisionsBounded⟩⟩

end ResourceGeneratedFrom

/-- Every variable in the exact decision resource of F(n) is at most n. -/
theorem stackedDecisionResource_bounded
    (count : Nat) :
    VarListBoundedBy
      count
      (stackedDecisionResource count) := by
  induction count with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      exact
        ⟨Nat.le_succ count,
          VarListBoundedBy.mono
            (Nat.le_succ count)
            inductionHypothesis⟩

/-- Every constituted endpoint decision of F(n) uses a variable at most n. -/
theorem explicitFamilyEndpoint_decisions_bounded
    (count : Nat) :
    StructuralDecisionsVarsBoundedBy
      count
      (explicitFamilyResourceTrajectory count).finish.context.decisions := by
  have generatedBounds :=
    ResourceGeneratedFrom.resource_and_decisions_bounded
      (explicitFamilyResourceTrajectory count).generated
      (stackedDecisionResource_bounded count)
  exact generatedBounds.2

/-- Final constituted history of F(n) fits a closed binary budget. -/
theorem explicitFamilyEndpoint_historyBinarySize_le
    (count : Nat) :
    StructuralDecisionHistory.binarySize
        (explicitFamilyResourceTrajectory count).finish.context.decisions ≤
      StructuralDecisionHistory.binaryBudget
        count
        count := by
  calc
    StructuralDecisionHistory.binarySize
        (explicitFamilyResourceTrajectory count).finish.context.decisions
        ≤
      StructuralDecisionHistory.binaryBudget
        count
        (explicitFamilyResourceTrajectory count).finish.context.decisions.length :=
      StructuralDecisionHistory.binarySize_le_budget
        (explicitFamilyEndpoint_decisions_bounded
          count)
    _ =
      StructuralDecisionHistory.binaryBudget
        count
        count :=
      congrArg
        (StructuralDecisionHistory.binaryBudget
          count)
        (explicitFamilyEndpoint_decisions_length
          count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.binarySize
#print axioms ConstitutiveSearch.SAT.Literal.binarySize_le_of_varBoundedBy
#print axioms ConstitutiveSearch.SAT.Clause.binarySize
#print axioms ConstitutiveSearch.SAT.Clause.binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.Cnf.binarySize
#print axioms ConstitutiveSearch.SAT.Cnf.binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_varsBoundedBy
#print axioms ConstitutiveSearch.SAT.explicitStackedSymmetricFamily_varsBoundedBy
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamily_binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.StructuralBranchDecision.binarySize
#print axioms ConstitutiveSearch.SAT.StructuralDecisionHistory.binarySize
#print axioms ConstitutiveSearch.SAT.StructuralDecisionHistory.binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.VarRemoval.target_bounded
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.resource_and_decisions_bounded
#print axioms ConstitutiveSearch.SAT.stackedDecisionResource_bounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_decisions_bounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_historyBinarySize_le
/- AXIOM_AUDIT_END -/
