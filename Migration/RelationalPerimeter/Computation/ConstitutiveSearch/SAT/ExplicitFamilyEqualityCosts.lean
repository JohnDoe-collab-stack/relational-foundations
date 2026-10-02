import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyBitCosts

/-!
# Binary equality charges for structural flip search

The executable global flip search checks two structural equalities:
* target formula against the flipped source formula;
* target decision history against the flipped source history.

This module assigns a transparent representation charge equal to the sum of the
binary sizes of both operands of both equalities.

This charge is a concrete representation-level comparison budget. It does not
claim that Lean's internal DecidableEq implementation takes exactly this many
machine steps.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Polarity flip preserves encoded literal size exactly. -/
theorem flipAt_binarySize
    (var : Var)
    (literal : Literal) :
    binarySize (flipAt var literal) =
      binarySize literal := by
  cases literal with
  | positive query =>
      by_cases same : query = var
      · have flipped :
            Literal.flipAt var (.positive query) =
              .negative query := by
          rw [Literal.flipAt, if_pos same]
        rw [flipped]
        rfl
      · have flipped :
            Literal.flipAt var (.positive query) =
              .positive query := by
          rw [Literal.flipAt, if_neg same]
        rw [flipped]
  | negative query =>
      by_cases same : query = var
      · have flipped :
            Literal.flipAt var (.negative query) =
              .positive query := by
          rw [Literal.flipAt, if_pos same]
        rw [flipped]
        rfl
      · have flipped :
            Literal.flipAt var (.negative query) =
              .negative query := by
          rw [Literal.flipAt, if_neg same]
        rw [flipped]

end Literal

namespace Clause

/-- Polarity flip preserves encoded clause size exactly. -/
theorem flipAt_binarySize
    (var : Var) :
    ∀ clause : Clause,
      binarySize (flipAt var clause) =
        binarySize clause
  | [] =>
      rfl
  | literal :: rest => by
      change
        Nat.succ
            (Literal.binarySize
                (Literal.flipAt var literal) +
              binarySize
                (flipAt var rest)) =
          Nat.succ
            (Literal.binarySize literal +
              binarySize rest)
      calc
        Nat.succ
            (Literal.binarySize
                (Literal.flipAt var literal) +
              binarySize
                (flipAt var rest))
            =
          Nat.succ
            (Literal.binarySize literal +
              binarySize
                (flipAt var rest)) :=
          congrArg Nat.succ
            (congrArg
              (fun value =>
                value +
                  binarySize
                    (flipAt var rest))
              (Literal.flipAt_binarySize
                var literal))
        _ =
          Nat.succ
            (Literal.binarySize literal +
              binarySize rest) :=
          congrArg Nat.succ
            (congrArg
              (Nat.add
                (Literal.binarySize literal))
              (flipAt_binarySize var rest))

end Clause

namespace Cnf

/-- Polarity flip preserves encoded CNF size exactly. -/
theorem flipAt_binarySize
    (var : Var) :
    ∀ formula : Cnf,
      binarySize (flipAt var formula) =
        binarySize formula
  | [] =>
      rfl
  | clause :: rest => by
      change
        Nat.succ
            (Clause.binarySize
                (Clause.flipAt var clause) +
              binarySize
                (flipAt var rest)) =
          Nat.succ
            (Clause.binarySize clause +
              binarySize rest)
      calc
        Nat.succ
            (Clause.binarySize
                (Clause.flipAt var clause) +
              binarySize
                (flipAt var rest))
            =
          Nat.succ
            (Clause.binarySize clause +
              binarySize
                (flipAt var rest)) :=
          congrArg Nat.succ
            (congrArg
              (fun value =>
                value +
                  binarySize
                    (flipAt var rest))
              (Clause.flipAt_binarySize
                var clause))
        _ =
          Nat.succ
            (Clause.binarySize clause +
              binarySize rest) :=
          congrArg Nat.succ
            (congrArg
              (Nat.add
                (Clause.binarySize clause))
              (flipAt_binarySize var rest))

/-- Weak branch residual never increases the concrete CNF binary size. -/
theorem branchResidual_binarySize_le
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    binarySize
        (branchResidual formula var value) ≤
      binarySize formula := by
  induction formula with
  | nil =>
      exact Nat.le_refl 1
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
            Nat.succ
                (Clause.binarySize clause +
                  binarySize
                    (branchResidual rest var value)) ≤
              Nat.succ
                (Clause.binarySize clause +
                  binarySize rest)
          exact
            Nat.succ_le_succ
              (Nat.add_le_add_left
                inductionHypothesis
                (Clause.binarySize clause))
      | true =>
          rw [
            branchResidual_cons_hit
              clause rest var value hit
          ]
          change
            binarySize
                (branchResidual rest var value) ≤
              Nat.succ
                (Clause.binarySize clause +
                  binarySize rest)
          exact
            Nat.le_trans
              inductionHypothesis
              (Nat.le_trans
                (Nat.le_add_left
                  (binarySize rest)
                  (Clause.binarySize clause))
                (Nat.le_succ
                  (Clause.binarySize clause +
                    binarySize rest)))

end Cnf

namespace StructuralBranchDecision

/-- Flipping only a Boolean decision value preserves its encoded size. -/
theorem flipAt_binarySize
    (var : Var)
    (decision : StructuralBranchDecision) :
    binarySize (flipAt var decision) =
      binarySize decision := by
  unfold flipAt
  by_cases same : decision.var = var
  · rw [if_pos same]
    rfl
  · rw [if_neg same]

end StructuralBranchDecision

namespace StructuralDecisionHistory

/-- Flipping a selected variable throughout history preserves encoded size. -/
theorem flipAt_binarySize
    (var : Var) :
    ∀ decisions : List StructuralBranchDecision,
      binarySize
          (flipStructuralDecisionsAt
            var decisions) =
        binarySize decisions
  | [] =>
      rfl
  | decision :: rest => by
      change
        Nat.succ
            (StructuralBranchDecision.binarySize
                (StructuralBranchDecision.flipAt
                  var decision) +
              binarySize
                (flipStructuralDecisionsAt
                  var rest)) =
          Nat.succ
            (StructuralBranchDecision.binarySize
                decision +
              binarySize rest)
      calc
        Nat.succ
            (StructuralBranchDecision.binarySize
                (StructuralBranchDecision.flipAt
                  var decision) +
              binarySize
                (flipStructuralDecisionsAt
                  var rest))
            =
          Nat.succ
            (StructuralBranchDecision.binarySize
                decision +
              binarySize
                (flipStructuralDecisionsAt
                  var rest)) :=
          congrArg Nat.succ
            (congrArg
              (fun value =>
                value +
                  binarySize
                    (flipStructuralDecisionsAt
                      var rest))
              (StructuralBranchDecision.flipAt_binarySize
                var decision))
        _ =
          Nat.succ
            (StructuralBranchDecision.binarySize
                decision +
              binarySize rest) :=
          congrArg Nat.succ
            (congrArg
              (Nat.add
                (StructuralBranchDecision.binarySize
                  decision))
              (flipAt_binarySize var rest))

end StructuralDecisionHistory

/--
Representation charge of the two equality tests used by one structural global
flip search.
-/
def generatedFlipEqualityCharge
    {rootFormula : Cnf}
    (var : Var)
    (source target :
      GeneratedStructuralBranchContext rootFormula) :
    Nat :=
  Cnf.binarySize target.context.formula +
    Cnf.binarySize
      (Cnf.flipAt
        var
        source.context.formula) +
    (StructuralDecisionHistory.binarySize
        target.context.decisions +
      StructuralDecisionHistory.binarySize
        (flipStructuralDecisionsAt
          var
          source.context.decisions))

/-- Flipping the source does not change the representation charge. -/
theorem generatedFlipEqualityCharge_eq
    {rootFormula : Cnf}
    (var : Var)
    (source target :
      GeneratedStructuralBranchContext rootFormula) :
    generatedFlipEqualityCharge
        var source target =
      Cnf.binarySize target.context.formula +
        Cnf.binarySize source.context.formula +
        (StructuralDecisionHistory.binarySize
            target.context.decisions +
          StructuralDecisionHistory.binarySize
            source.context.decisions) := by
  unfold generatedFlipEqualityCharge
  rw [Cnf.flipAt_binarySize]
  rw [StructuralDecisionHistory.flipAt_binarySize]

/-- Uniform comparison charge from formula and history bounds. -/
def uniformGeneratedFlipEqualityCharge
    (formulaBound historyBound : Nat) :
    Nat :=
  formulaBound +
    formulaBound +
    (historyBound + historyBound)

/-- One flip equality charge is bounded by uniform representation envelopes. -/
theorem generatedFlipEqualityCharge_le
    {rootFormula : Cnf}
    (var : Var)
    (source target :
      GeneratedStructuralBranchContext rootFormula)
    (formulaBound historyBound : Nat)
    (sourceFormulaLe :
      Cnf.binarySize
          source.context.formula ≤
        formulaBound)
    (targetFormulaLe :
      Cnf.binarySize
          target.context.formula ≤
        formulaBound)
    (sourceHistoryLe :
      StructuralDecisionHistory.binarySize
          source.context.decisions ≤
        historyBound)
    (targetHistoryLe :
      StructuralDecisionHistory.binarySize
          target.context.decisions ≤
        historyBound) :
    generatedFlipEqualityCharge
        var source target ≤
      uniformGeneratedFlipEqualityCharge
        formulaBound
        historyBound := by
  rw [generatedFlipEqualityCharge_eq]
  unfold uniformGeneratedFlipEqualityCharge
  exact
    Nat.add_le_add
      (Nat.add_le_add
        targetFormulaLe
        sourceFormulaLe)
      (Nat.add_le_add
        targetHistoryLe
        sourceHistoryLe)

/--
Binary representation budget used for one relation-search call on F(n).

The history bound uses the final trajectory depth n as a uniform envelope for
all shorter intermediate histories.
-/
def explicitFamilyRelationEqualityChargeBudget
    (count : Nat) : Nat :=
  uniformGeneratedFlipEqualityCharge
    (explicitFamilyBinaryBudget count)
    (StructuralDecisionHistory.binaryBudget
      count
      count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.flipAt_binarySize
#print axioms ConstitutiveSearch.SAT.Clause.flipAt_binarySize
#print axioms ConstitutiveSearch.SAT.Cnf.flipAt_binarySize
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_binarySize_le
#print axioms ConstitutiveSearch.SAT.StructuralBranchDecision.flipAt_binarySize
#print axioms ConstitutiveSearch.SAT.StructuralDecisionHistory.flipAt_binarySize
#print axioms ConstitutiveSearch.SAT.generatedFlipEqualityCharge
#print axioms ConstitutiveSearch.SAT.generatedFlipEqualityCharge_eq
#print axioms ConstitutiveSearch.SAT.uniformGeneratedFlipEqualityCharge
#print axioms ConstitutiveSearch.SAT.generatedFlipEqualityCharge_le
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationEqualityChargeBudget
/- AXIOM_AUDIT_END -/
