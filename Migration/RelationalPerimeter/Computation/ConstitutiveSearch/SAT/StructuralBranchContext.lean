import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierPreservation
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.AcceptedBinaryBranch
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.RestrictionTransport

/-!
# Structural recursive SAT branch contexts

This hardened context layer keeps branch provenance in the structural
continuation space and keeps SAT satisfaction exclusively in the acceptance
predicate.

A context state contains only the current residual formula and its decision
history.  A continuation is a total assignment together with a proof that it
realizes that history.  Acceptance states separately that the assignment
satisfies the current residual formula.
-/

namespace ConstitutiveSearch
namespace SAT

/-- One structurally recorded SAT branch decision. -/
structure StructuralBranchDecision where
  var : Var
  value : Bool
  deriving DecidableEq

/-- Every recorded structural decision is realized by one assignment. -/
def StructuralDecisionsHold
    (assignment : Assignment) : List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest =>
      assignment decision.var = decision.value ∧
        StructuralDecisionsHold assignment rest

/-- Hardened SAT branch state: residual syntax plus constituted provenance. -/
structure StructuralBranchContext where
  formula : Cnf
  decisions : List StructuralBranchDecision

/--
A structural continuation is any assignment realizing the constituted
decisions.  No satisfaction proof is stored here.
-/
abbrev StructuralBranchContinuation
    (context : StructuralBranchContext) : Type :=
  { assignment : Assignment //
      StructuralDecisionsHold assignment context.decisions }

/-- SAT acceptance remains separate from structural branch provenance. -/
def StructuralBranchAccept
    (context : StructuralBranchContext)
    (continuation : StructuralBranchContinuation context) : Prop :=
  Satisfies continuation.1 context.formula

/-- Search semantics for recursive structural SAT contexts. -/
abbrev structuralBranchContextSystem : SearchSystem :=
  { State := StructuralBranchContext
    Continuation := StructuralBranchContinuation
    Accept := StructuralBranchAccept }

/-- Initial context before any branch decision. -/
def structuralRootContext
    (formula : Cnf) : StructuralBranchContext :=
  { formula := formula
    decisions := [] }

/--
Child context constituted by one Boolean decision and the corresponding weak
branch residual.
-/
def structuralChildContext
    (parent : StructuralBranchContext)
    (var : Var)
    (value : Bool) : StructuralBranchContext :=
  { formula := branchResidual parent.formula var value
    decisions :=
      { var := var, value := value } :: parent.decisions }

/-- Split a structural continuation according to its actual selected bit. -/
def splitStructuralContextContinuation
    (parent : StructuralBranchContext)
    (var : Var)
    (continuation : StructuralBranchContinuation parent) :
    StructuralBranchContinuation
        (structuralChildContext parent var false) ⊕
      StructuralBranchContinuation
        (structuralChildContext parent var true) :=
  if valueFalse : continuation.1 var = false then
    .inl
      ⟨continuation.1,
        ⟨valueFalse, continuation.2⟩⟩
  else
    .inr
      ⟨continuation.1,
        ⟨bool_true_of_not_false_for_split
            (continuation.1 var)
            valueFalse,
          continuation.2⟩⟩

/-- Forget the newest child decision and recover the parent continuation. -/
def mergeStructuralContextContinuation
    {parent : StructuralBranchContext}
    {var : Var} :
    StructuralBranchContinuation
        (structuralChildContext parent var false) ⊕
      StructuralBranchContinuation
        (structuralChildContext parent var true) →
      StructuralBranchContinuation parent
  | .inl continuation =>
      ⟨continuation.1, continuation.2.2⟩
  | .inr continuation =>
      ⟨continuation.1, continuation.2.2⟩

/-- Merging after splitting reconstructs the parent continuation. -/
theorem merge_split_structural_context
    (parent : StructuralBranchContext)
    (var : Var)
    (continuation : StructuralBranchContinuation parent) :
    mergeStructuralContextContinuation
        (splitStructuralContextContinuation parent var continuation) =
      continuation := by
  by_cases valueFalse : continuation.1 var = false
  · unfold splitStructuralContextContinuation
    rw [dif_pos valueFalse]
    apply Subtype.ext
    rfl
  · unfold splitStructuralContextContinuation
    rw [dif_neg valueFalse]
    apply Subtype.ext
    rfl

/-- Splitting after merging reconstructs the child continuation exactly. -/
theorem split_merge_structural_context
    {parent : StructuralBranchContext}
    {var : Var}
    (branch :
      StructuralBranchContinuation
          (structuralChildContext parent var false) ⊕
        StructuralBranchContinuation
          (structuralChildContext parent var true)) :
    splitStructuralContextContinuation parent var
        (mergeStructuralContextContinuation branch) =
      branch := by
  cases branch with
  | inl leftContinuation =>
      cases leftContinuation with
      | mk assignment decisionsExact =>
          have valueExact : assignment var = false :=
            decisionsExact.1
          change
            splitStructuralContextContinuation parent var
                ⟨assignment, decisionsExact.2⟩ =
              .inl ⟨assignment, decisionsExact⟩
          unfold splitStructuralContextContinuation
          rw [dif_pos valueExact]
  | inr rightContinuation =>
      cases rightContinuation with
      | mk assignment decisionsExact =>
          have valueExact : assignment var = true :=
            decisionsExact.1
          have notFalse : assignment var ≠ false := by
            intro falseExact
            rw [valueExact] at falseExact
            cases falseExact
          change
            splitStructuralContextContinuation parent var
                ⟨assignment, decisionsExact.2⟩ =
              .inr ⟨assignment, decisionsExact⟩
          unfold splitStructuralContextContinuation
          rw [dif_neg notFalse]

/--
A recursive branch split is exact on structural continuations and preserves SAT
acceptance separately in both directions.
-/
def structuralContextSplit
    (parent : StructuralBranchContext)
    (var : Var) :
    AcceptingExactBinarySplit
      structuralBranchContextSystem
      parent
      (structuralChildContext parent var false)
      (structuralChildContext parent var true) :=
  { split := splitStructuralContextContinuation parent var
    merge := mergeStructuralContextContinuation
    splitMerge := split_merge_structural_context
    mergeSplit := merge_split_structural_context parent var
    splitPreservesAccept := by
      intro continuation accepted
      by_cases valueFalse : continuation.1 var = false
      · have residualAccepted :
            Satisfies continuation.1
              (branchResidual parent.formula var false) :=
          (branchWeakening parent.formula var false).preservesSatisfaction
            accepted
        simpa only [
          splitStructuralContextContinuation,
          dif_pos valueFalse,
          BinaryAccept,
          structuralBranchContextSystem,
          StructuralBranchAccept,
          structuralChildContext
        ] using residualAccepted
      · have residualAccepted :
            Satisfies continuation.1
              (branchResidual parent.formula var true) :=
          (branchWeakening parent.formula var true).preservesSatisfaction
            accepted
        simpa only [
          splitStructuralContextContinuation,
          dif_neg valueFalse,
          BinaryAccept,
          structuralBranchContextSystem,
          StructuralBranchAccept,
          structuralChildContext
        ] using residualAccepted
    mergePreservesAccept := by
      intro branch accepted
      cases branch with
      | inl leftContinuation =>
          exact
            restoreSatisfaction
              parent.formula
              leftContinuation.1
              var
              false
              leftContinuation.2.1
              accepted
      | inr rightContinuation =>
          exact
            restoreSatisfaction
              parent.formula
              rightContinuation.1
              var
              true
              rightContinuation.2.1
              accepted }

/-- Exact recursive branch expansion preserves frontier viability. -/
def structuralContextExpansion
    (parent : StructuralBranchContext)
    (var : Var) :
    AcceptedFrontierPreservation
      structuralBranchContextSystem
      [parent]
      [structuralChildContext parent var false,
        structuralChildContext parent var true] :=
  AcceptedFrontierPreservation.expandHead
    (structuralContextSplit parent var)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.StructuralBranchDecision
#print axioms ConstitutiveSearch.SAT.StructuralDecisionsHold
#print axioms ConstitutiveSearch.SAT.StructuralBranchContext
#print axioms ConstitutiveSearch.SAT.StructuralBranchContinuation
#print axioms ConstitutiveSearch.SAT.StructuralBranchAccept
#print axioms ConstitutiveSearch.SAT.structuralBranchContextSystem
#print axioms ConstitutiveSearch.SAT.structuralRootContext
#print axioms ConstitutiveSearch.SAT.structuralChildContext
#print axioms ConstitutiveSearch.SAT.splitStructuralContextContinuation
#print axioms ConstitutiveSearch.SAT.merge_split_structural_context
#print axioms ConstitutiveSearch.SAT.split_merge_structural_context
#print axioms ConstitutiveSearch.SAT.structuralContextSplit
#print axioms ConstitutiveSearch.SAT.structuralContextExpansion
/- AXIOM_AUDIT_END -/
