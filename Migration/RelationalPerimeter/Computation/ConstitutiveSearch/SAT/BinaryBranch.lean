import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ConstraintTransport
import ExactTypeTransport

/-!
# Exact SAT branching by one Boolean variable

This module isolates the OR step of SAT self-reduction from every later CNF
simplification.

A raw satisfying assignment is first reindexed by the Boolean value it gives to
the selected variable. That indexing is exact and reversible. The indexed
parent completion space then decomposes definitionally into a false branch and
a true branch.

No satisfiability query is performed. The only inspected datum is the value of
the selected variable inside an already supplied satisfying assignment.
-/

namespace ConstitutiveSearch
namespace SAT

/-- A completion indexed by the actual Boolean value assigned to one variable. -/
inductive ValueIndexedCompletion
    (formula : Cnf)
    (var : Var) : Bool → Type
  | ofCompletion
      (completion : Completion formula) :
      ValueIndexedCompletion formula var (completion.1 var)

namespace ValueIndexedCompletion

/-- Forget the value index and recover the underlying SAT completion. -/
def underlying
    {formula : Cnf}
    {var : Var}
    {value : Bool} :
    ValueIndexedCompletion formula var value → Completion formula
  | .ofCompletion completion => completion

end ValueIndexedCompletion

/-- Three structural views of one CNF at one branching variable. -/
inductive VariableBranchState where
  | parent : Cnf → Var → VariableBranchState
  | fixedFalse : Cnf → Var → VariableBranchState
  | fixedTrue : Cnf → Var → VariableBranchState

/--
The parent view stores the Boolean value together with a completion indexed by
that value. The child views select one of the two Boolean indices.
-/
def VariableBranchCompletion : VariableBranchState → Type
  | .parent formula var =>
      Sigma (ValueIndexedCompletion formula var)
  | .fixedFalse formula var =>
      ValueIndexedCompletion formula var false
  | .fixedTrue formula var =>
      ValueIndexedCompletion formula var true

/-- Exact reversible indexing of raw SAT completions by one selected bit. -/
def parentIndexing
    (formula : Cnf)
    (var : Var) :
    RelationalFoundations.ExactTransport
      (Completion formula)
      (VariableBranchCompletion (.parent formula var)) :=
  { forward := fun completion =>
      ⟨completion.1 var, .ofCompletion completion⟩
    backward := fun indexed =>
      match indexed with
      | ⟨_, .ofCompletion completion⟩ => completion
    forwardBackward := by
      intro completion
      rfl
    backwardForward := by
      intro indexed
      cases indexed with
      | mk value indexedCompletion =>
          cases indexedCompletion with
          | ofCompletion completion =>
              rfl }

/-- Exact constructive split of the indexed parent by one variable value. -/
def variableBranchSplit
    (formula : Cnf)
    (var : Var) :
    ExactBinarySplit
      VariableBranchCompletion
      (.parent formula var)
      (.fixedFalse formula var)
      (.fixedTrue formula var) :=
  { split := fun indexed =>
      match indexed with
      | ⟨false, completion⟩ => .inl completion
      | ⟨true, completion⟩ => .inr completion
    merge := fun branch =>
      match branch with
      | .inl completion => ⟨false, completion⟩
      | .inr completion => ⟨true, completion⟩
    splitMerge := by
      intro branch
      cases branch <;> rfl
    mergeSplit := by
      intro indexed
      cases indexed with
      | mk value completion =>
          cases value <;> rfl }

/-- Direct split of one raw SAT completion through the exact parent indexing. -/
def splitCompletion
    (formula : Cnf)
    (var : Var)
    (completion : Completion formula) :
    VariableBranchCompletion (.fixedFalse formula var) ⊕
      VariableBranchCompletion (.fixedTrue formula var) :=
  (variableBranchSplit formula var).split
    ((parentIndexing formula var).forward completion)

/-- Forget a branch tag and recover the corresponding raw SAT completion. -/
def mergeCompletion
    (formula : Cnf)
    (var : Var)
    (branch :
      VariableBranchCompletion (.fixedFalse formula var) ⊕
        VariableBranchCompletion (.fixedTrue formula var)) :
    Completion formula :=
  (parentIndexing formula var).backward
    ((variableBranchSplit formula var).merge branch)

/-- Splitting and then forgetting the branch reconstructs the original completion. -/
theorem merge_split_completion
    (formula : Cnf)
    (var : Var)
    (completion : Completion formula) :
    mergeCompletion formula var
        (splitCompletion formula var completion) =
      completion := by
  change
    (parentIndexing formula var).backward
        ((variableBranchSplit formula var).merge
          ((variableBranchSplit formula var).split
            ((parentIndexing formula var).forward completion))) =
      completion
  rw [(variableBranchSplit formula var).mergeSplit]
  exact (parentIndexing formula var).forwardBackward completion

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ValueIndexedCompletion
#print axioms ConstitutiveSearch.SAT.ValueIndexedCompletion.underlying
#print axioms ConstitutiveSearch.SAT.VariableBranchState
#print axioms ConstitutiveSearch.SAT.VariableBranchCompletion
#print axioms ConstitutiveSearch.SAT.parentIndexing
#print axioms ConstitutiveSearch.SAT.variableBranchSplit
#print axioms ConstitutiveSearch.SAT.splitCompletion
#print axioms ConstitutiveSearch.SAT.merge_split_completion
/- AXIOM_AUDIT_END -/