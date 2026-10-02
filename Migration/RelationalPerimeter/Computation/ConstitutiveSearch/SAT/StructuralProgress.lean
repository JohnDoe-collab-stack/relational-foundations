import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GeneratedStructuralContext

/-!
# Structural progress from a finite SAT variable resource

This module derives a finite progress budget from SAT syntax rather than
imposing an external iteration counter.

The initial resource is the finite list of variable occurrences in the root
CNF. A generated decision may consume any matching occurrence from the
remaining resource; no fixed variable order is imposed.

Each step still carries the existing freshness proof, so resource accounting
does not replace constitutive provenance. It only certifies that every
generated decision consumes finite input structure.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Variable mentioned by one literal. -/
def varOf : Literal → Var
  | .positive var => var
  | .negative var => var

end Literal

namespace Clause

/-- Variable occurrences in one clause, preserving syntax order and duplicates. -/
def variableOccurrences : Clause → List Var
  | [] => []
  | literal :: rest =>
      literal.varOf :: variableOccurrences rest

end Clause

namespace Cnf

/-- Finite variable-occurrence resource carried by a CNF syntax tree. -/
def variableOccurrences : Cnf → List Var
  | [] => []
  | clause :: rest =>
      clause.variableOccurrences ++
        variableOccurrences rest

end Cnf

/--
A structural decision history contains no repeated decision variable.
-/
def StructuralDecisionsDistinct :
    List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest =>
      StructuralDecisionsAvoid decision.var rest ∧
        StructuralDecisionsDistinct rest

namespace StructuralGeneratedFrom

/--
Fresh generation makes the complete constituted decision history pairwise
variable-distinct.
-/
theorem decisionsDistinct
    {rootFormula : Cnf}
    {context : StructuralBranchContext}
    (generated :
      StructuralGeneratedFrom rootFormula context) :
    StructuralDecisionsDistinct context.decisions := by
  induction generated with
  | root =>
      exact True.intro
  | @child parent parentGenerated var value fresh inductionHypothesis =>
      change
        StructuralDecisionsAvoid var parent.decisions ∧
          StructuralDecisionsDistinct parent.decisions
      exact ⟨fresh, inductionHypothesis⟩

end StructuralGeneratedFrom

/--
Proof-relevant removal of one selected variable occurrence from a finite
resource. The selected occurrence may occur anywhere in the list.
-/
inductive VarRemoval
    (var : Var) :
    List Var → List Var → Type where
  | head
      (rest : List Var) :
      VarRemoval var (var :: rest) rest
  | tail
      {head : Var}
      {source target : List Var}
      (different : head ≠ var)
      (removed : VarRemoval var source target) :
      VarRemoval var
        (head :: source)
        (head :: target)

namespace VarRemoval

/-- Removing one occurrence decreases resource length by exactly one. -/
theorem length_eq
    {var : Var}
    {source target : List Var}
    (removed : VarRemoval var source target) :
    source.length = target.length + 1 := by
  induction removed with
  | head rest =>
      rfl
  | tail different removed inductionHypothesis =>
      simp only [List.length_cons]
      rw [inductionHypothesis]

/-- Executable search for one removable occurrence. -/
def find
    (var : Var) :
    (source : List Var) →
      Option
        (Sigma fun target =>
          VarRemoval var source target)
  | [] => none
  | current :: rest =>
      if same : current = var then
        by
          cases same
          exact some ⟨rest, .head rest⟩
      else
        match find var rest with
        | none => none
        | some ⟨remaining, removed⟩ =>
            some
              ⟨current :: remaining,
                .tail same removed⟩

end VarRemoval

/--
One legal resource-consuming decision from a generated structural state.

This object contains no acceptance information. It records only a fresh
constitutive decision together with the finite syntax resource occurrence it
consumes.
-/
structure ResourceDecision
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (available : List Var) where
  var : Var
  value : Bool
  remaining : List Var
  fresh :
    StructuralDecisionsAvoid
      var
      state.context.decisions
  removed :
    VarRemoval var available remaining

/--
A resource-accounted state is terminal when no further fresh consuming
decision can be constructed.
-/
def ResourceTerminal
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (available : List Var) : Prop :=
  ResourceDecision state available → False

namespace VarRemoval

/-- No variable occurrence can be removed from an exhausted resource. -/
theorem impossible_from_empty
    {var : Var}
    {target : List Var}
    (removed : VarRemoval var [] target) :
    False := by
  cases removed

end VarRemoval

namespace ResourceTerminal

/-- Exhausting the finite resource is always structurally terminal. -/
theorem exhausted
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    ResourceTerminal state [] := by
  intro decision
  exact decision.removed.impossible_from_empty

/--
If the head resource variable is still fresh, a legal consuming decision
exists. Hence such a state is not terminal.
-/
theorem not_of_fresh_head
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {var : Var}
    {rest : List Var}
    (fresh :
      StructuralDecisionsAvoid
        var
        state.context.decisions) :
    ¬ ResourceTerminal state (var :: rest) := by
  intro terminal
  exact terminal
    { var := var
      value := false
      remaining := rest
      fresh := fresh
      removed := .head rest }

/--
Exact characterization of resource terminality: every removable occurrence is
blocked precisely because its variable is no longer fresh in the constituted
history.
-/
theorem iff_no_fresh_removal
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {available : List Var} :
    ResourceTerminal state available ↔
      ∀ (var : Var) (remaining : List Var),
        VarRemoval var available remaining →
          ¬ StructuralDecisionsAvoid
              var
              state.context.decisions := by
  constructor
  · intro terminal var remaining removed fresh
    exact terminal
      { var := var
        value := false
        remaining := remaining
        fresh := fresh
        removed := removed }
  · intro noFresh decision
    exact
      noFresh
        decision.var
        decision.remaining
        decision.removed
        decision.fresh

end ResourceTerminal

/--
Generated SAT provenance augmented with a finite resource account.

The initial resource is fixed for the complete history. Each child consumes one
selected occurrence from the currently remaining resource and still requires
the ordinary freshness proof of GeneratedStructuralBranchContext.
-/
inductive ResourceGeneratedFrom
    (rootFormula : Cnf)
    (initial : List Var) :
    List Var →
      GeneratedStructuralBranchContext rootFormula →
        Type where
  | root :
      ResourceGeneratedFrom
        rootFormula
        initial
        initial
        (GeneratedStructuralBranchContext.root rootFormula)
  | child
      {available remaining : List Var}
      {parent : GeneratedStructuralBranchContext rootFormula}
      (parentGenerated :
        ResourceGeneratedFrom
          rootFormula
          initial
          available
          parent)
      (var : Var)
      (value : Bool)
      (fresh :
        StructuralDecisionsAvoid
          var
          parent.context.decisions)
      (removed :
        VarRemoval var available remaining) :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        (GeneratedStructuralBranchContext.child
          parent
          var
          value
          fresh)

namespace ResourceGeneratedFrom

/--
Exact finite-resource invariant: constituted depth plus remaining resource
equals the initial resource length.
-/
theorem budget_exact
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    state.depth + remaining.length =
      initial.length := by
  induction generated with
  | root =>
      exact Nat.zero_add _
  | @child available remaining parent parentGenerated var value fresh removed inductionHypothesis =>
      exact
        Eq.trans
          (Nat.add_assoc
            parent.depth
            1
            remaining.length)
          (Eq.trans
            (congrArg
              (Nat.add parent.depth)
              (Nat.add_comm 1 remaining.length))
            (Eq.trans
              (congrArg
                (Nat.add parent.depth)
                removed.length_eq.symm)
              inductionHypothesis))

/-- Constructive depth-bound certificate with remaining resource as slack. -/
theorem depth_bound_certificate
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    ∃ slack : Nat,
      state.depth + slack = initial.length :=
  ⟨remaining.length, generated.budget_exact⟩

/-- Numeric consequence of the exact resource invariant. -/
theorem depth_le_initial
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    state.depth ≤ initial.length := by
  rw [← generated.budget_exact]
  exact Nat.le_add_right _ _

/-- Exhausted resource generation is structurally terminal. -/
theorem terminal_of_exhausted
    {rootFormula : Cnf}
    {initial : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (_generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        []
        state) :
    ResourceTerminal state [] :=
  ResourceTerminal.exhausted state

/--
When the resource is exhausted, the exact budget invariant leaves no slack:
constituted depth equals the initial finite resource length.
-/
theorem depth_eq_initial_of_exhausted
    {rootFormula : Cnf}
    {initial : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        []
        state) :
    state.depth = initial.length := by
  simpa using generated.budget_exact

end ResourceGeneratedFrom

/-- Resource-accounted generation using the root CNF's own syntax occurrences. -/
abbrev FormulaResourceGeneratedFrom
    (rootFormula : Cnf)
    (remaining : List Var)
    (state : GeneratedStructuralBranchContext rootFormula) :=
  ResourceGeneratedFrom
    rootFormula
    rootFormula.variableOccurrences
    remaining
    state

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.varOf
#print axioms ConstitutiveSearch.SAT.Clause.variableOccurrences
#print axioms ConstitutiveSearch.SAT.Cnf.variableOccurrences
#print axioms ConstitutiveSearch.SAT.StructuralDecisionsDistinct
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom.decisionsDistinct
#print axioms ConstitutiveSearch.SAT.VarRemoval
#print axioms ConstitutiveSearch.SAT.VarRemoval.length_eq
#print axioms ConstitutiveSearch.SAT.VarRemoval.find
#print axioms ConstitutiveSearch.SAT.VarRemoval.impossible_from_empty
#print axioms ConstitutiveSearch.SAT.ResourceDecision
#print axioms ConstitutiveSearch.SAT.ResourceTerminal
#print axioms ConstitutiveSearch.SAT.ResourceTerminal.exhausted
#print axioms ConstitutiveSearch.SAT.ResourceTerminal.not_of_fresh_head
#print axioms ConstitutiveSearch.SAT.ResourceTerminal.iff_no_fresh_removal
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.budget_exact
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.depth_bound_certificate
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.depth_le_initial
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.terminal_of_exhausted
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.depth_eq_initial_of_exhausted
#print axioms ConstitutiveSearch.SAT.FormulaResourceGeneratedFrom
/- AXIOM_AUDIT_END -/
