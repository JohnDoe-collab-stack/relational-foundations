import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyCosts

/-!
# Provenance size for the explicit stacked SAT family

Provenance size is measured extensionally by the constituted decision history,
not by the implementation size of a Lean proof term.

For every generated structural SAT state, the history length equals generation
depth.  The explicit family therefore reaches an endpoint with provenance size
exactly n.
-/

namespace ConstitutiveSearch
namespace SAT

namespace StructuralGeneratedFrom

/-- Every generation step contributes exactly one recorded decision. -/
theorem decisions_length_eq_depth
    {rootFormula : Cnf}
    {context : StructuralBranchContext}
    (generated :
      StructuralGeneratedFrom rootFormula context) :
    context.decisions.length =
      generated.depth := by
  induction generated with
  | root =>
      rfl
  | @child parent parentGenerated var value fresh inductionHypothesis =>
      change
        ({ var := var, value := value } ::
          parent.decisions).length =
        parentGenerated.depth + 1
      calc
        ({ var := var, value := value } ::
          parent.decisions).length
            =
          Nat.succ parent.decisions.length :=
            rfl
        _ =
          Nat.succ parentGenerated.depth :=
            congrArg Nat.succ inductionHypothesis
        _ =
          parentGenerated.depth + 1 :=
            Nat.succ_eq_add_one parentGenerated.depth

end StructuralGeneratedFrom

namespace GeneratedStructuralBranchContext

/-- Extensional provenance size: number of constituted branch decisions. -/
def provenanceSize
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    Nat :=
  state.context.decisions.length

/-- Provenance size agrees exactly with generated depth. -/
theorem provenanceSize_eq_depth
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    state.provenanceSize =
      state.depth :=
  state.generated.decisions_length_eq_depth

/-- Root provenance is empty. -/
theorem root_provenanceSize
    (formula : Cnf) :
    (root formula).provenanceSize = 0 := by
  rfl

/-- One generated child adds exactly one unit of provenance. -/
theorem child_provenanceSize
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions) :
    (child parent var value fresh).provenanceSize =
      parent.provenanceSize + 1 := by
  calc
    (child parent var value fresh).provenanceSize
        =
      (child parent var value fresh).depth :=
        provenanceSize_eq_depth
          (child parent var value fresh)
    _ =
      parent.depth + 1 :=
        child_depth parent var value fresh
    _ =
      parent.provenanceSize + 1 :=
        congrArg
          (fun depth => depth + 1)
          (provenanceSize_eq_depth parent).symm

end GeneratedStructuralBranchContext

namespace FlipSymmetricTrajectory

/-- A flip-symmetric trajectory adds exactly its length to provenance depth. -/
theorem finish_provenanceSize_eq
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    finish.provenanceSize =
      start.provenanceSize + length := by
  induction trajectory with
  | done state =>
      exact
        (Nat.add_zero state.provenanceSize).symm
  | @step parent finish length var fresh symmetric tail inductionHypothesis =>
      have childSize :
          (GeneratedStructuralBranchContext.child
            parent var true fresh).provenanceSize =
          parent.provenanceSize + 1 :=
        GeneratedStructuralBranchContext.child_provenanceSize
          parent var true fresh
      calc
        finish.provenanceSize
            =
          (GeneratedStructuralBranchContext.child
            parent var true fresh).provenanceSize +
              length :=
            inductionHypothesis
        _ =
          (parent.provenanceSize + 1) + length :=
            congrArg
              (fun value => value + length)
              childSize
        _ =
          parent.provenanceSize + (1 + length) :=
            Nat.add_assoc parent.provenanceSize 1 length
        _ =
          parent.provenanceSize + (length + 1) :=
            congrArg
              (Nat.add parent.provenanceSize)
              (Nat.add_comm 1 length)

end FlipSymmetricTrajectory

/-- The explicit resource-aligned endpoint carries exactly n decisions. -/
theorem explicitFamilyEndpoint_provenanceSize
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).finish.provenanceSize =
      count := by
  calc
    (explicitFamilyResourceTrajectory count).finish.provenanceSize
        =
      (explicitFamilyResourceTrajectory count).finish.depth :=
        GeneratedStructuralBranchContext.provenanceSize_eq_depth
          (explicitFamilyResourceTrajectory count).finish
    _ = count :=
        explicitFamilyEndpoint_depth count

/-- Equivalent statement directly on the stored decision list. -/
theorem explicitFamilyEndpoint_decisions_length
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).finish.context.decisions.length =
      count := by
  exact explicitFamilyEndpoint_provenanceSize count

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom.decisions_length_eq_depth
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.provenanceSize
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.provenanceSize_eq_depth
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.root_provenanceSize
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralBranchContext.child_provenanceSize
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.finish_provenanceSize_eq
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_provenanceSize
#print axioms ConstitutiveSearch.SAT.explicitFamilyEndpoint_decisions_length
/- AXIOM_AUDIT_END -/
