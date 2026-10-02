import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleProfileSemantics
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy

/-! The operational policy is composed from the actual local output images.
No occurrence-status marker supplies this policy. Its realization reads the
produced continuation values, and its inverse reads those same values. -/
namespace ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput
open Extensive RelationalExtensive

def policy : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    ExecutedRoleReductionHistory program → RolewiseObligationPolicy roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .step license rest =>
      .step (producedRoleOutputRegime license) (policy rest)

def ofStagewise : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (history : StagewiseExecutedDecompositionHistory run) → RolewiseObligationPolicy history.roles
  | _, _, _, .nil => .nil
  | _, _, _, .step head rest => .step head.outputRegime (ofStagewise rest)

theorem ofStagewise_exact : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (history : StagewiseExecutedDecompositionHistory run) →
    ofStagewise history = policy history.reduction
  | _, _, _, .nil => rfl
  | _, _, _, .step head rest => by
      change RolewiseObligationPolicy.step head.outputRegime (ofStagewise rest) =
        RolewiseObligationPolicy.step (producedRoleOutputRegime head.license) (policy rest.reduction)
      rw [head.outputRegimeExact, ofStagewise_exact rest]

def value : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    RolewiseObligation (policy reduction) → ExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil, _ => ()
  | _, _, _, _, _, .step _ rest, q => (q.1.1, value rest q.2)

/-- Image membership uses actual outputs; it contains no convergence equation. -/
def IsProduced : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    ExecutedOperationalTargetProfile reduction → Prop
  | _, _, _, _, _, .nil, _ => True
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ _ _ atom _ _ rest, target =>
      (∃ occurrence, producedRoleOutput atom occurrence = target.1) ∧ IsProduced rest target.2

theorem value_isProduced : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (q : RolewiseObligation (policy reduction)) → IsProduced reduction (value reduction q)
  | _, _, _, _, _, .nil, _ => True.intro
  | _, _, _, _, _, .step _ rest, q => ⟨q.1.2, value_isProduced rest q.2⟩

/-- The inverse copies target components; no source is chosen from an existential. -/
def reify : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) → IsProduced reduction target →
    RolewiseObligation (policy reduction)
  | _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, .step _ rest, target, member =>
      (⟨target.1, member.1⟩, reify rest target.2 member.2)

theorem value_reify : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) → (member : IsProduced reduction target) →
    value reduction (reify reduction target member) = target
  | _, _, _, _, _, .nil, target, _ => by cases target; rfl
  | _, _, _, _, _, .step _ rest, target, member => Prod.ext rfl (value_reify rest target.2 member.2)

theorem reify_value : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (q : RolewiseObligation (policy reduction)) →
    reify reduction (value reduction q) (value_isProduced reduction q) = q
  | _, _, _, _, _, .nil, q => by cases q; rfl
  | _, _, _, _, _, .step _ rest, q => Prod.ext rfl (reify_value rest q.2)

theorem value_injective {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) : Function.Injective (value reduction) := by
  intro left right same
  have mapped := congrArg (fun target : {t // IsProduced reduction t} =>
    reify reduction target.1 target.2)
    (Subtype.ext same :
      (⟨value reduction left, value_isProduced reduction left⟩ : {t // IsProduced reduction t}) =
      ⟨value reduction right, value_isProduced reduction right⟩)
  exact Eq.trans (reify_value reduction left).symm (Eq.trans mapped (reify_value reduction right))

theorem carry_action : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) → (p : RoleOccurrenceProfile roles) →
    value reduction (rolewiseCarry (policy reduction) p) =
      RoleSemantics.actProfile reduction p (canonicalRoleProfilePayload roles p)
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .step _ rest, p => Prod.ext rfl (carry_action rest p.2)

/-- Width follows local output-image convergence, then product composition. -/
theorem width : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} → {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (rolewiseObligationFrontier (policy reduction)).length = 1
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step license rest => by
      change (productFrontier (producedRoleOutputRegime license).frontier
        (rolewiseObligationFrontier (policy rest))).length = 1
      rw [productFrontier_length, producedRoleOutputRegime_width, width rest]

end ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.policy
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.ofStagewise
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.ofStagewise_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.IsProduced
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.value_isProduced
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.reify
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.value_reify
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.reify_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.value_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.carry_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOutput.width
/- AXIOM_AUDIT_END -/
