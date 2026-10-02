import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationRegime
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalRoleExtensiveFamily

/-!
# Local obligation policies induced over a relational role history

Each role receives its own surjective local obligation regime.  Their dependent
product induces a global regime on the already constituted occurrence profiles.
Because every binary role has a positively constructed occurrence, global
injectivity is equivalent to injectivity at every local stage.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive
open RelationalExtensive

/-- Finite local carrier of the two identities constituted by one role. -/
def roleOpeningFiniteCarrier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) : FiniteCarrier :=
  { Identity := RoleConstitutedOccurrence role
    decEq := relationallyConstitutedOccurrenceDecEq
      (generalOpeningStageOfRole role)
    frontier := relationallyConstitutedOccurrenceFrontier
      (generalOpeningStageOfRole role)
    complete := relationallyConstitutedOccurrenceFrontier_complete
      (generalOpeningStageOfRole role)
    nodup := relationallyConstitutedOccurrenceFrontier_nodup
      (generalOpeningStageOfRole role) }

/-- One local obligation regime for every role in the dependent history. -/
inductive RolewiseObligationPolicy :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      RolewiseObligationPolicy
        (RelationalConstitutiveRoleHistory.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      (headRegime : ObligationRegime (roleOpeningFiniteCarrier headRole))
      (tailPolicy : RolewiseObligationPolicy tailRoles) :
      RolewiseObligationPolicy
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)

/-- Global obligation type induced by the local policy. -/
def RolewiseObligation :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      RolewiseObligationPolicy roles → Type
  | _, _, _, _, .nil => Unit
  | _, _, _, _, .step headRegime tailPolicy =>
      headRegime.Obligation × RolewiseObligation tailPolicy

/-- Pointwise carry from constituted profiles into policy obligations. -/
def rolewiseCarry :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      RoleOccurrenceProfile roles → RolewiseObligation policy
  | _, _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, _, .step headRegime tailPolicy, profile =>
      (headRegime.carry profile.1,
        rolewiseCarry tailPolicy profile.2)

/-- Complete frontier of obligations induced from local regime frontiers. -/
def rolewiseObligationFrontier :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      List (RolewiseObligation policy)
  | _, _, _, _, .nil => [()]
  | _, _, _, _, .step headRegime tailPolicy =>
      productFrontier headRegime.frontier
        (rolewiseObligationFrontier tailPolicy)

def rolewiseObligationDecEq :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      DecidableEq (RolewiseObligation policy)
  | _, _, _, _, .nil => fun left right =>
      match left, right with
      | (), () => isTrue rfl
  | _, _, _, _, .step headRegime tailPolicy => fun left right =>
      match headRegime.decEq left.1 right.1 with
      | isFalse headDifferent =>
          isFalse (fun same => headDifferent (congrArg Prod.fst same))
      | isTrue headSame =>
          match rolewiseObligationDecEq tailPolicy left.2 right.2 with
          | isFalse tailDifferent =>
              isFalse (fun same => tailDifferent (congrArg Prod.snd same))
          | isTrue tailSame => isTrue (Prod.ext headSame tailSame)

theorem rolewiseObligationFrontier_complete :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      (obligation : RolewiseObligation policy) →
      obligation ∈ rolewiseObligationFrontier policy
  | _, _, _, _, .nil, obligation => by cases obligation; exact .head _
  | _, _, _, _, .step headRegime tailPolicy, obligation =>
      productFrontier_complete
        (headRegime.complete obligation.1)
        (rolewiseObligationFrontier_complete tailPolicy obligation.2)

theorem rolewiseObligationFrontier_nodup :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      (rolewiseObligationFrontier policy).Nodup
  | _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, .step headRegime tailPolicy => by
      letI : DecidableEq headRegime.Obligation := headRegime.decEq
      letI : DecidableEq (RolewiseObligation tailPolicy) :=
        rolewiseObligationDecEq tailPolicy
      exact productFrontier_nodup headRegime.nodup
        (rolewiseObligationFrontier_nodup tailPolicy)

theorem rolewiseCarry_surjective :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      (obligation : RolewiseObligation policy) →
      ∃ profile, rolewiseCarry policy profile = obligation
  | _, _, _, _, .nil, obligation => by
      cases obligation
      exact ⟨(), rfl⟩
  | _, _, _, _, .step headRegime tailPolicy, obligation => by
      rcases headRegime.carry_surjective obligation.1 with
        ⟨headOccurrence, headExact⟩
      rcases rolewiseCarry_surjective tailPolicy obligation.2 with
        ⟨tailProfile, tailExact⟩
      exact ⟨(headOccurrence, tailProfile), Prod.ext headExact tailExact⟩

/-- Global finite regime induced by a local rolewise policy. -/
def rolewiseObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (policy : RolewiseObligationPolicy roles) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  { Obligation := RolewiseObligation policy
    decEq := rolewiseObligationDecEq policy
    frontier := rolewiseObligationFrontier policy
    complete := rolewiseObligationFrontier_complete policy
    nodup := rolewiseObligationFrontier_nodup policy
    carry := rolewiseCarry policy
    carry_surjective := rolewiseCarry_surjective policy }

/-- Every role history has a positive default occurrence profile. -/
def defaultRoleOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles
  | _, _, _, .nil => ()
  | _, _, _, .step headRole tailRoles =>
      (roleConstitutedOccurrenceAt headRole .left,
        defaultRoleOccurrenceProfile tailRoles)

/-- The same positive default, with the role history inferred from its policy. -/
def defaultPolicyOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      RoleOccurrenceProfile roles
  | _, _, _, _, .nil => ()
  | _, _, _, _, @RolewiseObligationPolicy.step
      _ _ _ _ headRole _ _ tailPolicy =>
        (roleConstitutedOccurrenceAt headRole .left,
          defaultPolicyOccurrenceProfile tailPolicy)

/-- Pointwise proposition that every local carry map is injective. -/
def AllLocalPoliciesPreserve :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      RolewiseObligationPolicy roles → Prop
  | _, _, _, _, .nil => True
  | _, _, _, _, .step headRegime tailPolicy =>
      PreservesIdentitiesSeparately headRegime ∧
        AllLocalPoliciesPreserve tailPolicy

/-- Local injectivity composes to global injectivity. -/
theorem rolewiseCarry_injective_of_allLocal :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      AllLocalPoliciesPreserve policy →
      Function.Injective (rolewiseCarry policy)
  | _, _, _, _, .nil, _, left, right, _ => by
      cases left; cases right; rfl
  | _, _, _, _, .step headRegime tailPolicy, preserves,
      left, right, same => by
        apply Prod.ext
        · exact preserves.1 (congrArg Prod.fst same)
        · exact rolewiseCarry_injective_of_allLocal
            tailPolicy preserves.2 (congrArg Prod.snd same)

/-- Global injectivity forces injectivity of every local regime. -/
theorem allLocal_of_rolewiseCarry_injective :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (policy : RolewiseObligationPolicy roles) →
      Function.Injective (rolewiseCarry policy) →
      AllLocalPoliciesPreserve policy
  | _, _, _, _, .nil, _ => True.intro
  | _, _, _, _, .step headRegime tailPolicy, globalInjective => by
      constructor
      · intro left right same
        let tailDefault := defaultPolicyOccurrenceProfile tailPolicy
        have pairSame :
            rolewiseCarry (RolewiseObligationPolicy.step headRegime tailPolicy)
                (left, tailDefault) =
              rolewiseCarry (RolewiseObligationPolicy.step headRegime tailPolicy)
                (right, tailDefault) :=
          Prod.ext same rfl
        exact congrArg Prod.fst (globalInjective pairSame)
      · apply allLocal_of_rolewiseCarry_injective tailPolicy
        intro left right same
        let headDefault :=
          (defaultPolicyOccurrenceProfile
            (RolewiseObligationPolicy.step headRegime tailPolicy)).1
        have pairSame :
            rolewiseCarry (RolewiseObligationPolicy.step headRegime tailPolicy)
                (headDefault, left) =
              rolewiseCarry (RolewiseObligationPolicy.step headRegime tailPolicy)
                (headDefault, right) :=
          Prod.ext rfl same
        exact congrArg Prod.snd (globalInjective pairSame)

/-- Exact local/global conservation equivalence. -/
theorem allLocalPoliciesPreserve_iff_globalPreservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (policy : RolewiseObligationPolicy roles) :
    AllLocalPoliciesPreserve policy ↔
      PreservesIdentitiesSeparately (rolewiseObligationRegime policy) :=
  ⟨rolewiseCarry_injective_of_allLocal policy,
    allLocal_of_rolewiseCarry_injective policy⟩

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleOpeningFiniteCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolewiseObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolewiseCarry
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolewiseObligationFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolewiseObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.defaultRoleOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.defaultPolicyOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.AllLocalPoliciesPreserve
#print axioms ConstitutiveSearch.EndogenousDecomposition.rolewiseCarry_injective_of_allLocal
#print axioms ConstitutiveSearch.EndogenousDecomposition.allLocal_of_rolewiseCarry_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.allLocalPoliciesPreserve_iff_globalPreservation
/- AXIOM_AUDIT_END -/
