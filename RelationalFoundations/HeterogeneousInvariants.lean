import RelationalFoundations.NativeForgettingContinuationV1
set_option genInjectivity false

namespace RelationalFoundations.HeterogeneousInvariants
open HeterogeneousFeedback

/-- The test agrees with the active number, which stays within the initial bound.
The seed is a parameter of the proof; it is absent from the forgotten memory. -/
def Invariant (seed : Nat) (state : State) : Prop :=
  ReducedHeterogeneous.Local state ∧ ReducedHeterogeneous.number state ≤ seed + 1

theorem initial (seed : Nat) : Invariant seed (.ready seed) :=
  ⟨True.intro, Nat.le_succ seed⟩

theorem adjust_bounded (seed number : Nat) (bounded : number ≤ seed + 1) :
    TypedResources.adjust (TypedResources.test number) number ≤ seed + 1 := by
  cases number with
  | zero => exact Nat.succ_le_succ (Nat.zero_le seed)
  | succ number => exact Nat.le_trans (Nat.le_succ number) bounded

theorem step_preserves {seed : Nat} {source target : State} (step : Step source target)
    (allowed : LocalAdmission step) (prior : Invariant seed source) : Invariant seed target := by
  cases step with
  | observe number flag => exact ⟨allowed, prior.2⟩
  | act number flag selected result =>
      have coherent : flag = TypedResources.test number := prior.1
      have same : result = TypedResources.adjust (TypedResources.test number) number :=
        allowed.2.trans (congrArg (fun value => TypedResources.adjust value number) coherent)
      exact ⟨True.intro, same.symm ▸ adjust_bounded seed number prior.2⟩
  | reuse number result => exact ⟨True.intro, allowed.symm ▸ prior.2⟩

theorem admitted_preserves {seed : Nat} {source target : State}
    (history : History Step source target) (allowed : Admissible history)
    (prior : Invariant seed source) : Invariant seed target := by
  induction history with
  | root => exact prior
  | extend previous step ih => exact step_preserves step allowed.2 (ih allowed.1)

/-- The independently proved invariant is extracted from the common constructor. -/
theorem extracted {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (allowed : Admissible history) :
    Invariant seed (visible (FiniteRuleInstances.heterogeneousComplete history allowed).realization.frame) :=
  (FiniteRuleInstances.heterogeneous seed).extract_guarantee
    (fun state _ => Invariant seed state) (initial seed)
    (fun step admitted _ prior => step_preserves step admitted prior)
    history ((FiniteRuleInstances.heterogeneousAdmission seed history).mpr allowed)

theorem native_run (seed depth : Nat) :
    Invariant seed (run (HeterogeneousFeedback.initial seed) depth).1.1 := by
  have actual := admitted_preserves _ (execution_admitted (run (HeterogeneousFeedback.initial seed) depth).2) (initial seed)
  exact actual

/-- Every admitted suffix preserves the bound in the actual scalar execution. -/
theorem forgotten_suffix {seed : Nat} (memory : NativeForgettingV1.Memory)
    (prior : Invariant seed (NativeForgettingV1.view memory)) {target : State}
    (following : History Step (NativeForgettingV1.view memory) target) (allowed : Admissible following) :
    Invariant seed (NativeForgettingV1.view (NativeForgettingV1.run memory following.length)) :=
  (NativeForgettingV1.all_admissible_terminal memory following allowed).symm ▸
    admitted_preserves following allowed prior

theorem forgotten_run {seed : Nat} (memory : NativeForgettingV1.Memory)
    (prior : Invariant seed (NativeForgettingV1.view memory)) (depth : Nat) :
    Invariant seed (NativeForgettingV1.view (NativeForgettingV1.run memory depth)) := by
  induction depth with
  | zero => exact prior
  | succ depth ih =>
      rw [NativeForgettingV1.run_succ, NativeForgettingV1.step_view]
      exact step_preserves (canonical _) (canonical_admitted _) ih

/-- Closed chain from the common constructor through forgetting and every later tick. -/
theorem constructed_then_forgotten {seed : Nat} {target : State}
    (history : History Step (.ready seed) target) (allowed : Admissible history) (depth : Nat) :
    Invariant seed (NativeForgettingV1.view (NativeForgettingV1.run
      (NativeForgettingV1.forget (FiniteRuleInstances.heterogeneousComplete history allowed).realization.frame) depth)) := by
  let actual := FiniteRuleInstances.heterogeneousComplete history allowed
  let native := FiniteRuleInstances.heterogeneousRealization history allowed actual.realization
  have checked := execution_valid native.execution
  have prior : Invariant seed native.frame.1 :=
    (visible_valid native.frame checked) ▸ extracted history allowed
  have matched := NativeForgettingV1.forget_matches native.execution
  exact forgotten_run _ (matched.state.symm ▸ prior) depth

end RelationalFoundations.HeterogeneousInvariants

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.HeterogeneousInvariants.Invariant
#print axioms RelationalFoundations.HeterogeneousInvariants.adjust_bounded
#print axioms RelationalFoundations.HeterogeneousInvariants.step_preserves
#print axioms RelationalFoundations.HeterogeneousInvariants.admitted_preserves
#print axioms RelationalFoundations.HeterogeneousInvariants.extracted
#print axioms RelationalFoundations.HeterogeneousInvariants.native_run
#print axioms RelationalFoundations.HeterogeneousInvariants.forgotten_suffix
#print axioms RelationalFoundations.HeterogeneousInvariants.forgotten_run
#print axioms RelationalFoundations.HeterogeneousInvariants.constructed_then_forgotten
/- AXIOM_AUDIT_END -/
