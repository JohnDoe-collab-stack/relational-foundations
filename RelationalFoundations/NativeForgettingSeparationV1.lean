import RelationalFoundations.NativeForgettingContinuationV1
set_option genInjectivity false

namespace RelationalFoundations.NativeForgettingV1
open TypedResources

def prefixZero := (HeterogeneousFeedback.run (HeterogeneousFeedback.initial 0) 2).1
def prefixTwo := (HeterogeneousFeedback.run (HeterogeneousFeedback.initial 2) 2).1
def shared : Memory := ⟨2, 1⟩

theorem zero_erased : forget prefixZero = shared := rfl
theorem two_erased : forget prefixTwo = shared := rfl
theorem same_erased : forget prefixZero = forget prefixTwo := rfl

theorem zero_matches : Matches shared prefixZero :=
  forget_matches (HeterogeneousFeedback.run (HeterogeneousFeedback.initial 0) 2).2

theorem two_matches : Matches shared prefixTwo :=
  forget_matches (HeterogeneousFeedback.run (HeterogeneousFeedback.initial 2) 2).2

def reuseSuffix : History HeterogeneousFeedback.Step (view shared) (.ready 1) :=
  .extend .root (.reuse 1 1)

theorem reuseSuffix_admitted : HeterogeneousFeedback.Admissible reuseSuffix := ⟨True.intro, rfl⟩

theorem nonempty_reuse : reuseSuffix.length = 1 := rfl

theorem calculated_reuse : event shared = ⟨.updated 1, .ready 1, HeterogeneousFeedback.Step.reuse 1 1⟩ := rfl

theorem typed_reuse_wiring : observation shared = ⟨3, .number, (1 : Nat), .reuse, [⟨.number, 2⟩]⟩ := rfl

theorem fresh_reuse_identity : (observation shared).occurrence ≠ coordinate .updated shared.position .number .head := by
  change (3 : Nat) ≠ 2
  intro same
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj same))

theorem reuse_certified : (certify shared).value = (certify shared).node.eval
    (read (ReducedHeterogeneous.phaseAt shared.position) shared.active) := (certify shared).certified

theorem same_all_future_observations (count : Nat) : nativeObservations prefixZero count = nativeObservations prefixTwo count :=
  same_native_continuations shared prefixZero prefixTwo zero_matches two_matches count

/-- The supplied suffixes use exactly the native admission predicate. -/
theorem same_all_admitted_suffixes {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view shared) target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    (⟨(HeterogeneousFeedback.run prefixZero following.length).1.1,
      (HeterogeneousFeedback.run prefixZero following.length).2.continuation⟩ :
      (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (view shared) last) = ⟨target, following⟩ ∧
    (⟨(HeterogeneousFeedback.run prefixTwo following.length).1.1,
      (HeterogeneousFeedback.run prefixTwo following.length).2.continuation⟩ :
      (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (view shared) last) = ⟨target, following⟩ :=
  ⟨all_native_continuations shared prefixZero zero_matches following allowed,
    all_native_continuations shared prefixTwo two_matches following allowed⟩

theorem zero_new_certificates (count : Nat) :
    (certify (run shared count)).value = ((certify (run shared count)).node.map
      (frontierFor (run shared count) (HeterogeneousFeedback.run prefixZero count).1
        (matches_run shared prefixZero zero_matches count))).eval
          (HeterogeneousFeedback.run prefixZero count).1.2.support.read :=
  every_certificate _ _ zero_matches count

theorem two_new_certificates (count : Nat) :
    (certify (run shared count)).value = ((certify (run shared count)).node.map
      (frontierFor (run shared count) (HeterogeneousFeedback.run prefixTwo count).1
        (matches_run shared prefixTwo two_matches count))).eval
          (HeterogeneousFeedback.run prefixTwo count).1.2.support.read :=
  every_certificate _ _ two_matches count

theorem initial_observation_separates :
    prefixZero.2.support.read .number (.old (.old .head)) ≠ prefixTwo.2.support.read .number (.old (.old .head)) := by
  exact Nat.noConfusion

theorem origin_irrecoverable :
    ¬ (∃ recover : Memory → Nat, ∀ old : ReducedHeterogeneous.Memory, ReducedHeterogeneous.Coherent old →
      recover (erase old) = old.origin) := by
  intro ⟨recover, correct⟩
  apply ReducedHeterogeneous.origin_not_reconstructible
  exact ⟨fun pair => recover ⟨pair.1, pair.2⟩, fun old coherent => correct old coherent⟩

theorem origin_irrecoverable_from_prefixes :
    ¬ (∃ recover : Memory → Nat, ∀ seed count,
      recover (forget (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) count).1) = seed) := by
  intro ⟨recover, correct⟩
  exact Nat.noConfusion ((correct 0 2).symm.trans (correct 2 2))

/-- Weakening active value fails already at one ready-state consumer. -/
theorem active_not_reconstructible :
    ¬ (∃ recover : Nat → Nat, ∀ number, recover (initial number).position = (initial number).active) := by
  intro ⟨recover, correct⟩
  exact Nat.noConfusion ((correct 0).symm.trans (correct 1))

theorem active_consumption_separates :
    produce .ready (initial 0).active ≠ produce .ready (initial 1).active := by
  exact Bool.noConfusion

/-- Equal active numbers can occupy different occurrences and phases. -/
theorem position_not_reconstructible :
    ¬ (∃ recover : Nat → Nat, ∀ seed count,
      recover (run (initial seed) count).active = (run (initial seed) count).position) := by
  intro ⟨recover, correct⟩
  exact Nat.noConfusion ((correct 0 0).symm.trans (correct 0 6))

theorem same_values_different_next_consumers :
    (run (initial 0) 0).active = (run (initial 0) 6).active ∧
      (observation (run (initial 0) 0)).occurrence ≠ (observation (run (initial 0) 6)).occurrence := by
  constructor
  · rfl
  · change (1 : Nat) ≠ 7
    intro same
    exact Nat.noConfusion (Nat.succ.inj same)

end RelationalFoundations.NativeForgettingV1
