import RelationalFoundations.NativeForgettingSeparationV1
set_option genInjectivity false

/-! The observation contract: phase-based events, absolute occurrence addresses and lost historical decisions. -/

namespace RelationalFoundations.NativeForgettingContract
open RelationalFoundations RelationalFoundations.NativeForgettingV1
open RelationalFoundations.ReducedHeterogeneous (Phase phaseAt)

def pstep : Phase × Nat → Phase × Nat
  | (ph, n) => (ph.next, ReducedHeterogeneous.number (target ph n))

def prun (s : Phase × Nat) : Nat → Phase × Nat
  | 0 => s
  | k + 1 => pstep (prun s k)

theorem phase_memory_runs (m : Memory) (k : Nat) :
    prun (phaseAt m.position, m.active) k = (phaseAt (run m k).position, (run m k).active) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ]
      exact congrArg pstep ih

def pevents (s : Phase × Nat) : Nat → List ReducedHeterogeneous.Event
  | 0 => []
  | k + 1 => pevents s k ++ [eventAt (prun s k).1 (prun s k).2]

theorem phase_memory_events (m : Memory) (k : Nat) :
    pevents (phaseAt m.position, m.active) k = events m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change pevents _ k ++ [eventAt (prun _ k).1 (prun _ k).2] = events m k ++ [event (run m k)]
      rw [ih, phase_memory_runs]
      rfl

theorem phase_memory_view (m : Memory) (k : Nat) :
    ReducedHeterogeneous.state (prun (phaseAt m.position, m.active) k).1 (prun (phaseAt m.position, m.active) k).2 =
      view (run m k) := by
  rw [phase_memory_runs]
  rfl

theorem same_phase_active_different_observation :
    phaseAt (⟨0, 0⟩ : Memory).position = phaseAt (⟨3, 0⟩ : Memory).position ∧
    (∀ k, events ⟨0, 0⟩ k = events ⟨3, 0⟩ k) ∧
    observation ⟨0, 0⟩ ≠ observation ⟨3, 0⟩ := by
  refine ⟨rfl, fun k => ?_, ?_⟩
  · rw [← phase_memory_events, ← phase_memory_events]
    rfl
  · intro same
    have occ := congrArg Observation.occurrence same
    exact Nat.noConfusion (Nat.succ.inj occ)

theorem decision_boolean_also_forgotten :
    forget prefixZero = forget prefixTwo ∧
    prefixZero.2.support.read .truth (.old .head) = true ∧
    prefixTwo.2.support.read .truth (.old .head) = false :=
  ⟨rfl, rfl, rfl⟩

theorem both_prefixes_match : Matches shared prefixZero ∧ Matches shared prefixTwo :=
  ⟨zero_matches, two_matches⟩

theorem unreachable_memory_incoherent : ¬ ReducedHeterogeneous.Coherent (⟨0, 0, 7⟩ : ReducedHeterogeneous.Memory) := by
  intro h
  cases h

theorem reordered_inputs_false :
    (observation ⟨1, 0⟩).inputs ≠ [⟨.number, 0⟩, ⟨.truth, 1⟩] := by
  intro h
  cases h

def firstDecision (seed : Nat) : Bool :=
  (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) 2).1.2.support.read .truth (.old .head)

theorem first_decision_irrecoverable :
    ¬ (∃ recover : Memory → Bool, ∀ seed,
      recover (forget (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) 2).1) = firstDecision seed) := by
  intro ⟨recover, correct⟩
  exact Bool.noConfusion ((correct 0).symm.trans (correct 2))

end RelationalFoundations.NativeForgettingContract

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.NativeForgettingContract.pstep
#print axioms RelationalFoundations.NativeForgettingContract.prun
#print axioms RelationalFoundations.NativeForgettingContract.phase_memory_runs
#print axioms RelationalFoundations.NativeForgettingContract.pevents
#print axioms RelationalFoundations.NativeForgettingContract.phase_memory_events
#print axioms RelationalFoundations.NativeForgettingContract.phase_memory_view
#print axioms RelationalFoundations.NativeForgettingContract.same_phase_active_different_observation
#print axioms RelationalFoundations.NativeForgettingContract.decision_boolean_also_forgotten
#print axioms RelationalFoundations.NativeForgettingContract.both_prefixes_match
#print axioms RelationalFoundations.NativeForgettingContract.unreachable_memory_incoherent
#print axioms RelationalFoundations.NativeForgettingContract.reordered_inputs_false
#print axioms RelationalFoundations.NativeForgettingContract.firstDecision
#print axioms RelationalFoundations.NativeForgettingContract.first_decision_irrecoverable
/- AXIOM_AUDIT_END -/
