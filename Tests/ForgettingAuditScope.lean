import Tests.HiddenEncoding
import RelationalFoundations.NativeForgettingContract
set_option genInjectivity false

/-! A replay retains its origin in scalar data. Shape and name checks are
separate from the collision theorems of the native execution memory. -/

namespace RelationalFoundations.ForgettingAuditScopeTests
open HiddenEncodingTests

structure ReplayMemory where
  position : Nat
  active : Nat

def replay (origin : Nat) : Nat → HeterogeneousFeedback.State
  | 0 => .ready origin
  | depth + 1 => HeterogeneousFeedback.next (replay origin depth)

def initial (origin : Nat) : ReplayMemory := ⟨0, enc origin origin⟩

def step (memory : ReplayMemory) : ReplayMemory :=
  ⟨memory.position + 1,
    enc (decO memory.active)
      (ReducedHeterogeneous.number (replay (decO memory.active) (memory.position + 1)))⟩

def run (memory : ReplayMemory) : Nat → ReplayMemory
  | 0 => memory
  | depth + 1 => step (run memory depth)

def project (memory : ReplayMemory) : NativeForgettingV1.Memory :=
  ⟨memory.position, decA memory.active⟩

theorem replay_terminal (origin : Nat) : (depth : Nat) →
    (NativeForgettingV1.canonicalHistory (.ready origin) depth).1 = replay origin depth
  | 0 => rfl
  | depth + 1 => congrArg HeterogeneousFeedback.next (replay_terminal origin depth)

theorem native_active (origin depth : Nat) :
    (NativeForgettingV1.run (NativeForgettingV1.initial origin) depth).active =
      ReducedHeterogeneous.number (replay origin depth) := by
  have terminal := NativeForgettingV1.run_view (NativeForgettingV1.initial origin) depth
  rw [← replay_terminal]
  have number : ReducedHeterogeneous.number
      (NativeForgettingV1.view (NativeForgettingV1.run (NativeForgettingV1.initial origin) depth)) =
      (NativeForgettingV1.run (NativeForgettingV1.initial origin) depth).active := by
    unfold NativeForgettingV1.view
    cases ReducedHeterogeneous.phaseAt (NativeForgettingV1.run (NativeForgettingV1.initial origin) depth).position <;> rfl
  exact number.symm.trans (congrArg ReducedHeterogeneous.number terminal)

theorem replay_tracks (origin : Nat) : (depth : Nat) →
    project (run (initial origin) depth) = NativeForgettingV1.run (NativeForgettingV1.initial origin) depth ∧
      decO (run (initial origin) depth).active = origin
  | 0 => ⟨congrArg (NativeForgettingV1.Memory.mk 0) (decA_enc origin origin), decO_enc origin origin⟩
  | depth + 1 => by
      have prior := replay_tracks origin depth
      have position : (run (initial origin) depth).position = depth :=
        (congrArg NativeForgettingV1.Memory.position prior.1).trans (Nat.zero_add depth)
      refine ⟨?_, ?_⟩
      · show (⟨(run (initial origin) depth).position + 1,
          decA (enc (decO (run (initial origin) depth).active)
            (ReducedHeterogeneous.number (replay (decO (run (initial origin) depth).active)
              ((run (initial origin) depth).position + 1))))⟩ : NativeForgettingV1.Memory) = _
        rw [decA_enc, prior.2, position, ← native_active]
        show (⟨depth + 1, _⟩ : NativeForgettingV1.Memory) = ⟨0 + (depth + 1), _⟩
        rw [Nat.zero_add]
        rfl
      · show decO (enc (decO (run (initial origin) depth).active) _) = origin
        exact (decO_enc _ _).trans prior.2

theorem origin_recoverable : ∃ recover : ReplayMemory → Nat,
    ∀ origin depth, recover (run (initial origin) depth) = origin :=
  ⟨fun memory => decO memory.active, fun origin depth => (replay_tracks origin depth).2⟩

theorem replay_separates :
    project (run (initial 0) 2) = project (run (initial 2) 2) ∧ run (initial 0) 2 ≠ run (initial 2) 2 :=
  ⟨(replay_tracks 0 2).1.trans (replay_tracks 2 2).1.symm,
    fun same => Nat.noConfusion ((replay_tracks 0 2).2.symm.trans
      ((congrArg (fun memory => decO memory.active) same).trans (replay_tracks 2 2).2))⟩

theorem equal_native_runs {one two : NativeForgettingV1.Memory} (same : one = two) (depth : Nat) :
    NativeForgettingV1.run one depth = NativeForgettingV1.run two depth :=
  congrArg (fun memory => NativeForgettingV1.run memory depth) same

theorem equal_native_observations {one two : NativeForgettingV1.Memory} (same : one = two) (depth : Nat) :
    NativeForgettingV1.observations one depth = NativeForgettingV1.observations two depth :=
  congrArg (fun memory => NativeForgettingV1.observations memory depth) same

theorem colliding_prefixes_continue (depth : Nat) :
    NativeForgettingV1.run (NativeForgettingV1.forget NativeForgettingV1.prefixZero) depth =
      NativeForgettingV1.run (NativeForgettingV1.forget NativeForgettingV1.prefixTwo) depth ∧
    NativeForgettingV1.observations (NativeForgettingV1.forget NativeForgettingV1.prefixZero) depth =
      NativeForgettingV1.observations (NativeForgettingV1.forget NativeForgettingV1.prefixTwo) depth :=
  ⟨equal_native_runs NativeForgettingV1.same_erased depth,
    equal_native_observations NativeForgettingV1.same_erased depth⟩

def replayControl (origin depth : Nat) : Bool :=
  let encoded := run (initial origin) depth
  let native := NativeForgettingV1.run (NativeForgettingV1.initial origin) depth
  Nat.beq encoded.position native.position && Nat.beq (decA encoded.active) native.active &&
    Nat.beq (decO encoded.active) origin

#guard (List.range 13).all (fun origin => (List.range 25).all (replayControl origin))
#eval "AUDIT_V4_REPLAY_RUNTIME_OK: seeds 0..12; horizons 0..24; native projection agrees and origin is retained"

end RelationalFoundations.ForgettingAuditScopeTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.ForgettingAuditScopeTests.replay
#print axioms RelationalFoundations.ForgettingAuditScopeTests.initial
#print axioms RelationalFoundations.ForgettingAuditScopeTests.step
#print axioms RelationalFoundations.ForgettingAuditScopeTests.run
#print axioms RelationalFoundations.ForgettingAuditScopeTests.replay_tracks
#print axioms RelationalFoundations.ForgettingAuditScopeTests.origin_recoverable
#print axioms RelationalFoundations.ForgettingAuditScopeTests.replay_separates
#print axioms RelationalFoundations.ForgettingAuditScopeTests.colliding_prefixes_continue
#print axioms RelationalFoundations.ForgettingAuditScopeTests.replayControl
/- AXIOM_AUDIT_END -/
