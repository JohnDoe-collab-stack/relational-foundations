import RelationalFoundations.NativeForgettingSeparationV1
set_option genInjectivity false

/-! An executable encoding retains origin information within two scalar fields while reproducing the native continuation. -/

namespace RelationalFoundations.HiddenEncodingTests
open RelationalFoundations RelationalFoundations.NativeForgettingV1

def half : Nat → Nat × Bool
  | 0 => (0, false)
  | n + 1 => match half n with
    | (q, true) => (q + 1, false)
    | (q, false) => (q, true)

theorem half_even : (a : Nat) → half (2 * a) = (a, false)
  | 0 => rfl
  | a + 1 => by
      show (match half (2 * a + 1) with | (q, true) => (q + 1, false) | (q, false) => (q, true)) = _
      show (match (match half (2 * a) with | (q, true) => (q + 1, false) | (q, false) => (q, true)) with
        | (q, true) => (q + 1, false) | (q, false) => (q, true)) = _
      rw [half_even a]

theorem half_odd (a : Nat) : half (2 * a + 1) = (a, true) := by
  show (match half (2 * a) with | (q, true) => (q + 1, false) | (q, false) => (q, true)) = _
  rw [half_even a]

def strip : Nat → Nat → Nat × Nat
  | 0, n => (0, n)
  | f + 1, n => match half n with
    | (q, false) => ((strip f q).1 + 1, (strip f q).2)
    | (_, true) => (0, n)

def enc : Nat → Nat → Nat
  | 0, a => 2 * a + 1
  | o + 1, a => 2 * enc o a
def decO (n : Nat) : Nat := (strip n n).1
def decA (n : Nat) : Nat := (half (strip n n).2).1

theorem strip_odd (a : Nat) : (f : Nat) → strip f (2 * a + 1) = (0, 2 * a + 1)
  | 0 => rfl
  | f + 1 => by
      show (match half (2 * a + 1) with | (q, false) => ((strip f q).1 + 1, (strip f q).2) | (_, true) => (0, 2 * a + 1)) = _
      rw [half_odd]

theorem enc_succ (o a : Nat) : enc (o + 1) a = 2 * enc o a := rfl

theorem strip_enc (a : Nat) : (o f : Nat) → o ≤ f → strip f (enc o a) = (o, 2 * a + 1)
  | 0, f, _ => strip_odd a f
  | o + 1, 0, le => absurd le (Nat.not_succ_le_zero o)
  | o + 1, f + 1, le => by
      rw [enc_succ]
      show (match half (2 * enc o a) with
        | (q, false) => ((strip f q).1 + 1, (strip f q).2) | (_, true) => (0, 2 * enc o a)) = _
      rw [half_even]
      show ((strip f (enc o a)).1 + 1, (strip f (enc o a)).2) = _
      rw [strip_enc a o f (Nat.le_of_succ_le_succ le)]

theorem enc_pos (a : Nat) : (o : Nat) → 1 ≤ enc o a
  | 0 => Nat.succ_le_succ (Nat.zero_le _)
  | o + 1 => by
      show 1 ≤ 2 * enc o a
      rw [Nat.two_mul]
      exact Nat.le_trans (enc_pos a o) (Nat.le_add_right _ _)

theorem fuel_enough : (o a : Nat) → o ≤ enc o a
  | 0, _ => Nat.zero_le _
  | o + 1, a => by
      show o + 1 ≤ 2 * enc o a
      rw [Nat.two_mul]
      exact Nat.add_le_add (fuel_enough o a) (enc_pos a o)

theorem decO_enc (o a : Nat) : decO (enc o a) = o :=
  congrArg Prod.fst (strip_enc a o _ (fuel_enough o a))

theorem decA_enc (o a : Nat) : decA (enc o a) = a := by
  show (half (strip (enc o a) (enc o a)).2).1 = a
  rw [strip_enc a o _ (fuel_enough o a), half_odd]

structure HMem where
  position : Nat
  active : Nat

def toV1 (h : HMem) : Memory := ⟨h.position, decA h.active⟩
def hinit (seed : Nat) : HMem := ⟨0, enc seed seed⟩
def hstep (h : HMem) : HMem := ⟨h.position + 1, enc (decO h.active) (step (toV1 h)).active⟩
def hrun (h : HMem) : Nat → HMem
  | 0 => h
  | k + 1 => hstep (hrun h k)

theorem hidden_tracks (seed : Nat) : (k : Nat) →
    toV1 (hrun (hinit seed) k) = run (initial seed) k ∧ decO (hrun (hinit seed) k).active = seed
  | 0 => ⟨congrArg (Memory.mk 0) (decA_enc seed seed), decO_enc seed seed⟩
  | k + 1 => by
      have ih := hidden_tracks seed k
      refine ⟨?_, ?_⟩
      · show (⟨(hrun (hinit seed) k).position + 1, decA (enc _ (step (toV1 (hrun (hinit seed) k))).active)⟩ : Memory) = _
        have hp : (hrun (hinit seed) k).position = (run (initial seed) k).position := congrArg Memory.position ih.1
        rw [decA_enc, hp, ih.1, run_succ]
        rfl
      · show decO (enc (decO (hrun (hinit seed) k).active) _) = seed
        rw [decO_enc]
        exact ih.2

theorem hidden_tracks_v1 (seed k : Nat) : toV1 (hrun (hinit seed) k) = run (initial seed) k :=
  (hidden_tracks seed k).1

theorem hidden_origin_recoverable :
    ∃ recover : HMem → Nat, ∀ seed k, recover (hrun (hinit seed) k) = seed :=
  ⟨fun h => decO h.active, fun seed k => (hidden_tracks seed k).2⟩

theorem hidden_separating_horizon :
    toV1 (hrun (hinit 0) 2) = toV1 (hrun (hinit 2) 2) ∧ hrun (hinit 0) 2 ≠ hrun (hinit 2) 2 :=
  ⟨(hidden_tracks_v1 0 2).trans (hidden_tracks_v1 2 2).symm, fun same =>
    Nat.noConfusion ((hidden_tracks 0 2).2.symm.trans ((congrArg (fun h => decO h.active) same).trans (hidden_tracks 2 2).2))⟩

end RelationalFoundations.HiddenEncodingTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.HiddenEncodingTests.half
#print axioms RelationalFoundations.HiddenEncodingTests.half_even
#print axioms RelationalFoundations.HiddenEncodingTests.half_odd
#print axioms RelationalFoundations.HiddenEncodingTests.strip
#print axioms RelationalFoundations.HiddenEncodingTests.enc
#print axioms RelationalFoundations.HiddenEncodingTests.decO
#print axioms RelationalFoundations.HiddenEncodingTests.decA
#print axioms RelationalFoundations.HiddenEncodingTests.strip_odd
#print axioms RelationalFoundations.HiddenEncodingTests.enc_succ
#print axioms RelationalFoundations.HiddenEncodingTests.strip_enc
#print axioms RelationalFoundations.HiddenEncodingTests.enc_pos
#print axioms RelationalFoundations.HiddenEncodingTests.fuel_enough
#print axioms RelationalFoundations.HiddenEncodingTests.decO_enc
#print axioms RelationalFoundations.HiddenEncodingTests.decA_enc
#print axioms RelationalFoundations.HiddenEncodingTests.toV1
#print axioms RelationalFoundations.HiddenEncodingTests.hinit
#print axioms RelationalFoundations.HiddenEncodingTests.hstep
#print axioms RelationalFoundations.HiddenEncodingTests.hrun
#print axioms RelationalFoundations.HiddenEncodingTests.hidden_tracks
#print axioms RelationalFoundations.HiddenEncodingTests.hidden_tracks_v1
#print axioms RelationalFoundations.HiddenEncodingTests.hidden_origin_recoverable
#print axioms RelationalFoundations.HiddenEncodingTests.hidden_separating_horizon
/- AXIOM_AUDIT_END -/
