import RelationalFoundations.ReducedContinuation
set_option genInjectivity false

namespace RelationalFoundations.ReducedHeterogeneous
open TypedResources

/-- The further weakening of the active cache. Only provenance and position persist. -/
structure Kernel where
  origin : Nat
  position : Nat

def erase (m : Memory) : Kernel := ⟨m.origin, m.position⟩

/-- Scalar recomputation constructs no historical support or reference. -/
def inflate (k : Kernel) : Memory :=
  ⟨k.origin, k.position, number (HeterogeneousFeedback.trajectory k.origin k.position)⟩

theorem inflate_coherent (k : Kernel) : Coherent (inflate k) := by
  change state (phaseAt k.position) (number (HeterogeneousFeedback.trajectory k.origin k.position)) = _
  rw [← trajectory_phase k.origin k.position]
  exact state_number _ (trajectory_local _ _)

theorem erase_inflate (k : Kernel) : erase (inflate k) = k := rfl

theorem inflate_erase (m : Memory) (coherent : Coherent m) : inflate (erase m) = m := by
  change Memory.mk m.origin m.position (number (HeterogeneousFeedback.trajectory m.origin m.position)) = m
  rw [← coherent]
  change Memory.mk m.origin m.position (number (state _ m.active)) = m
  rw [number_state]

def Kernel.initial (seed : Nat) : Kernel := ⟨seed, 0⟩

/-- A tick emits its actual operational witness and returns only the next kernel.
The event is an output; it is not retained inside the kernel. -/
structure Tick where
  emitted : Event
  next : Kernel

def Kernel.tick (k : Kernel) : Tick :=
  let active := inflate k
  ⟨event active, erase (step active)⟩

theorem tick_event (m : Memory) (coherent : Coherent m) : (erase m).tick.emitted = event m :=
  congrArg event (inflate_erase m coherent)

theorem tick_next (m : Memory) (coherent : Coherent m) : (erase m).tick.next = erase (step m) :=
  congrArg (fun memory => erase (step memory)) (inflate_erase m coherent)

theorem tick_active (k : Kernel) : inflate k.tick.next = step (inflate k) :=
  inflate_erase _ (step_coherent _ (inflate_coherent k))

theorem tick_next_view (k : Kernel) : view (inflate k.tick.next) = k.tick.emitted.2.1 :=
  (congrArg view (tick_active k)).trans
    ((step_view _).trans (congrArg (fun e : Event => e.2.1) (event_canonical (inflate k))).symm)

theorem tick_restitution (k : Kernel) :
    reconstruct (inflate k.tick.next) = HeterogeneousFeedback.advance (reconstruct (inflate k)) := rfl

theorem tick_exact (k : Kernel) : k.tick.emitted =
    ⟨(reconstruct (inflate k)).1, (HeterogeneousFeedback.advance (reconstruct (inflate k))).1,
      HeterogeneousFeedback.reaction (reconstruct (inflate k))⟩ := event_exact _ (inflate_coherent k)

theorem tick_admitted (k : Kernel) : HeterogeneousFeedback.LocalAdmission k.tick.emitted.2.2 :=
  event_admitted _

/-- Each tick along any finite continuation computes the same actual witness. -/
theorem every_tick (m : Memory) (coherent : Coherent m) (count : Nat) :
    (erase (run m count)).tick.emitted =
      ⟨(reconstruct (run m count)).1, (HeterogeneousFeedback.advance (reconstruct (run m count))).1,
        HeterogeneousFeedback.reaction (reconstruct (run m count))⟩ :=
  (tick_event _ (run_coherent m coherent count)).trans (event_exact _ (run_coherent m coherent count))

theorem kernel_continuation (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (reconstruct m).1 target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    reconstruct (inflate (erase (run m following.length))) =
      HeterogeneousFeedback.specified (History.append (reconstruct m).2.history following) :=
  all_finite_continuations m following allowed

def originalRef (m : Memory) : Ref (reconstruct m).2.context .number :=
  (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2.embed .number .head

theorem original_value (m : Memory) : (reconstruct m).2.support.read .number (originalRef m) = m.origin :=
  (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2.resources.read_preserved _ _

def withoutOrigin (m : Memory) : Nat × Nat := ⟨m.position, m.active⟩
def withoutPosition (m : Memory) : Nat × Nat := ⟨m.origin, m.active⟩

theorem origin_separator : withoutOrigin (run (initial 0) 2) = withoutOrigin (run (initial 2) 2) := rfl

theorem original_values_separate :
    (reconstruct (run (initial 0) 2)).2.support.read .number (originalRef (run (initial 0) 2)) ≠
      (reconstruct (run (initial 2) 2)).2.support.read .number (originalRef (run (initial 2) 2)) := by
  rw [original_value, original_value]
  exact Nat.noConfusion

theorem origin_not_reconstructible :
    ¬ (∃ recover : Nat × Nat → Nat, ∀ m, Coherent m → recover (withoutOrigin m) = m.origin) := by
  intro ⟨recover, correct⟩
  have one := correct (run (initial 0) 2) (run_coherent _ (initial_coherent 0) 2)
  have two := correct (run (initial 2) 2) (run_coherent _ (initial_coherent 2) 2)
  exact Nat.noConfusion (one.symm.trans ((congrArg recover origin_separator).trans two))

theorem position_separator : withoutPosition (run (initial 0) 0) = withoutPosition (run (initial 0) 6) := rfl

theorem position_not_reconstructible :
    ¬ (∃ recover : Nat × Nat → Nat, ∀ m, Coherent m → recover (withoutPosition m) = m.position) := by
  intro ⟨recover, correct⟩
  have one := correct (run (initial 0) 0) (run_coherent _ (initial_coherent 0) 0)
  have two := correct (run (initial 0) 6) (run_coherent _ (initial_coherent 0) 6)
  exact Nat.noConfusion (one.symm.trans ((congrArg recover position_separator).trans two))

/-- A value coincidence never licenses identification of resource occurrences. -/
theorem repeated_zero_distinct :
    (originalRef (run (initial 0) 6)) ≠ (Ref.head : Ref (reconstruct (run (initial 0) 6)).2.context .number) := by
  intro same
  exact Ref.head_ne_old _ same.symm

theorem repeated_zero_equal :
    (reconstruct (run (initial 0) 6)).2.support.read .number (originalRef (run (initial 0) 6)) =
      (reconstruct (run (initial 0) 6)).2.support.read .number .head := rfl

/-- Abstract encoding: one constructor cell, one cell per scalar, and binary
digits for natural payloads (one digit for zero). This is not an allocator byte model. -/
def digits (n : Nat) : Nat := Nat.log2 n + 1

/-- The recursion underlying the executable logarithm, bounded directly by its
fuel; this proof needs no division lemmas or extensional arithmetic tactics. -/
theorem logLoop_bound (fuel n : Nat) :
    (fuel.rec (fun _ => 0) (fun _ ih value => (Nat.ble 2 value).rec 0 ((ih (value / 2)).succ)) n : Nat) ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      change (Nat.ble 2 n).rec 0
        (((fuel.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
          (fun _ ih value => (Nat.ble 2 value).rec 0 ((ih (value / 2)).succ))) (n / 2)).succ) ≤ fuel.succ
      cases Nat.ble 2 n with
      | false => exact Nat.zero_le _
      | true => exact Nat.succ_le_succ (ih (n / 2))

theorem digits_bound (n : Nat) : digits n ≤ n + 1 :=
  Nat.add_le_add_right (logLoop_bound n n) 1

def kernelCost (k : Kernel) : Nat := 3 + digits k.origin + digits k.position
def cacheCost (m : Memory) : Nat := 4 + digits m.origin + digits m.position + digits m.active

def supportNodes : {context : List Kind} → Support context → Nat
  | _, .empty => 0
  | _, .push previous _ => supportNodes previous + 1

theorem support_nodes : {context : List Kind} → (support : Support context) → supportNodes support = context.length
  | _, .empty => rfl
  | _, .push previous _ => congrArg (fun n => n + 1) (support_nodes previous)

/-- A lower bound counting just history/support constructors and the origin's
digits; operator syntax, references and other witness payloads add further data. -/
def expandedLowerCost (m : Memory) : Nat :=
  supportNodes (reconstruct m).2.support + ((reconstruct m).2.history.length + 1) + digits m.origin

theorem reconstruction_resources (m : Memory) : (reconstruct m).2.context.length = 1 + m.position := by
  have same := Native.replay_specified (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2
  exact (congrArg (fun frame => frame.2.context.length) same).trans
    ((HeterogeneousFeedback.declared_size _).trans (congrArg (fun n => 1 + n) (reconstruction_history_length m)))

theorem expanded_lower_cost (m : Memory) : expandedLowerCost m = 2 * (m.position + 1) + digits m.origin := by
  unfold expandedLowerCost
  rw [support_nodes, reconstruction_resources, reconstruction_history_length]
  rw [Nat.two_mul, Nat.add_comm 1 m.position]

/-- Strict material reduction in the declared cell/digit encoding, from position 3. -/
theorem strict_reduction (m : Memory) (depth : 3 ≤ m.position) : kernelCost (erase m) < expandedLowerCost m := by
  have bounded := digits_bound m.position
  rw [expanded_lower_cost]
  calc
    kernelCost (erase m) ≤ 3 + digits m.origin + (m.position + 1) := Nat.add_le_add_left bounded _
    _ = ((m.position + 1) + 3) + digits m.origin :=
      (Nat.add_comm (3 + digits m.origin) (m.position + 1)).trans
        (Nat.add_assoc (m.position + 1) 3 (digits m.origin)).symm
    _ < ((m.position + 1) + (m.position + 1)) + digits m.origin :=
      Nat.add_lt_add_right (Nat.add_lt_add_left (Nat.lt_succ_of_le depth) _) _
    _ = 2 * (m.position + 1) + digits m.origin := by rw [Nat.two_mul]

/-- Cached execution also strictly reduces this encoding once its extra buffer
fits below the historical constructors that have been removed. -/
theorem cached_reduction (m : Memory) (depth : 4 + digits m.active ≤ m.position) :
    cacheCost m < expandedLowerCost m := by
  have bounded := digits_bound m.position
  rw [expanded_lower_cost]
  calc
    cacheCost m ≤ 4 + digits m.origin + (m.position + 1) + digits m.active :=
      Nat.add_le_add_right (Nat.add_le_add_left bounded _) _
    _ = ((4 + (m.position + 1)) + digits m.active) + digits m.origin :=
      (congrArg (fun n => n + digits m.active) (Nat.add_right_comm 4 (digits m.origin) (m.position + 1))).trans
        (Nat.add_right_comm (4 + (m.position + 1)) (digits m.origin) (digits m.active))
    _ = ((m.position + 1) + (4 + digits m.active)) + digits m.origin :=
      congrArg (fun n => n + digits m.origin)
        ((congrArg (fun n => n + digits m.active) (Nat.add_comm 4 (m.position + 1))).trans
          (Nat.add_assoc (m.position + 1) 4 (digits m.active)))
    _ ≤ ((m.position + 1) + m.position) + digits m.origin :=
      Nat.add_le_add_right (Nat.add_le_add_left depth _) _
    _ < ((m.position + 1) + (m.position + 1)) + digits m.origin :=
      Nat.add_lt_add_right (Nat.add_lt_add_left (Nat.lt_succ_self m.position) _) _
    _ = 2 * (m.position + 1) + digits m.origin := by rw [Nat.two_mul]

/-- Separate, declared operation counters: scalar regeneration and full replay. -/
def scalarRegenerationSteps (k : Kernel) : Nat := k.position
def fullReplaySteps (m : Memory) : Nat := m.position
def restitutionSize (m : Memory) : Nat := 1 + m.position
def workingSupportBound (m : Memory) : Nat := 1 + m.position

theorem replay_length {seed : Nat} (first : HeterogeneousFeedback.Frame seed) (count : Nat) :
    (HeterogeneousFeedback.run first count).2.length = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (fun n => n + 1) ih

theorem replay_step_count (m : Memory) :
    (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2.length = fullReplaySteps m :=
  replay_length _ _

/-- Instrument the same scalar recurrence used by inflate. The second field
counts calls of next, not the costs of natural-number arithmetic or allocation. -/
def regeneration (seed : Nat) : Nat → HeterogeneousFeedback.State × Nat
  | 0 => ⟨.ready seed, 0⟩
  | count + 1 => let prior := regeneration seed count; ⟨HeterogeneousFeedback.next prior.1, prior.2 + 1⟩

theorem regeneration_exact (seed count : Nat) : (regeneration seed count).1 = HeterogeneousFeedback.trajectory seed count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg HeterogeneousFeedback.next ih

theorem regeneration_count (seed count : Nat) : (regeneration seed count).2 = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (fun n => n + 1) ih

theorem scalar_step_count (k : Kernel) : (regeneration k.origin k.position).2 = scalarRegenerationSteps k :=
  regeneration_count _ _

theorem output_size (m : Memory) : (certificate m).resources.length = restitutionSize m :=
  (certificate m).counted.trans (reconstruction_resources m)

theorem working_support_bound (m : Memory) (earlier : Nat) (within : earlier ≤ m.position) :
    (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) earlier).1.2.context.length ≤ workingSupportBound m := by
  have length := reconstruction_resources (⟨m.origin, earlier, 0⟩ : Memory)
  exact length ▸ Nat.add_le_add_left within 1

end RelationalFoundations.ReducedHeterogeneous

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.ReducedHeterogeneous.inflate_coherent
#print axioms RelationalFoundations.ReducedHeterogeneous.strict_reduction
#print axioms RelationalFoundations.ReducedHeterogeneous.scalar_step_count
#print axioms RelationalFoundations.ReducedHeterogeneous.working_support_bound
/- AXIOM_AUDIT_END -/
