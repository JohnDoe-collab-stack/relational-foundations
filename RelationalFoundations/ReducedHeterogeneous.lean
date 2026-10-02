import RelationalFoundations.FiniteRuleInstances
set_option genInjectivity false

/-!
Executable scalar continuation, with exact on-demand historical restitution.
Persistent memory contains no support, history, reference or execution witness.
The boolean is locally regenerated; the phase is determined by the position.
-/

namespace RelationalFoundations.ReducedHeterogeneous
open TypedResources




inductive Phase where
  | ready | observed | updated

def Phase.next : Phase → Phase
  | .ready => .observed
  | .observed => .updated
  | .updated => .ready

def phaseAt : Nat → Phase
  | 0 => .ready
  | depth + 1 => (phaseAt depth).next

def number : HeterogeneousFeedback.State → Nat
  | .ready n => n
  | .observed n _ => n
  | .updated n => n

def phase : HeterogeneousFeedback.State → Phase
  | .ready _ => .ready
  | .observed _ _ => .observed
  | .updated _ => .updated

def state (stage : Phase) (n : Nat) : HeterogeneousFeedback.State :=
  match stage with
  | .ready => .ready n
  | .observed => .observed n (TypedResources.test n)
  | .updated => .updated n

theorem phase_next (s : HeterogeneousFeedback.State) : phase (HeterogeneousFeedback.next s) = (phase s).next := by
  cases s <;> rfl

theorem trajectory_phase (seed depth : Nat) : phase (HeterogeneousFeedback.trajectory seed depth) = phaseAt depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact (phase_next _).trans (congrArg Phase.next ih)

/-- The reachable observation boolean is locally reconstructible from its number. -/
def Local (s : HeterogeneousFeedback.State) : Prop :=
  match s with
  | .ready _ => True
  | .observed n b => b = TypedResources.test n
  | .updated _ => True

theorem next_local (s : HeterogeneousFeedback.State) : Local (HeterogeneousFeedback.next s) := by
  cases s with
  | ready _ => rfl
  | observed _ _ => exact True.intro
  | updated _ => exact True.intro

theorem trajectory_local (seed depth : Nat) : Local (HeterogeneousFeedback.trajectory seed depth) := by
  cases depth with
  | zero => exact True.intro
  | succ _ => exact next_local _

theorem state_number (s : HeterogeneousFeedback.State) (law : Local s) : state (phase s) (number s) = s := by
  cases s with
  | ready _ => rfl
  | observed n b => exact congrArg (HeterogeneousFeedback.State.observed n) law.symm
  | updated _ => rfl

/-- Only three scalar naturals. Correctness propositions are separate. -/
structure Memory where
  origin : Nat
  position : Nat
  active : Nat

def view (m : Memory) : HeterogeneousFeedback.State := state (phaseAt m.position) m.active

def initial (seed : Nat) : Memory := ⟨seed, 0, seed⟩

def Coherent (m : Memory) : Prop := view m = HeterogeneousFeedback.trajectory m.origin m.position

theorem initial_coherent (seed : Nat) : Coherent (initial seed) := rfl

/-- The native scalar producer performs test, boolean-directed adjustment or reuse. -/
def produced (m : Memory) : (kind : Kind) × Value kind :=
  match phaseAt m.position with
  | .ready => ⟨.truth, TypedResources.test m.active⟩
  | .observed => ⟨.number, TypedResources.adjust (TypedResources.test m.active) m.active⟩
  | .updated => ⟨.number, m.active⟩

def output (m : Memory) : Nat × Bool :=
  match phaseAt m.position with
  | .ready => ⟨m.active, TypedResources.test m.active⟩
  | .observed => ⟨TypedResources.adjust (TypedResources.test m.active) m.active, TypedResources.test m.active⟩
  | .updated => ⟨m.active, false⟩

def nextState (m : Memory) : HeterogeneousFeedback.State :=
  let result := output m
  match phaseAt m.position with
  | .ready => .observed m.active result.2
  | .observed => .updated result.1
  | .updated => .ready result.1

theorem nextState_eq (m : Memory) : nextState m = HeterogeneousFeedback.next (view m) := by
  unfold nextState output view
  cases stage : phaseAt m.position <;> rfl

def step (m : Memory) : Memory := ⟨m.origin, m.position + 1, number (nextState m)⟩

theorem step_view (m : Memory) : view (step m) = HeterogeneousFeedback.next (view m) := by
  change state ((phaseAt m.position).next) (number (nextState m)) = _
  rw [nextState_eq]
  unfold view
  cases stage : phaseAt m.position <;> rfl

theorem step_coherent (m : Memory) (coherent : Coherent m) : Coherent (step m) :=
  (step_view m).trans (congrArg HeterogeneousFeedback.next coherent)

/-- Erased indices can be compared through the complete operational witness. -/
abbrev Event := (source : HeterogeneousFeedback.State) × (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step source target

def event (m : Memory) : Event :=
  let result := output m
  match phaseAt m.position with
  | .ready => ⟨.ready m.active, .observed m.active result.2, .observe m.active result.2⟩
  | .observed => ⟨.observed m.active (TypedResources.test m.active), .updated result.1,
      .act m.active (TypedResources.test m.active) result.2 result.1⟩
  | .updated => ⟨.updated m.active, .ready result.1, .reuse m.active result.1⟩

theorem event_canonical (m : Memory) : event m =
    ⟨view m, HeterogeneousFeedback.next (view m), HeterogeneousFeedback.canonical (view m)⟩ := by
  unfold event output view
  cases stage : phaseAt m.position <;> rfl

theorem event_target (m : Memory) : (event m).2.1 = nextState m := by
  unfold event nextState
  cases stage : phaseAt m.position <;> rfl

theorem event_admitted (m : Memory) : HeterogeneousFeedback.LocalAdmission (event m).2.2 := by
  rw [event_canonical]
  exact HeterogeneousFeedback.canonical_admitted _

def sweep (position active : Nat) : Nat → Nat
  | 0 => active
  | count + 1 => number (nextState ⟨0, position + count, sweep position active count⟩)

def run (first : Memory) (count : Nat) : Memory :=
  ⟨first.origin, first.position + count, sweep first.position first.active count⟩

theorem run_succ (m : Memory) (count : Nat) : run m (count + 1) = step (run m count) := by
  unfold run step
  rw [← Nat.add_assoc]
  rfl

theorem run_coherent (m : Memory) (coherent : Coherent m) (count : Nat) : Coherent (run m count) := by
  induction count with
  | zero => exact coherent
  | succ count ih => exact (run_succ m count).symm ▸ step_coherent _ ih

theorem run_origin (m : Memory) (count : Nat) : (run m count).origin = m.origin := rfl

theorem run_position (m : Memory) (count : Nat) : (run m count).position = m.position + count := rfl

theorem run_add (m : Memory) (one two : Nat) : run m (one + two) = run (run m one) two := by
  induction two with
  | zero => rfl
  | succ two ih =>
      exact (congrArg (run m) (Nat.add_assoc one two 1).symm).trans
        ((run_succ m (one + two)).trans
          ((congrArg step ih).trans (run_succ (run m one) two).symm))

/-- Replay is only called for an explicit historical restitution. -/
def reconstruct (m : Memory) : HeterogeneousFeedback.Frame m.origin := (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).1

theorem reconstruct_valid (m : Memory) : HeterogeneousFeedback.Valid (reconstruct m) :=
  HeterogeneousFeedback.execution_valid (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2

theorem reconstruct_state (m : Memory) (coherent : Coherent m) : (reconstruct m).1 = view m :=
  (HeterogeneousFeedback.run_trajectory _ _).trans coherent.symm

theorem reconstruct_step (m : Memory) : reconstruct (step m) = HeterogeneousFeedback.advance (reconstruct m) := rfl

theorem reconstruct_run (m : Memory) (count : Nat) :
    reconstruct (run m count) = (HeterogeneousFeedback.run (reconstruct m) count).1 :=
  HeterogeneousFeedback.run_add _ _ _

def reduce {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Memory :=
  ⟨seed, frame.2.history.length, number (HeterogeneousFeedback.visible frame)⟩

namespace Native
theorem frame_run {seed : Nat} {first last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution first last) :
    last = (HeterogeneousFeedback.run first execution.length).1 := by
  induction execution with
  | idle => rfl
  | step previous ih => exact congrArg HeterogeneousFeedback.advance ih

theorem history_length {seed : Nat} {first last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution first last) :
    last.2.history.length = first.2.history.length + execution.length := by
  induction execution with
  | idle => rfl
  | step previous ih =>
      exact (HeterogeneousFeedback.advance_history_length _).trans
        ((congrArg (fun n => n + 1) ih).trans (Nat.add_assoc _ _ _))

theorem replay_specified {seed : Nat} {last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) last) :
    last = HeterogeneousFeedback.specified last.2.history := by
  have admitted := HeterogeneousFeedback.execution_admitted execution
  have length := (history_length execution).trans (Nat.zero_add _)
  exact ((frame_run execution).trans
    ((congrArg (fun n => (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) n).1) length.symm).trans
      (HeterogeneousFeedback.build_run last.2.history admitted).symm)).trans (HeterogeneousFeedback.build last.2.history admitted).exact

theorem reaction_canonical {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (valid : HeterogeneousFeedback.Valid frame) :
    (⟨frame.1, (HeterogeneousFeedback.advance frame).1, HeterogeneousFeedback.reaction frame⟩ : Event) =
      ⟨frame.1, HeterogeneousFeedback.next frame.1, HeterogeneousFeedback.canonical frame.1⟩ := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready ref =>
      change (⟨_, _, HeterogeneousFeedback.Step.observe _ (TypedResources.test (support.read .number ref))⟩ : Event) = _
      rw [valid]
      rfl
  | observed numeric boolean =>
      change (⟨_, _, HeterogeneousFeedback.Step.act _ _ (support.read .truth boolean)
        (TypedResources.adjust (support.read .truth boolean) (support.read .number numeric))⟩ : Event) = _
      rw [valid.1, valid.2]
      rfl
  | updated ref =>
      change (⟨_, _, HeterogeneousFeedback.Step.reuse _ (support.read .number ref)⟩ : Event) = _
      rw [valid]
      rfl
end Native

theorem reconstruct_reduce {seed : Nat} {last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) last) :
    reconstruct (reduce last) = last := by
  change (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) last.2.history.length).1 = last
  have length := (Native.history_length execution).trans (Nat.zero_add _)
  exact (congrArg (fun n => (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) n).1) length).trans (Native.frame_run execution).symm

theorem reduce_view {seed : Nat} {last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) last) :
    view (reduce last) = last.1 := by
  have length := (Native.history_length execution).trans (Nat.zero_add _)
  have same := Native.frame_run execution
  have target := (congrArg Sigma.fst same).trans (HeterogeneousFeedback.run_trajectory seed execution.length)
  have law : Local last.1 := target.symm ▸ trajectory_local seed execution.length
  have stage : phase last.1 = phaseAt last.2.history.length :=
    (congrArg phase target).trans ((trajectory_phase _ _).trans (congrArg phaseAt length.symm))
  change state (phaseAt last.2.history.length) (number (HeterogeneousFeedback.visible last)) = _
  rw [HeterogeneousFeedback.visible_valid last (HeterogeneousFeedback.execution_valid execution), ← stage]
  exact state_number _ law

theorem reduce_coherent {seed : Nat} {last : HeterogeneousFeedback.Frame seed} (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) last) :
    Coherent (reduce last) :=
  (reduce_view execution).trans
    ((congrArg Sigma.fst (reconstruct_reduce execution).symm).trans (HeterogeneousFeedback.run_trajectory _ _))

theorem event_exact (m : Memory) (coherent : Coherent m) :
    event m = ⟨(reconstruct m).1, (HeterogeneousFeedback.advance (reconstruct m)).1, HeterogeneousFeedback.reaction (reconstruct m)⟩ := by
  exact (event_canonical m).trans
    ((congrArg (fun s => (⟨s, HeterogeneousFeedback.next s, HeterogeneousFeedback.canonical s⟩ : Event))
      (reconstruct_state m coherent).symm).trans
        (Native.reaction_canonical _ (reconstruct_valid m)).symm)

def realization (m : Memory) : HeterogeneousFeedback.Realization (reconstruct m).2.history :=
  ⟨reconstruct m, (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2,
    Native.replay_specified (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) m.position).2⟩

/-- Every historical certification is constructed on demand, for all sorts and references. -/
def certificate (m : Memory) : HeterogeneousFeedback.CompleteRealization (reconstruct m).2.history :=
  HeterogeneousFeedback.certify _ (HeterogeneousFeedback.execution_admitted (realization m).execution) (realization m)

theorem certificate_frame (m : Memory) : (certificate m).realization.frame = reconstruct m := rfl

theorem terminal (m : Memory) (coherent : Coherent m) : HeterogeneousFeedback.visible (reconstruct m) = view m :=
  (HeterogeneousFeedback.visible_valid _ (reconstruct_valid m)).trans (reconstruct_state m coherent)

end RelationalFoundations.ReducedHeterogeneous
