import RelationalFoundations.NativeForgettingBridgeV1
set_option genInjectivity false

namespace RelationalFoundations.NativeForgettingV1
open TypedResources

def extendRecord {source middle : HeterogeneousFeedback.State}
    (previous : History HeterogeneousFeedback.Step source middle)
    (next : (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step middle target) :
    (target : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step source target :=
  ⟨next.1, .extend previous next.2⟩

def canonicalExtend {source : HeterogeneousFeedback.State}
    (previous : (middle : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step source middle) :=
  extendRecord previous.2 ⟨HeterogeneousFeedback.next previous.1, HeterogeneousFeedback.canonical previous.1⟩

/-- Only the suffix is constructed, from its active starting state. -/
def canonicalHistory (source : HeterogeneousFeedback.State) : Nat →
    (target : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step source target
  | 0 => ⟨source, .root⟩
  | count + 1 => canonicalExtend (canonicalHistory source count)

theorem locally_exact {source target : HeterogeneousFeedback.State}
    (next : HeterogeneousFeedback.Step source target) (allowed : HeterogeneousFeedback.LocalAdmission next) :
    (⟨target, next⟩ : (last : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step source last) =
      ⟨HeterogeneousFeedback.next source, HeterogeneousFeedback.canonical source⟩ := by
  cases next with
  | observe n b => cases allowed; rfl
  | act n b selected result => obtain ⟨rfl, rfl⟩ := allowed; rfl
  | reuse n result => cases allowed; rfl

theorem admissible_history {source target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step source target) (allowed : HeterogeneousFeedback.Admissible following) :
    canonicalHistory source following.length = ⟨target, following⟩ := by
  induction following with
  | root => rfl
  | extend previous next ih =>
      exact (congrArg canonicalExtend (ih allowed.1)).trans
        (congrArg (extendRecord previous) (locally_exact next allowed.2).symm)

theorem run_view (m : Memory) (count : Nat) : view (run m count) = (canonicalHistory (view m) count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (congrArg view (run_succ m count)).trans
        ((step_view _).trans (congrArg HeterogeneousFeedback.next ih))

theorem all_admissible_terminal (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view m) target)
    (allowed : HeterogeneousFeedback.Admissible following) : view (run m following.length) = target :=
  (run_view m following.length).trans (congrArg Sigma.fst (admissible_history following allowed))

def historyEvents {source : HeterogeneousFeedback.State} : {target : HeterogeneousFeedback.State} →
    History HeterogeneousFeedback.Step source target → List ReducedHeterogeneous.Event
  | _, .root => []
  | target, .extend (b := middle) previous next => historyEvents previous ++ [⟨middle, target, next⟩]
termination_by structural _ history => history

def events (m : Memory) : Nat → List ReducedHeterogeneous.Event
  | 0 => []
  | count + 1 => events m count ++ [event (run m count)]

theorem events_canonical (m : Memory) (count : Nat) :
    events m count = historyEvents (canonicalHistory (view m) count).2 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (congrArg (fun prior => prior ++ [event (run m count)]) ih).trans
        (congrArg (fun last => historyEvents (canonicalHistory (view m) count).2 ++ [last])
          ((event_canonical _).trans
            (congrArg (fun s => (⟨s, HeterogeneousFeedback.next s, HeterogeneousFeedback.canonical s⟩ : ReducedHeterogeneous.Event)) (run_view m count))))

/-- Agreement with every supplied witness, rather than only the final number. -/
theorem all_admissible_events (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view m) target)
    (allowed : HeterogeneousFeedback.Admissible following) : events m following.length = historyEvents following :=
  (events_canonical _ _).trans
    (congrArg (fun packed : (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (view m) last => historyEvents packed.2)
      (admissible_history following allowed))

def tick (m : Memory) : Memory × (ReducedHeterogeneous.Event × (Observation × Production m)) :=
  ⟨step m, event m, observation m, certify m⟩

theorem execution_valid_from {seed : Nat} {first last : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution first last) (valid : HeterogeneousFeedback.Valid first) :
    HeterogeneousFeedback.Valid last := by
  induction execution with
  | idle => exact valid
  | step previous ih => exact HeterogeneousFeedback.advance_valid _ ih

theorem native_reaction_allowed {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (valid : HeterogeneousFeedback.Valid frame) :
    HeterogeneousFeedback.LocalAdmission (HeterogeneousFeedback.reaction frame) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready numeric => exact congrArg TypedResources.test valid
  | observed numeric boolean =>
      exact ⟨valid.2, (congrArg (fun b => TypedResources.adjust b (support.read .number numeric)) valid.2).trans
        (congrArg (TypedResources.adjust _) valid.1)⟩
  | updated numeric => exact valid

theorem native_suffix {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (valid : HeterogeneousFeedback.Valid frame) (count : Nat) :
    (⟨(HeterogeneousFeedback.run frame count).1.1, (HeterogeneousFeedback.run frame count).2.continuation⟩ :
      (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step frame.1 last) = canonicalHistory frame.1 count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (congrArg (extendRecord (HeterogeneousFeedback.run frame count).2.continuation)
        (locally_exact (HeterogeneousFeedback.reaction _)
          (native_reaction_allowed _ (execution_valid_from (HeterogeneousFeedback.run frame count).2 valid)))).trans
            (congrArg canonicalExtend ih)

theorem matches_run (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) : Matches (run m count) (HeterogeneousFeedback.run frame count).1 := by
  induction count with
  | zero => exact matched
  | succ count ih => exact (run_succ m count).symm ▸ matches_step _ _ ih

theorem every_observation (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) :
    observation (run m count) = nativeObservation (HeterogeneousFeedback.run frame count).1 :=
  observation_native _ _ (matches_run m frame matched count)

theorem every_reaction (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) :
    event (run m count) = ⟨(HeterogeneousFeedback.run frame count).1.1,
      (HeterogeneousFeedback.advance (HeterogeneousFeedback.run frame count).1).1,
      HeterogeneousFeedback.reaction (HeterogeneousFeedback.run frame count).1⟩ :=
  event_native _ _ (matches_run m frame matched count)

theorem every_certificate (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) :
    (certify (run m count)).value = ((certify (run m count)).node.map
      (frontierFor (run m count) (HeterogeneousFeedback.run frame count).1 (matches_run m frame matched count))).eval
        (HeterogeneousFeedback.run frame count).1.2.support.read :=
  certified_frontier_evaluation _ _ (matches_run m frame matched count)

theorem every_new_evaluation (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) :
    (certify (run m count)).value = ((certify (run m count)).node.map
      (intoNextFor (run m count) (HeterogeneousFeedback.run frame count).1 (matches_run m frame matched count))).eval
        (HeterogeneousFeedback.advance (HeterogeneousFeedback.run frame count).1).2.support.read :=
  certified_new_evaluation _ _ (matches_run m frame matched count)

def nativeObservations {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Nat → List Observation
  | 0 => []
  | count + 1 => nativeObservations frame count ++ [nativeObservation (HeterogeneousFeedback.run frame count).1]

theorem observation_log (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (count : Nat) : observations m count = nativeObservations frame count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (congrArg (fun prior => prior ++ [observation (run m count)]) ih).trans
        (congrArg (fun last => nativeObservations frame count ++ [last]) (every_observation m frame matched count))

/-- Native admission stays unchanged. All supplied finite suffixes are realized. -/
theorem all_native_continuations (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame)
    {target : HeterogeneousFeedback.State} (following : History HeterogeneousFeedback.Step frame.1 target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    (⟨(HeterogeneousFeedback.run frame following.length).1.1,
      (HeterogeneousFeedback.run frame following.length).2.continuation⟩ :
      (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step frame.1 last) = ⟨target, following⟩ :=
  (native_suffix frame matched.valid following.length).trans (admissible_history following allowed)

theorem transport_identity {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (count : Nat) (kind : Kind) :
    Function.Injective ((HeterogeneousFeedback.run frame count).2.embed kind) :=
  (HeterogeneousFeedback.run frame count).2.resources.embed_injective kind

theorem transport_coordinates {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (count : Nat) (kind : Kind)
    (ref : Ref frame.2.context kind) : address ((HeterogeneousFeedback.run frame count).2.embed kind ref) = address ref :=
  transported_address _ _ _

theorem transports_compose {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (one two : Nat) (kind : Kind)
    (ref : Ref frame.2.context kind) :
    ((HeterogeneousFeedback.run frame one).2.compose (HeterogeneousFeedback.run (HeterogeneousFeedback.run frame one).1 two).2).embed kind ref =
      (HeterogeneousFeedback.run (HeterogeneousFeedback.run frame one).1 two).2.embed kind ((HeterogeneousFeedback.run frame one).2.embed kind ref) :=
  HeterogeneousFeedback.Execution.embed_compose _ _ kind ref

theorem observation_composition (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) (one two : Nat) (later : Nat) :
    observation (run (run m one) (two + later)) =
      nativeObservation (HeterogeneousFeedback.run (HeterogeneousFeedback.run (HeterogeneousFeedback.run frame one).1 two).1 later).1 :=
  (congrArg observation (run_add (run m one) two later)).trans
    (every_observation _ _ (matches_run _ _ (matches_run m frame matched one) two) later)

theorem same_native_continuations (m : Memory) {oneSeed twoSeed : Nat}
    (one : HeterogeneousFeedback.Frame oneSeed) (two : HeterogeneousFeedback.Frame twoSeed)
    (left : Matches m one) (right : Matches m two) (count : Nat) :
    nativeObservations one count = nativeObservations two count :=
  (observation_log m one left count).symm.trans (observation_log m two right count)

/-- Closed entry point: reachability supplies every law in Matches, while the
suffix is independently admitted by the unchanged native predicate. -/
theorem forgetting_all_admissible {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame)
    {target : HeterogeneousFeedback.State} (following : History HeterogeneousFeedback.Step (view (forget frame)) target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    view (run (forget frame) following.length) = target ∧
    events (forget frame) following.length = historyEvents following ∧
    observations (forget frame) following.length = nativeObservations frame following.length :=
  ⟨all_admissible_terminal _ following allowed, all_admissible_events _ following allowed,
    observation_log _ _ (forget_matches execution) _⟩

theorem forgetting_all_new_evaluations {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame) (count : Nat) :
    (certify (run (forget frame) count)).value = ((certify (run (forget frame) count)).node.map
      (intoNextFor (run (forget frame) count) (HeterogeneousFeedback.run frame count).1
        (matches_run (forget frame) frame (forget_matches execution) count))).eval
          (HeterogeneousFeedback.advance (HeterogeneousFeedback.run frame count).1).2.support.read :=
  every_new_evaluation _ _ (forget_matches execution) count

end RelationalFoundations.NativeForgettingV1
