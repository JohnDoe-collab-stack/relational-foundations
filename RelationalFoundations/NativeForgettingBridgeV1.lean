import RelationalFoundations.NativeForgettingV1
set_option genInjectivity false

namespace RelationalFoundations.NativeForgettingV1
open TypedResources
open ReducedHeterogeneous (Phase phaseAt)

/-- A chronological address is obtained from the actual typed reference.
The scope of the address remains the native execution containing that reference. -/
def address : {context : List Kind} → {kind : Kind} → Ref context kind → Nat
  | _, _, @Ref.head _ rest => rest.length
  | _, _, .old ref => address ref

theorem address_bound : {context : List Kind} → {kind : Kind} → (ref : Ref context kind) → address ref < context.length
  | _, _, .head => Nat.lt_succ_self _
  | _, _, .old ref => Nat.lt_trans (address_bound ref) (Nat.lt_succ_self _)

theorem address_identity : {context : List Kind} → {kind : Kind} → (one two : Ref context kind) →
    address one = address two → one = two
  | _, _, .head, .head, _ => rfl
  | _, _, .head, .old ref, same => False.elim (Nat.lt_irrefl _ (same ▸ address_bound ref))
  | _, _, .old ref, .head, same => False.elim (Nat.lt_irrefl _ (same ▸ address_bound ref))
  | _, _, .old one, .old two, same => congrArg Ref.old (address_identity one two same)

theorem transported_address {a b : List Kind} {first : Support a} {last : Support b}
    (extension : Extension first last) (kind : Kind) (ref : Ref a kind) :
    address (extension.embed kind ref) = address ref := by
  induction extension with
  | refl => rfl
  | push previous _ ih => exact ih

def Sized {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Prop :=
  frame.2.context.length = frame.2.history.length + 1

def Focused {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Prop :=
  match frame with
  | ⟨.ready _, data⟩ => match data.focus with
      | .ready numeric => address numeric = data.history.length
  | ⟨.observed _ _, data⟩ => match data.focus with
      | .observed numeric boolean =>
          address numeric = data.history.length.pred ∧ address boolean = data.history.length
  | ⟨.updated _, data⟩ => match data.focus with
      | .updated numeric => address numeric = data.history.length

theorem advance_sized {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (sized : Sized frame) :
    Sized (HeterogeneousFeedback.advance frame) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus <;> exact congrArg (fun n => n + 1) sized

theorem advance_focused {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (sized : Sized frame) (focused : Focused frame) : Focused (HeterogeneousFeedback.advance frame) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready ref => exact ⟨focused, sized⟩
  | observed _ _ => exact sized
  | updated _ => exact sized

theorem execution_sized {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame) : Sized frame := by
  induction execution with
  | idle => rfl
  | step previous ih => exact advance_sized _ ih

theorem execution_focused {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame) : Focused frame := by
  induction execution with
  | idle => rfl
  | step previous ih => exact advance_focused _ (execution_sized previous) ih

/-- This relation is used in proofs, never stored in execution memory. -/
structure Matches (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Prop where
  state : view m = frame.1
  position : m.position = frame.2.history.length
  valid : HeterogeneousFeedback.Valid frame
  sized : Sized frame
  focused : Focused frame

def forget {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : Memory :=
  ⟨frame.2.history.length, ReducedHeterogeneous.number (HeterogeneousFeedback.visible frame)⟩

theorem forget_matches {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame) : Matches (forget frame) frame :=
  ⟨ReducedHeterogeneous.reduce_view execution, rfl, HeterogeneousFeedback.execution_valid execution,
    execution_sized execution, execution_focused execution⟩

theorem matches_step (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    Matches (step m) (HeterogeneousFeedback.advance frame) :=
  ⟨(step_view m).trans ((congrArg HeterogeneousFeedback.next matched.state).trans
      (HeterogeneousFeedback.advance_state frame matched.valid).symm),
    (congrArg (fun n => n + 1) matched.position).trans (HeterogeneousFeedback.advance_history_length frame).symm,
    HeterogeneousFeedback.advance_valid frame matched.valid, advance_sized frame matched.sized,
    advance_focused frame matched.sized matched.focused⟩

theorem forget_step {seed : Nat} {frame : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame) :
    forget (HeterogeneousFeedback.advance frame) = step (forget frame) :=
  congrArg erase (ReducedHeterogeneous.reduce_step execution) |>.trans (erase_step (ReducedHeterogeneous.reduce frame))

def frontierEmbedding {seed : Nat} : (frame : HeterogeneousFeedback.Frame seed) → (kind : Kind) →
    Ref (Context (ReducedHeterogeneous.phase frame.1)) kind → Ref frame.2.context kind
  | ⟨.ready _, data⟩ => match data.focus with
      | .ready numeric => prependPorts numeric emptyPorts
  | ⟨.observed _ _, data⟩ => match data.focus with
      | .observed numeric boolean => prependPorts boolean (prependPorts numeric emptyPorts)
  | ⟨.updated _, data⟩ => match data.focus with
      | .updated numeric => prependPorts numeric emptyPorts

theorem frontier_unique (stage : Phase) (kind : Kind) (one two : Ref (Context stage) kind) : one = two := by
  cases stage with
  | ready => cases one with
      | head => cases two with | head => rfl | old impossible => cases impossible
      | old impossible => cases impossible
  | observed => cases one with
      | head => cases two with
          | head => rfl
          | old impossible => cases impossible with | old impossible => cases impossible
      | old one => cases one with
          | head => cases two with
              | old two => cases two with | head => rfl | old impossible => cases impossible
          | old impossible => cases impossible
  | updated => cases one with
      | head => cases two with | head => rfl | old impossible => cases impossible
      | old impossible => cases impossible

theorem frontier_injective {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (kind : Kind) :
    Function.Injective (frontierEmbedding frame kind) := fun one two _ => frontier_unique _ kind one two

theorem frontier_read {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (valid : HeterogeneousFeedback.Valid frame)
    (law : ReducedHeterogeneous.Local frame.1) (kind : Kind)
    (ref : Ref (Context (ReducedHeterogeneous.phase frame.1)) kind) :
    frame.2.support.read kind (frontierEmbedding frame kind ref) =
      read (ReducedHeterogeneous.phase frame.1) (ReducedHeterogeneous.number frame.1) kind ref := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready numeric => cases ref with | head => exact valid | old impossible => cases impossible
  | observed numeric boolean => cases ref with
      | head => exact valid.2.trans law
      | old ref => cases ref with | head => exact valid.1 | old impossible => cases impossible
  | updated numeric => cases ref with | head => exact valid | old impossible => cases impossible

theorem frontier_address {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (focused : Focused frame)
    (kind : Kind) (ref : Ref (Context (ReducedHeterogeneous.phase frame.1)) kind) :
    address (frontierEmbedding frame kind ref) = coordinate (ReducedHeterogeneous.phase frame.1) frame.2.history.length kind ref := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready numeric => cases ref with | head => exact focused | old impossible => cases impossible
  | observed numeric boolean => cases ref with
      | head => exact focused.2
      | old ref => cases ref with | head => exact focused.1 | old impossible => cases impossible
  | updated numeric => cases ref with | head => exact focused | old impossible => cases impossible

def intoNext {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) :
    (kind : Kind) → Ref (Context (ReducedHeterogeneous.phase frame.1)) kind → Ref (HeterogeneousFeedback.advance frame).2.context kind :=
  fun kind ref => (HeterogeneousFeedback.advanceResources frame).embed kind (frontierEmbedding frame kind ref)

def outputRef {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) :
    Ref (HeterogeneousFeedback.advance frame).2.context (Result (ReducedHeterogeneous.phase frame.1)) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus <;> exact .head

theorem output_fresh_address {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) : address (outputRef frame) = frame.2.context.length := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus <;> rfl

theorem fresh_separate {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (kind : Kind) (ref : Ref frame.2.context kind) :
    address (outputRef frame) ≠ address ((HeterogeneousFeedback.advanceResources frame).embed kind ref) := by
  rw [output_fresh_address, transported_address]
  intro same
  exact Nat.lt_irrefl _ (same ▸ address_bound ref)

theorem new_operator {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) :
    (HeterogeneousFeedback.advance frame).2.support.nodeAt (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame) =
      (operation (ReducedHeterogeneous.phase frame.1)).map (intoNext frame) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus <;> rfl

theorem new_ordered_inputs {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) :
    ((HeterogeneousFeedback.advance frame).2.support.nodeAt (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame)).inputs =
      (operation (ReducedHeterogeneous.phase frame.1)).inputs.map (AnyRef.map (intoNext frame)) :=
  (congrArg Operation.inputs (new_operator frame)).trans (Operation.inputs_map _ _)

theorem native_new_value {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (valid : HeterogeneousFeedback.Valid frame)
    (law : ReducedHeterogeneous.Local frame.1) :
    (HeterogeneousFeedback.advance frame).2.support.read (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame) =
      produce (ReducedHeterogeneous.phase frame.1) (ReducedHeterogeneous.number frame.1) := by
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready numeric => exact congrArg TypedResources.test valid
  | observed numeric boolean =>
      exact (congrArg (fun b => TypedResources.adjust b (support.read .number numeric)) (valid.2.trans law)).trans
        (congrArg (TypedResources.adjust _) valid.1)
  | updated numeric => exact valid

def nativeObservation {seed : Nat} : HeterogeneousFeedback.Frame seed → Observation
  | ⟨.ready _, data⟩ => match data.focus with
      | .ready numeric => ⟨data.context.length, .truth, TypedResources.test (data.support.read .number numeric), .test,
          [⟨.number, address numeric⟩]⟩
  | ⟨.observed _ _, data⟩ => match data.focus with
      | .observed numeric boolean => ⟨data.context.length, .number,
          TypedResources.adjust (data.support.read .truth boolean) (data.support.read .number numeric), .adjust,
          [⟨.truth, address boolean⟩, ⟨.number, address numeric⟩]⟩
  | ⟨.updated _, data⟩ => match data.focus with
      | .updated numeric => ⟨data.context.length, .number, data.support.read .number numeric, .reuse,
          [⟨.number, address numeric⟩]⟩

def flag : HeterogeneousFeedback.State → Bool
  | .ready _ => false
  | .observed _ b => b
  | .updated _ => false

theorem observation_native (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    observation m = nativeObservation frame := by
  have same := matched.state
  have size := matched.sized
  have position := matched.position
  have focused := matched.focused
  have valid := matched.valid
  rcases frame with ⟨s, history, context, support, focus⟩
  cases focus with
  | ready numeric =>
      change ReducedHeterogeneous.state (phaseAt m.position) m.active = .ready _ at same
      cases stage : phaseAt m.position with
      | ready =>
          rw [stage] at same
          have numericSame : m.active = _ := congrArg ReducedHeterogeneous.number same
          dsimp only [ReducedHeterogeneous.number] at numericSame
          unfold observation
          rw [stage]
          change Observation.mk (m.position + 1) .truth (TypedResources.test m.active) .test [⟨.number, m.position⟩] =
            Observation.mk context.length .truth (TypedResources.test (support.read .number numeric)) .test [⟨.number, address numeric⟩]
          rw [valid, ← numericSame, focused, ← position, size, ← position]
      | observed => rw [stage] at same; cases same
      | updated => rw [stage] at same; cases same
  | observed numeric boolean =>
      change ReducedHeterogeneous.state (phaseAt m.position) m.active = .observed _ _ at same
      cases stage : phaseAt m.position with
      | ready => rw [stage] at same; cases same
      | observed =>
          rw [stage] at same
          have numericSame : m.active = _ := congrArg ReducedHeterogeneous.number same
          have flagSame : TypedResources.test m.active = _ := congrArg flag same
          dsimp only [ReducedHeterogeneous.number] at numericSame
          dsimp only [flag] at flagSame
          unfold observation
          rw [stage]
          change Observation.mk (m.position + 1) .number (TypedResources.adjust (TypedResources.test m.active) m.active) .adjust
            [⟨.truth, m.position⟩, ⟨.number, m.position.pred⟩] =
            Observation.mk context.length .number (TypedResources.adjust (support.read .truth boolean) (support.read .number numeric)) .adjust
              [⟨.truth, address boolean⟩, ⟨.number, address numeric⟩]
          rw [valid.1, valid.2, ← numericSame, ← flagSame, focused.1, focused.2, ← position, size, ← position]
      | updated => rw [stage] at same; cases same
  | updated numeric =>
      change ReducedHeterogeneous.state (phaseAt m.position) m.active = .updated _ at same
      cases stage : phaseAt m.position with
      | ready => rw [stage] at same; cases same
      | observed => rw [stage] at same; cases same
      | updated =>
          rw [stage] at same
          have numericSame : m.active = _ := congrArg ReducedHeterogeneous.number same
          dsimp only [ReducedHeterogeneous.number] at numericSame
          unfold observation
          rw [stage]
          change Observation.mk (m.position + 1) .number m.active .reuse [⟨.number, m.position⟩] =
            Observation.mk context.length .number (support.read .number numeric) .reuse [⟨.number, address numeric⟩]
          rw [valid, ← numericSame, focused, ← position, size, ← position]

theorem event_native (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    event m = ⟨frame.1, (HeterogeneousFeedback.advance frame).1, HeterogeneousFeedback.reaction frame⟩ :=
  (event_canonical m).trans
    ((congrArg (fun s => (⟨s, HeterogeneousFeedback.next s, HeterogeneousFeedback.canonical s⟩ : ReducedHeterogeneous.Event)) matched.state).trans
      (ReducedHeterogeneous.Native.reaction_canonical frame matched.valid).symm)

theorem view_local (m : Memory) : ReducedHeterogeneous.Local (view m) := by
  unfold view
  cases phaseAt m.position with
  | ready => exact True.intro
  | observed => rfl
  | updated => exact True.intro

theorem phase_view (m : Memory) : ReducedHeterogeneous.phase (view m) = phaseAt m.position := by
  unfold view
  cases phaseAt m.position <;> rfl

theorem phaseMatch (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    phaseAt m.position = ReducedHeterogeneous.phase frame.1 :=
  (phase_view m).symm.trans (congrArg ReducedHeterogeneous.phase matched.state)

def portTransport {one two : Phase} (same : one = two) (kind : Kind) :
    ExactTransport (Ref (Context one) kind) (Ref (Context two) kind) :=
  ExactTransport.ofEquality (congrArg (fun stage => Ref (Context stage) kind) same)

theorem transported_read {one two : Phase} (same : one = two) (n : Nat) (kind : Kind) (ref : Ref (Context one) kind) :
    read two n kind ((portTransport same kind).forward ref) = read one n kind ref := by cases same; rfl

theorem transported_coordinate {one two : Phase} (same : one = two) (position : Nat) (kind : Kind) (ref : Ref (Context one) kind) :
    coordinate two position kind ((portTransport same kind).forward ref) = coordinate one position kind ref := by cases same; rfl

/-- Map one finite frontier into its own native execution. No claim identifies
the same numerical address globally across two different executions. -/
def frontierFor (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    (kind : Kind) → Ref (Context (phaseAt m.position)) kind → Ref frame.2.context kind :=
  fun kind ref => frontierEmbedding frame kind ((portTransport (phaseMatch m frame matched) kind).forward ref)

theorem frontierFor_injective (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) (kind : Kind) :
    Function.Injective (frontierFor m frame matched kind) := fun one two _ => frontier_unique _ kind one two

theorem frontierFor_value (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame)
    (kind : Kind) (ref : Ref (Context (phaseAt m.position)) kind) :
    frame.2.support.read kind (frontierFor m frame matched kind ref) = read (phaseAt m.position) m.active kind ref := by
  have numeric : m.active = ReducedHeterogeneous.number frame.1 :=
    (ReducedHeterogeneous.number_state _ _).symm.trans (congrArg ReducedHeterogeneous.number matched.state)
  exact (frontier_read frame matched.valid (matched.state ▸ view_local m) kind _).trans
    ((congrArg (fun n => read (ReducedHeterogeneous.phase frame.1) n kind
      ((portTransport (phaseMatch m frame matched) kind).forward ref)) numeric.symm).trans
        (transported_read _ _ _ _))

theorem frontierFor_address (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame)
    (kind : Kind) (ref : Ref (Context (phaseAt m.position)) kind) :
    address (frontierFor m frame matched kind ref) = coordinate (phaseAt m.position) m.position kind ref :=
  (frontier_address frame matched.focused kind _).trans
    ((congrArg (fun position => coordinate (ReducedHeterogeneous.phase frame.1) position kind
      ((portTransport (phaseMatch m frame matched) kind).forward ref)) matched.position.symm).trans
        (transported_coordinate _ _ _ _))

def Corresponding (m : Memory) {oneSeed twoSeed : Nat}
    (one : HeterogeneousFeedback.Frame oneSeed) (two : HeterogeneousFeedback.Frame twoSeed)
    (left : Matches m one) (right : Matches m two) (kind : Kind)
    (first : Ref one.2.context kind) (second : Ref two.2.context kind) : Prop :=
  ∃ port, frontierFor m one left kind port = first ∧ frontierFor m two right kind port = second

theorem corresponding_values (m : Memory) {oneSeed twoSeed : Nat}
    (one : HeterogeneousFeedback.Frame oneSeed) (two : HeterogeneousFeedback.Frame twoSeed)
    (left : Matches m one) (right : Matches m two) (kind : Kind)
    (first : Ref one.2.context kind) (second : Ref two.2.context kind)
    (related : Corresponding m one two left right kind first second) :
    one.2.support.read kind first = two.2.support.read kind second := by
  obtain ⟨port, rfl, rfl⟩ := related
  exact (frontierFor_value m one left kind port).trans (frontierFor_value m two right kind port).symm

def Retained (m : Memory) (kind : Kind) (before : Ref (Context (phaseAt m.position)) kind)
    (after : Ref (Context (phaseAt (step m).position)) kind) : Prop :=
  coordinate (phaseAt m.position) m.position kind before = coordinate (phaseAt (step m).position) (step m).position kind after

theorem retained_native_identity (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame)
    (kind : Kind) (before : Ref (Context (phaseAt m.position)) kind) (after : Ref (Context (phaseAt (step m).position)) kind)
    (retained : Retained m kind before after) :
    frontierFor (step m) (HeterogeneousFeedback.advance frame) (matches_step m frame matched) kind after =
      (HeterogeneousFeedback.advanceResources frame).embed kind (frontierFor m frame matched kind before) :=
  address_identity _ _
    ((frontierFor_address _ _ _ kind after).trans
      (retained.symm.trans ((frontierFor_address m frame matched kind before).symm.trans
        (transported_address (HeterogeneousFeedback.advanceResources frame) kind _).symm)))

/-- The imported port value is certified by the boundary correspondence; the
new local node certificate itself is constructed by certify and uses no prefix. -/
theorem certified_frontier_evaluation (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) :
    (certify m).value = ((certify m).node.map (frontierFor m frame matched)).eval frame.2.support.read :=
  ((certify m).certified.trans
    (ReducedHeterogeneous.evaluation_local (certify m).node _ _
      (fun kind ref _ => (frontierFor_value m frame matched kind ref).symm))).trans
        (Operation.eval_map _ _ _).symm

theorem transported_operator {one two : Phase} (same : one = two) {context : List Kind}
    (embed : ∀ kind, Ref (Context two) kind → Ref context kind) :
    (⟨Result one, (operation one).map (fun kind ref => embed kind ((portTransport same kind).forward ref))⟩ :
      (kind : Kind) × Operation context kind) = ⟨Result two, (operation two).map embed⟩ := by cases same; rfl

theorem transported_produce {one two : Phase} (same : one = two) (n : Nat) :
    (⟨Result one, produce one n⟩ : (kind : Kind) × Value kind) = ⟨Result two, produce two n⟩ := by cases same; rfl

def intoNextFor (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    (kind : Kind) → Ref (Context (phaseAt m.position)) kind → Ref (HeterogeneousFeedback.advance frame).2.context kind :=
  fun kind ref => (HeterogeneousFeedback.advanceResources frame).embed kind (frontierFor m frame matched kind ref)

theorem certified_new_evaluation (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed)
    (matched : Matches m frame) :
    (certify m).value = ((certify m).node.map (intoNextFor m frame matched)).eval
      (HeterogeneousFeedback.advance frame).2.support.read :=
  ((certify m).certified.trans
    (ReducedHeterogeneous.evaluation_local (certify m).node _ _ (fun kind ref _ =>
      (frontierFor_value m frame matched kind ref).symm.trans
        ((HeterogeneousFeedback.advanceResources frame).read_preserved kind _).symm))).trans
          (Operation.eval_map _ _ _).symm

/-- Equality of the actual operator syntax and typed references at the new
native node, not merely an equality of computed scalar values. -/
theorem new_operator_memory (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    (⟨Result (phaseAt m.position), (certify m).node.map (intoNextFor m frame matched)⟩ :
      (kind : Kind) × Operation (HeterogeneousFeedback.advance frame).2.context kind) =
      ⟨Result (ReducedHeterogeneous.phase frame.1),
        (HeterogeneousFeedback.advance frame).2.support.nodeAt (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame)⟩ :=
  (transported_operator (phaseMatch m frame matched) (intoNext frame)).trans
    (congrArg (fun node => (⟨Result (ReducedHeterogeneous.phase frame.1), node⟩ :
      (kind : Kind) × Operation (HeterogeneousFeedback.advance frame).2.context kind)) (new_operator frame).symm)

theorem new_inputs_memory (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    ((certify m).node.map (intoNextFor m frame matched)).inputs =
      ((HeterogeneousFeedback.advance frame).2.support.nodeAt (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame)).inputs :=
  congrArg (fun packed : (kind : Kind) × Operation (HeterogeneousFeedback.advance frame).2.context kind => packed.2.inputs)
    (new_operator_memory m frame matched)

theorem new_value_memory (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    (⟨Result (phaseAt m.position), (certify m).value⟩ : (kind : Kind) × Value kind) =
      ⟨Result (ReducedHeterogeneous.phase frame.1),
        (HeterogeneousFeedback.advance frame).2.support.read (Result (ReducedHeterogeneous.phase frame.1)) (outputRef frame)⟩ := by
  have numeric : m.active = ReducedHeterogeneous.number frame.1 :=
    (ReducedHeterogeneous.number_state _ _).symm.trans (congrArg ReducedHeterogeneous.number matched.state)
  exact (transported_produce (phaseMatch m frame matched) m.active).trans
    ((congrArg (fun n => (⟨Result (ReducedHeterogeneous.phase frame.1), produce (ReducedHeterogeneous.phase frame.1) n⟩ :
      (kind : Kind) × Value kind)) numeric).trans
        (congrArg (fun value => (⟨Result (ReducedHeterogeneous.phase frame.1), value⟩ : (kind : Kind) × Value kind))
          (native_new_value frame matched.valid (matched.state ▸ view_local m)).symm))

theorem new_occurrence_memory (m : Memory) {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (matched : Matches m frame) :
    address (outputRef frame) = m.position + 1 :=
  (output_fresh_address frame).trans (matched.sized.trans (congrArg (fun n => n + 1) matched.position.symm))

end RelationalFoundations.NativeForgettingV1
