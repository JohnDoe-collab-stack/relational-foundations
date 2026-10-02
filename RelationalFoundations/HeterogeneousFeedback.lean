import RelationalFoundations.TypedResources
import RelationalFoundations.FeedbackCoverage
set_option genInjectivity false

/-!
# Complete heterogeneous feedback: numbers, truth values and typed historical reuse

Operational admission and the expected resource values are specified from the
history before realization. The executor reads a number to produce a boolean,
reads that boolean to choose the next numerical operation and its witness,
then reuses the produced number through its typed historical reference.
-/

namespace RelationalFoundations.HeterogeneousFeedback
open TypedResources

inductive State where
  | ready (number : Nat)
  | observed (number : Nat) (flag : Bool)
  | updated (number : Nat)

inductive Step : State → State → Type where
  | observe (number : Nat) (flag : Bool) : Step (.ready number) (.observed number flag)
  | act (number : Nat) (flag selected : Bool) (result : Nat) : Step (.observed number flag) (.updated result)
  | reuse (number result : Nat) : Step (.updated number) (.ready result)

def LocalAdmission : {source target : State} → Step source target → Prop
  | _, _, .observe number flag => flag = TypedResources.test number
  | _, _, .act number flag selected result => selected = flag ∧ result = TypedResources.adjust flag number
  | _, _, .reuse number result => result = number

def Admissible {source : State} : {target : State} → History Step source target → Prop
  | _, .root => True
  | _, .extend previous step => Admissible previous ∧ LocalAdmission step
termination_by structural _ history => history

def next : State → State
  | .ready number => .observed number (TypedResources.test number)
  | .observed number flag => .updated (TypedResources.adjust flag number)
  | .updated number => .ready number

def canonical (state : State) : Step state (next state) :=
  match state with
  | .ready number => .observe number (TypedResources.test number)
  | .observed number flag => .act number flag flag (TypedResources.adjust flag number)
  | .updated number => .reuse number number

theorem canonical_admitted (state : State) : LocalAdmission (canonical state) := by
  cases state with
  | ready _ => rfl
  | observed _ _ => exact ⟨rfl, rfl⟩
  | updated _ => rfl

namespace Step
def kind : {source target : State} → Step source target → Kind
  | _, _, .observe _ _ => .truth
  | _, _, .act _ _ _ _ => .number
  | _, _, .reuse _ _ => .number

def value : {source target : State} → (step : Step source target) → Value step.kind
  | _, _, .observe _ flag => flag
  | _, _, .act _ _ _ result => result
  | _, _, .reuse _ result => result
end Step

inductive Focus (context : List Kind) : State → Type where
  | ready {number : Nat} (ref : Ref context .number) : Focus context (.ready number)
  | observed {number : Nat} {flag : Bool} (numeric : Ref context .number)
      (boolean : Ref context .truth) : Focus context (.observed number flag)
  | updated {number : Nat} (ref : Ref context .number) : Focus context (.updated number)

structure At (seed : Nat) (state : State) where
  history : History Step (.ready seed) state
  context : List Kind
  support : Support context
  focus : Focus context state

abbrev Frame (seed : Nat) := (state : State) × At seed state

def initial (seed : Nat) : Frame seed :=
  ⟨.ready seed, ⟨.root, [.number], .push .empty (.literal seed), .ready .head⟩⟩

def Valid {seed : Nat} (frame : Frame seed) : Prop :=
  match frame with
  | ⟨.ready number, data⟩ => match data.focus with
      | .ready ref => data.support.read .number ref = number
  | ⟨.observed number flag, data⟩ => match data.focus with
      | .observed numeric boolean =>
          data.support.read .number numeric = number ∧ data.support.read .truth boolean = flag
  | ⟨.updated number, data⟩ => match data.focus with
      | .updated ref => data.support.read .number ref = number

def visible {seed : Nat} : Frame seed → State
  | ⟨.ready _, data⟩ => match data.focus with
      | .ready ref => .ready (data.support.read .number ref)
  | ⟨.observed _ _, data⟩ => match data.focus with
      | .observed numeric boolean => .observed (data.support.read .number numeric) (data.support.read .truth boolean)
  | ⟨.updated _, data⟩ => match data.focus with
      | .updated ref => .updated (data.support.read .number ref)

def advance {seed : Nat} : Frame seed → Frame seed
  | ⟨.ready number, data⟩ => match data.focus with
      | .ready ref =>
          let operation : Operation data.context .truth := .test ref
          let result := operation.eval data.support.read
          ⟨.observed number result,
            ⟨.extend data.history (.observe number result), .truth :: data.context,
              .push data.support operation, .observed (.old ref) .head⟩⟩
  | ⟨.observed number flag, data⟩ => match data.focus with
      | .observed numeric boolean =>
          let operation : Operation data.context .number := .adjust boolean numeric
          let selected := data.support.read .truth boolean
          let result := operation.eval data.support.read
          ⟨.updated result,
            ⟨.extend data.history (.act number flag selected result), .number :: data.context,
              .push data.support operation, .updated .head⟩⟩
  | ⟨.updated number, data⟩ => match data.focus with
      | .updated ref =>
          let operation : Operation data.context .number := .reuse ref
          let result := operation.eval data.support.read
          ⟨.ready result,
            ⟨.extend data.history (.reuse number result), .number :: data.context,
              .push data.support operation, .ready .head⟩⟩

theorem initial_valid (seed : Nat) : Valid (initial seed) := rfl

theorem advance_valid {seed : Nat} (frame : Frame seed) (valid : Valid frame) : Valid (advance frame) := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus with
  | ready ref => exact ⟨valid, rfl⟩
  | observed numeric boolean => rfl
  | updated ref => rfl

theorem visible_valid {seed : Nat} (frame : Frame seed) (valid : Valid frame) : visible frame = frame.1 := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus with
  | ready ref => exact congrArg State.ready valid
  | observed numeric boolean =>
      exact (congrArg (fun number => State.observed number (support.read .truth boolean)) valid.1).trans
        (congrArg (State.observed _) valid.2)
  | updated ref => exact congrArg State.updated valid

def declaredContext {seed : Nat} : {target : State} → History Step (.ready seed) target → List Kind
  | _, .root => [.number]
  | _, .extend previous step => step.kind :: declaredContext previous
termination_by structural _ history => history

/-- An independently extracted demand diagram: operators and references, with no execution input. -/
def diagram {seed : Nat} : {target : State} → (history : History Step (.ready seed) target) →
    Support (declaredContext history) × Focus (declaredContext history) target
  | _, .root => ⟨.push .empty (.literal seed), .ready .head⟩
  | _, .extend previous (.observe _ _) =>
      let old := diagram previous
      match old.2 with
      | .ready ref => ⟨.push old.1 (.test ref), .observed (.old ref) .head⟩
  | _, .extend previous (.act _ _ _ _) =>
      let old := diagram previous
      match old.2 with
      | .observed numeric boolean => ⟨.push old.1 (.adjust boolean numeric), .updated .head⟩
  | _, .extend previous (.reuse _ _) =>
      let old := diagram previous
      match old.2 with
      | .updated ref => ⟨.push old.1 (.reuse ref), .ready .head⟩
termination_by structural _ history => history

def specified {seed : Nat} {target : State} (history : History Step (.ready seed) target) : Frame seed :=
  ⟨target, ⟨history, declaredContext history, (diagram history).1, (diagram history).2⟩⟩

/-- Expected values are read from the operational witnesses, independently of the producers. -/
def expected {seed : Nat} : {target : State} → (history : History Step (.ready seed) target) →
    (kind : Kind) → Ref (declaredContext history) kind → Value kind
  | _, .root, _, .head => seed
  | _, .extend previous (.observe _ flag), kind, ref => match ref with
      | .head => flag
      | .old ref => expected previous kind ref
  | _, .extend previous (.act _ _ _ result), kind, ref => match ref with
      | .head => result
      | .old ref => expected previous kind ref
  | _, .extend previous (.reuse _ result), kind, ref => match ref with
      | .head => result
      | .old ref => expected previous kind ref
termination_by structural _ history _ _ => history

def Agreement {context : List Kind} (read : ∀ kind, Ref context kind → Value kind) :
    {state : State} → Focus context state → Prop
  | .ready number, .ready ref => read .number ref = number
  | .observed number flag, .observed numeric boolean => read .number numeric = number ∧ read .truth boolean = flag
  | .updated number, .updated ref => read .number ref = number

theorem diagram_focus_valid {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    Agreement (expected history) (diagram history).2 := by
  induction history with
  | root => rfl
  | extend previous step ih =>
      cases step with
      | observe number flag =>
          cases focus : (diagram previous).2 with
          | ready ref =>
              rw [focus] at ih
              simp only [diagram, focus]
              exact ⟨ih, rfl⟩
      | act number flag selected result =>
          cases focus : (diagram previous).2 with
          | observed numeric boolean => simp only [diagram, focus]; rfl
      | reuse number result =>
          cases focus : (diagram previous).2 with
          | updated ref => simp only [diagram, focus]; rfl

theorem diagram_certified {seed : Nat} {target : State}
    (history : History Step (.ready seed) target) (admitted : Admissible history)
    (kind : Kind) (ref : Ref (declaredContext history) kind) :
    (diagram history).1.read kind ref = expected history kind ref := by
  induction history generalizing kind with
  | root => cases ref with | head => rfl | old ref => cases ref
  | extend previous step ih =>
      have valid := diagram_focus_valid previous
      cases step with
      | observe number flag =>
          cases focus : (diagram previous).2 with
          | ready numeric =>
              rw [focus] at valid
              simp only [diagram, focus]
              cases ref with
              | head => exact (congrArg TypedResources.test ((ih admitted.1 .number numeric).trans valid)).trans admitted.2.symm
              | old ref => exact ih admitted.1 kind ref
      | act number flag selected result =>
          cases focus : (diagram previous).2 with
          | observed numeric boolean =>
              rw [focus] at valid
              simp only [diagram, focus]
              cases ref with
              | head =>
                  have numericValue := (ih admitted.1 .number numeric).trans valid.1
                  have booleanValue := (ih admitted.1 .truth boolean).trans valid.2
                  exact ((congrArg (fun flag => TypedResources.adjust flag ((diagram previous).1.read .number numeric))
                    booleanValue).trans (congrArg (TypedResources.adjust flag) numericValue)).trans admitted.2.2.symm
              | old ref => exact ih admitted.1 kind ref
      | reuse number result =>
          cases focus : (diagram previous).2 with
          | updated numeric =>
              rw [focus] at valid
              simp only [diagram, focus]
              cases ref with
              | head => exact ((ih admitted.1 .number numeric).trans valid).trans admitted.2.symm
              | old ref => exact ih admitted.1 kind ref

theorem specified_valid {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : Valid (specified history) := by
  have valid := diagram_focus_valid history
  unfold Valid specified
  cases focus : (diagram history).2 with
  | ready ref =>
      rw [focus] at valid
      exact (diagram_certified history admitted .number ref).trans valid
  | observed numeric boolean =>
      rw [focus] at valid
      exact ⟨(diagram_certified history admitted .number numeric).trans valid.1,
        (diagram_certified history admitted .truth boolean).trans valid.2⟩
  | updated ref =>
      rw [focus] at valid
      exact (diagram_certified history admitted .number ref).trans valid

theorem advance_specified {seed : Nat} {middle target : State}
    (history : History Step (.ready seed) middle) (admitted : Admissible history)
    (step : Step middle target) (allowed : LocalAdmission step) :
    advance (specified history) = specified (.extend history step) := by
  have prior := diagram_certified history admitted
  have valid := diagram_focus_valid history
  cases step with
  | observe number flag =>
      cases focus : (diagram history).2 with
      | ready numeric =>
          rw [focus] at valid
          have numericValue := (prior .number numeric).trans valid
          simp only [specified, advance, diagram, focus, Operation.eval]
          rw [numericValue, allowed]
          rfl
  | act number flag selected result =>
      cases focus : (diagram history).2 with
      | observed numeric boolean =>
          rw [focus] at valid
          have numericValue := (prior .number numeric).trans valid.1
          have booleanValue := (prior .truth boolean).trans valid.2
          simp only [specified, advance, diagram, focus, Operation.eval]
          rw [numericValue, booleanValue, allowed.1, allowed.2]
          rfl
  | reuse number result =>
      cases focus : (diagram history).2 with
      | updated numeric =>
          rw [focus] at valid
          have numericValue := (prior .number numeric).trans valid
          simp only [specified, advance, diagram, focus, Operation.eval]
          rw [numericValue, allowed]
          rfl

theorem advance_admitted {seed : Nat} (frame : Frame seed) (valid : Valid frame)
    (admitted : Admissible frame.2.history) : Admissible (advance frame).2.history := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus with
  | ready ref => exact ⟨admitted, congrArg TypedResources.test valid⟩
  | observed numeric boolean =>
      exact ⟨admitted, valid.2,
        (congrArg (fun flag => TypedResources.adjust flag (support.read .number numeric)) valid.2).trans
          (congrArg (TypedResources.adjust _) valid.1)⟩
  | updated ref => exact ⟨admitted, valid⟩

def reaction {seed : Nat} (frame : Frame seed) : Step frame.1 (advance frame).1 := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus with
  | ready ref =>
      simp only [advance]
      exact .observe _ (TypedResources.test (support.read .number ref))
  | observed numeric boolean =>
      simp only [advance]
      exact .act _ _ (support.read .truth boolean)
        (TypedResources.adjust (support.read .truth boolean) (support.read .number numeric))
  | updated ref =>
      simp only [advance]
      exact .reuse _ (support.read .number ref)

theorem advance_history {seed : Nat} (frame : Frame seed) :
    (advance frame).2.history = .extend frame.2.history (reaction frame) := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> simp only [advance, reaction] <;> rfl

def advanceResources {seed : Nat} (frame : Frame seed) :
    Extension frame.2.support (advance frame).2.support := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> simp only [advance] <;> exact .push .refl _

inductive Execution {seed : Nat} (first : Frame seed) : Frame seed → Type where
  | idle : Execution first first
  | step {middle : Frame seed} : Execution first middle → Execution first (advance middle)

namespace Execution
variable {seed : Nat} {first second third : Frame seed}

def length : {last : Frame seed} → Execution first last → Nat
  | _, .idle => 0
  | _, .step previous => previous.length + 1

def resources : {last : Frame seed} → (execution : Execution first last) →
    Extension first.2.support last.2.support
  | _, .idle => .refl
  | _, .step (middle := middle) previous => previous.resources.compose (advanceResources middle)

def embed (execution : Execution first second) : ∀ kind, Ref first.2.context kind → Ref second.2.context kind :=
  execution.resources.embed

def continuation : {last : Frame seed} → (execution : Execution first last) → History Step first.1 last.1
  | _, .idle => .root
  | _, .step (middle := middle) previous => .extend previous.continuation (reaction middle)

theorem history_exact (execution : Execution first second) :
    History.append first.2.history execution.continuation = second.2.history := by
  induction execution with
  | idle => rfl
  | step previous ih =>
      exact (congrArg (fun history => History.extend history _) ih).trans (advance_history _).symm

def compose (one : Execution first second) : {last : Frame seed} → Execution second last → Execution first last
  | _, .idle => one
  | _, .step previous => .step (compose one previous)

theorem resources_compose (one : Execution first second) (two : Execution second third) :
    (one.compose two).resources = one.resources.compose two.resources := by
  induction two with
  | idle => rfl
  | step previous ih =>
      exact (congrArg (fun resources => resources.compose (advanceResources _)) ih).trans
        (Extension.compose_associative _ _ _)

theorem embed_compose (one : Execution first second) (two : Execution second third)
    (kind : Kind) (ref : Ref first.2.context kind) :
    (one.compose two).embed kind ref = two.embed kind (one.embed kind ref) :=
  (congrArg (fun extension => extension.embed kind ref) (resources_compose one two)).trans
    (Extension.embed_compose _ _ _ _)

theorem continuation_compose (one : Execution first second) (two : Execution second third) :
    (one.compose two).continuation = History.append one.continuation two.continuation := by
  induction two with
  | idle => rfl
  | step previous ih => exact congrArg (fun history => History.extend history _) ih

theorem compose_associative {fourth : Frame seed} (one : Execution first second)
    (two : Execution second third) (three : Execution third fourth) :
    (one.compose two).compose three = one.compose (two.compose three) := by
  induction three with
  | idle => rfl
  | step previous ih => exact congrArg Execution.step ih
end Execution

theorem execution_valid {seed : Nat} {last : Frame seed} (execution : Execution (initial seed) last) : Valid last := by
  induction execution with
  | idle => exact initial_valid seed
  | step previous ih => exact advance_valid _ ih

theorem execution_admitted {seed : Nat} {last : Frame seed} (execution : Execution (initial seed) last) :
    Admissible last.2.history := by
  induction execution with
  | idle => exact True.intro
  | step previous ih => exact advance_admitted _ (execution_valid previous) ih

structure Realization {seed : Nat} {target : State} (history : History Step (.ready seed) target) where
  frame : Frame seed
  execution : Execution (initial seed) frame
  exact : frame = specified history

def build {seed : Nat} : {target : State} → (history : History Step (.ready seed) target) →
    Admissible history → Realization history
  | _, .root, _ => ⟨initial seed, .idle, rfl⟩
  | _, .extend previous step, admitted =>
      let prior := build previous admitted.1
      ⟨advance prior.frame, .step prior.execution,
        (congrArg advance prior.exact).trans (advance_specified previous admitted.1 step admitted.2)⟩
termination_by structural _ history _ => history

theorem coverage_iff {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    Admissible history ↔ Nonempty (Realization history) := by
  constructor
  · intro admitted
    exact ⟨build history admitted⟩
  · intro ⟨realized⟩
    have actual := execution_admitted realized.execution
    exact (congrArg (fun frame : Frame seed => Admissible frame.2.history) realized.exact) ▸ actual

def declaredDependencies {seed : Nat} : {target : State} → (history : History Step (.ready seed) target) →
    (kind : Kind) → Ref (declaredContext history) kind → List (AnyRef (declaredContext history))
  | _, .root => fun _ ref => match ref with
      | .head => []
      | .old ref => nomatch ref
  | _, .extend previous (.observe _ _) => fun kind ref => match ref with
      | .head => match (diagram previous).2 with
          | .ready numeric => [.number (.old numeric)]
      | .old ref => (declaredDependencies previous kind ref).map AnyRef.old
  | _, .extend previous (.act _ _ _ _) => fun kind ref => match ref with
      | .head => match (diagram previous).2 with
          | .observed numeric boolean => [.truth (.old boolean), .number (.old numeric)]
      | .old ref => (declaredDependencies previous kind ref).map AnyRef.old
  | _, .extend previous (.reuse _ _) => fun kind ref => match ref with
      | .head => match (diagram previous).2 with
          | .updated numeric => [.number (.old numeric)]
      | .old ref => (declaredDependencies previous kind ref).map AnyRef.old
termination_by structural _ history => history

theorem diagram_dependencies {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (kind : Kind) (ref : Ref (declaredContext history) kind) :
    ((diagram history).1.nodeAt kind ref).inputs = declaredDependencies history kind ref := by
  induction history generalizing kind with
  | root => cases ref with | head => rfl | old ref => cases ref
  | extend previous step ih =>
      cases step with
      | observe number flag =>
          cases focus : (diagram previous).2 with
          | ready numeric =>
              simp only [diagram, focus]
              cases ref with
              | head =>
                  change ([.number (.old numeric)] : List (AnyRef (.truth :: declaredContext previous))) =
                    (match (diagram previous).2 with | .ready ref => [.number (.old ref)])
                  rw [focus]
                  rfl
              | old ref => exact (Operation.inputs_map (fun _ => Ref.old) _).trans (congrArg (List.map AnyRef.old) (ih kind ref))
      | act number flag selected result =>
          cases focus : (diagram previous).2 with
          | observed numeric boolean =>
              simp only [diagram, focus]
              cases ref with
              | head =>
                  change ([.truth (.old boolean), .number (.old numeric)] : List (AnyRef (.number :: declaredContext previous))) =
                    (match (diagram previous).2 with
                      | .observed numeric boolean => [.truth (.old boolean), .number (.old numeric)])
                  rw [focus]
                  rfl
              | old ref => exact (Operation.inputs_map (fun _ => Ref.old) _).trans (congrArg (List.map AnyRef.old) (ih kind ref))
      | reuse number result =>
          cases focus : (diagram previous).2 with
          | updated numeric =>
              simp only [diagram, focus]
              cases ref with
              | head =>
                  change ([.number (.old numeric)] : List (AnyRef (.number :: declaredContext previous))) =
                    (match (diagram previous).2 with | .updated ref => [.number (.old ref)])
                  rw [focus]
                  rfl
              | old ref => exact (Operation.inputs_map (fun _ => Ref.old) _).trans (congrArg (List.map AnyRef.old) (ih kind ref))

def coordinates {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (frame : Frame seed) (same : frame = specified history) (kind : Kind) :
    ExactTransport (Ref (declaredContext history) kind) (Ref frame.2.context kind) :=
  ExactTransport.ofEquality (congrArg (fun frame : Frame seed => Ref frame.2.context kind) same.symm)

theorem coordinate_certified {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) (frame : Frame seed) (same : frame = specified history)
    (kind : Kind) (ref : Ref (declaredContext history) kind) :
    frame.2.support.read kind ((coordinates history frame same kind).forward ref) = expected history kind ref := by
  cases same
  exact diagram_certified history admitted kind ref

theorem coordinate_dependencies {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (frame : Frame seed) (same : frame = specified history) (kind : Kind) (ref : Ref (declaredContext history) kind) :
    (frame.2.support.nodeAt kind ((coordinates history frame same kind).forward ref)).inputs =
      (declaredDependencies history kind ref).map (AnyRef.map (fun kind => (coordinates history frame same kind).forward)) := by
  cases same
  exact (diagram_dependencies history kind ref).trans
    (AnyRef.map_list_id _).symm

structure CompleteRealization {seed : Nat} {target : State} (history : History Step (.ready seed) target) where
  realization : Realization history
  coordinates : ∀ kind, ExactTransport (Ref (declaredContext history) kind) (Ref realization.frame.2.context kind)
  certified : ∀ kind ref, realization.frame.2.support.read kind ((coordinates kind).forward ref) = expected history kind ref
  coveredDependencies : ∀ kind ref,
    (realization.frame.2.support.nodeAt kind ((coordinates kind).forward ref)).inputs =
      (declaredDependencies history kind ref).map (AnyRef.map (fun kind => (coordinates kind).forward))
  ruleCertified : ∀ kind ref, realization.frame.2.support.read kind ref =
    (realization.frame.2.support.nodeAt kind ref).eval realization.frame.2.support.read
  resources : List (AnyRef realization.frame.2.context)
  exhaustive : ∀ ref, ref ∈ resources
  unique : resources.Nodup
  counted : resources.length = realization.frame.2.context.length
  terminal : visible realization.frame = target

/-- Produce every certificate for an actual realization, including a resumed one. -/
def certify {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) (realized : Realization history) : CompleteRealization history where
  realization := realized
  coordinates := coordinates history realized.frame realized.exact
  certified := coordinate_certified history admitted realized.frame realized.exact
  coveredDependencies := coordinate_dependencies history realized.frame realized.exact
  ruleCertified := realized.frame.2.support.read_correct
  resources := references realized.frame.2.context
  exhaustive := references_all _
  unique := references_unique _
  counted := references_length _
  terminal := (visible_valid realized.frame (execution_valid realized.execution)).trans (congrArg Sigma.fst realized.exact)

def complete {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : CompleteRealization history := certify history admitted (build history admitted)

theorem complete_coverage_iff {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    Admissible history ↔ Nonempty (CompleteRealization history) :=
  ⟨fun admitted => ⟨complete history admitted⟩, fun ⟨realized⟩ => (coverage_iff history).mpr ⟨realized.realization⟩⟩

theorem declared_size {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    (declaredContext history).length = 1 + history.length := by
  induction history with
  | root => rfl
  | extend previous step ih => exact (congrArg Nat.succ ih).trans (Nat.add_assoc 1 previous.length 1)

theorem complete_size {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : (complete history admitted).resources.length = 1 + history.length :=
  (complete history admitted).counted.trans
    ((congrArg (fun frame : Frame seed => frame.2.context.length) (build history admitted).exact).trans (declared_size history))

def run {seed : Nat} (first : Frame seed) : Nat → (last : Frame seed) × Execution first last
  | 0 => ⟨first, .idle⟩
  | depth + 1 => let prior := run first depth; ⟨advance prior.1, .step prior.2⟩

theorem run_add {seed : Nat} (first : Frame seed) (one two : Nat) :
    (run first (one + two)).1 = (run (run first one).1 two).1 := by
  induction two with
  | zero => rfl
  | succ two ih => exact congrArg advance ih

theorem build_run {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : (build history admitted).frame = (run (initial seed) history.length).1 := by
  induction history with
  | root => rfl
  | extend previous step ih => exact congrArg advance (ih admitted.1)

def trajectory (seed : Nat) : Nat → State
  | 0 => .ready seed
  | depth + 1 => next (trajectory seed depth)

theorem advance_state {seed : Nat} (frame : Frame seed) (valid : Valid frame) : (advance frame).1 = next frame.1 := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus with
  | ready ref => exact congrArg (State.observed _) (congrArg TypedResources.test valid)
  | observed numeric boolean =>
      exact congrArg State.updated
        ((congrArg (fun flag => TypedResources.adjust flag (support.read .number numeric)) valid.2).trans
          (congrArg (TypedResources.adjust _) valid.1))
  | updated ref => exact congrArg State.ready valid

theorem run_trajectory (seed depth : Nat) : (run (initial seed) depth).1.1 = trajectory seed depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      exact (advance_state _ (execution_valid (run (initial seed) depth).2)).trans (congrArg next ih)

theorem admitted_target {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : target = trajectory seed history.length :=
  (congrArg Sigma.fst (build history admitted).exact).symm.trans
    ((congrArg Sigma.fst (build_run history admitted)).trans (run_trajectory seed history.length))

theorem advance_history_length {seed : Nat} (frame : Frame seed) :
    (advance frame).2.history.length = frame.2.history.length + 1 := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> simp only [advance] <;> rfl

theorem run_history_length {seed : Nat} (first : Frame seed) (depth : Nat) :
    (run first depth).1.2.history.length = first.2.history.length + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      exact (advance_history_length (run first depth).1).trans
        ((congrArg (fun length => length + 1) ih).trans (Nat.add_assoc _ _ _))

theorem admitted_supports_unbounded (seed bound : Nat) :
    ∃ target : State, ∃ history : History Step (.ready seed) target,
      ∃ admitted : Admissible history, bound < (complete history admitted).resources.length := by
  let actual := run (initial seed) bound
  have admitted := execution_admitted actual.2
  refine ⟨actual.1.1, actual.1.2.history, admitted, ?_⟩
  have length : actual.1.2.history.length = bound :=
    (run_history_length (initial seed) bound).trans (Nat.zero_add _)
  rw [complete_size, length, Nat.add_comm 1 bound]
  exact Nat.lt_succ_self _

theorem admissible_append {source middle target : State} (one : History Step source middle)
    (two : History Step middle target) : Admissible (History.append one two) ↔ Admissible one ∧ Admissible two := by
  induction two with
  | root => exact ⟨fun admitted => ⟨admitted, True.intro⟩, fun admitted => admitted.1⟩
  | extend previous step ih =>
      constructor
      · intro admitted
        have prior := ih.mp admitted.1
        exact ⟨prior.1, prior.2, admitted.2⟩
      · intro admitted
        exact ⟨ih.mpr ⟨admitted.1, admitted.2.1⟩, admitted.2.2⟩

/-- Resume the supplied realization; reconstruction of the prefix is used only in the erased proof. -/
def resumeFrom {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (prior : Realization history)
    (following : History Step middle target) (allowed : Admissible following) :
    Realization (History.append history following) :=
  let further := run prior.frame following.length
  have same : further.1 = specified (History.append history following) := by
    let combined := build (History.append history following) ((admissible_append history following).mpr ⟨admitted, allowed⟩)
    have all := build_run (History.append history following) ((admissible_append history following).mpr ⟨admitted, allowed⟩)
    rw [History.length_append] at all
    have prefixSame : prior.frame = (build history admitted).frame :=
      prior.exact.trans (build history admitted).exact.symm
    exact (((congrArg (fun frame => (run frame following.length).1) (prefixSame.trans (build_run history admitted))).trans
      (run_add (initial seed) _ _).symm).trans all.symm).trans combined.exact
  ⟨further.1, prior.execution.compose further.2, same⟩

def resume {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (following : History Step middle target) (allowed : Admissible following) :
    Realization (History.append history following) := resumeFrom history admitted (build history admitted) following allowed

def resumeCompleteFrom {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (prior : Realization history)
    (following : History Step middle target) (allowed : Admissible following) :
    CompleteRealization (History.append history following) :=
  certify _ ((admissible_append history following).mpr ⟨admitted, allowed⟩) (resumeFrom history admitted prior following allowed)

def resumeComplete {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (following : History Step middle target) (allowed : Admissible following) :
    CompleteRealization (History.append history following) :=
  resumeCompleteFrom history admitted (build history admitted) following allowed

def resumeResourcesFrom {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (prior : Realization history)
    (following : History Step middle target) (allowed : Admissible following) :
    Extension prior.frame.2.support (resumeFrom history admitted prior following allowed).frame.2.support :=
  (run prior.frame following.length).2.resources

def resumeResources {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (following : History Step middle target) (allowed : Admissible following) :
    Extension (build history admitted).frame.2.support (resume history admitted following allowed).frame.2.support :=
  resumeResourcesFrom history admitted (build history admitted) following allowed

theorem resumeFrom_certified_old {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (prior : Realization history)
    (following : History Step middle target) (allowed : Admissible following)
    (kind : Kind) (ref : Ref (declaredContext history) kind) :
    (resumeFrom history admitted prior following allowed).frame.2.support.read kind
        ((resumeResourcesFrom history admitted prior following allowed).embed kind
          ((coordinates history prior.frame prior.exact kind).forward ref)) = expected history kind ref :=
  ((resumeResourcesFrom history admitted prior following allowed).read_preserved _ _).trans
    (coordinate_certified history admitted prior.frame prior.exact kind ref)

theorem resume_certified_old {seed : Nat} {middle target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (following : History Step middle target) (allowed : Admissible following)
    (kind : Kind) (ref : Ref (declaredContext history) kind) :
    (resume history admitted following allowed).frame.2.support.read kind
        ((resumeResources history admitted following allowed).embed kind ((complete history admitted).coordinates kind |>.forward ref)) =
      expected history kind ref :=
  ((resumeResources history admitted following allowed).read_preserved _ _).trans ((complete history admitted).certified kind ref)

theorem resume_compose {seed : Nat} {middle nextState target : State} (history : History Step (.ready seed) middle)
    (admitted : Admissible history) (one : History Step middle nextState) (two : History Step nextState target)
    (allowedOne : Admissible one) (allowedTwo : Admissible two) :
    (resume history admitted (History.append one two) ((admissible_append one two).mpr ⟨allowedOne, allowedTwo⟩)).frame =
      (run (resume history admitted one allowedOne).frame two.length).1 := by
  change (run (build history admitted).frame (History.append one two).length).1 = _
  rw [History.length_append]
  exact run_add _ _ _

def localDecision {source target : State} (step : Step source target) : Decidable (LocalAdmission step) :=
  match step with
  | .observe number flag => inferInstanceAs (Decidable (flag = TypedResources.test number))
  | .act number flag selected result =>
      inferInstanceAs (Decidable (selected = flag ∧ result = TypedResources.adjust flag number))
  | .reuse number result => inferInstanceAs (Decidable (result = number))

def admissionDecision {source : State} : {target : State} → (history : History Step source target) → Decidable (Admissible history)
  | _, .root => .isTrue True.intro
  | _, .extend previous step => match admissionDecision previous with
      | .isFalse rejected => .isFalse (fun admitted => rejected admitted.1)
      | .isTrue prior => match localDecision step with
          | .isFalse rejected => .isFalse (fun admitted => rejected admitted.2)
          | .isTrue allowed => .isTrue ⟨prior, allowed⟩
termination_by structural _ history => history

def checkAdmission {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    Decidable (Admissible history) → CompleteRealization history ⊕ PLift (¬ Admissible history)
  | .isTrue admitted => .inl (complete history admitted)
  | .isFalse rejected => .inr ⟨rejected⟩

def check {seed : Nat} {target : State} (history : History Step (.ready seed) target) :
    CompleteRealization history ⊕ PLift (¬ Admissible history) := checkAdmission history (admissionDecision history)

theorem check_complete {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (admitted : Admissible history) : ∃ result, check history = .inl result := by
  cases decision : admissionDecision history with
  | isTrue allowed => exact ⟨complete history allowed, congrArg (checkAdmission history) decision⟩
  | isFalse rejected => exact False.elim (rejected admitted)

theorem check_rejects {seed : Nat} {target : State} (history : History Step (.ready seed) target)
    (rejected : ¬ Admissible history) : ∃ reason, check history = .inr ⟨reason⟩ := by
  cases decision : admissionDecision history with
  | isTrue allowed => exact False.elim (rejected allowed)
  | isFalse reason => exact ⟨reason, congrArg (checkAdmission history) decision⟩

end RelationalFoundations.HeterogeneousFeedback
