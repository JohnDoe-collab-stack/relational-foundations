import RelationalFoundations.ResourceGraph
import RelationalFoundations.Cardinalization
set_option genInjectivity false

/-!
Uniform construction from finite local resource fragments. The contract contains
origin data and one-step laws only. In particular, neither a complete support
for a history nor a global coverage or correctness theorem is a parameter.
Different backends may implement different typed reference and operator syntax.
-/

namespace RelationalFoundations.FiniteRuleConstruction
open ResourceGraph DemandClosure
universe u

def Packed {Kind : Type} (Ref : Kind → Type) := (kind : Kind) × Ref kind

theorem list_id {A : Type} (items : List A) : items.map id = items := by
  induction items with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

def rename {Kind : Type} {A B : Kind → Type} (f : ∀ kind, A kind → B kind) : Packed A → Packed B
  | ⟨kind, ref⟩ => ⟨kind, f kind ref⟩

theorem rename_comp {Kind : Type} {A B C : Kind → Type}
    (one : ∀ kind, A kind → B kind) (two : ∀ kind, B kind → C kind) (ref : Packed A) :
    rename two (rename one ref) = rename (fun kind ref => two kind (one kind ref)) ref := by
  cases ref
  rfl

theorem rename_injective {Kind : Type} {A B : Kind → Type} (f : ∀ kind, A kind → B kind)
    (injective : ∀ kind, Function.Injective (f kind)) : Function.Injective (rename f) := by
  intro one two same
  cases one with
  | mk kind one =>
      cases two with
      | mk other two =>
          obtain ⟨sortSame, refsSame⟩ := Sigma.mk.inj same
          cases sortSame
          exact congrArg (Sigma.mk kind) (injective kind (eq_of_heq refsSame))

def sumLeft {A B C : Type} (one : ExactTransport A B) : ExactTransport (A ⊕ C) (B ⊕ C) where
  forward := fun value => match value with | .inl old => .inl (one.forward old) | .inr fresh => .inr fresh
  backward := fun value => match value with | .inl old => .inl (one.backward old) | .inr fresh => .inr fresh
  forwardBackward := fun value => by
    cases value with
    | inl old => exact congrArg Sum.inl (one.forwardBackward old)
    | inr _ => rfl
  backwardForward := fun value => by
    cases value with
    | inl old => exact congrArg Sum.inl (one.backwardForward old)
    | inr _ => rfl

structure Finite (A : Type) where
  items : List A
  exhaustive : ∀ a, a ∈ items
  unique : items.Nodup

structure Rules where
  State : Type u
  Step : State → State → Type u
  origin : State
  allowed : {a b : State} → Step a b → Prop
  Kind : Type
  Value : Kind → Type u
  Initial : Kind → Type
  New : {a b : State} → Step a b → Kind → Type
  initialExpected : ∀ kind, Initial kind → Value kind
  newExpected : {a b : State} → (step : Step a b) → ∀ kind, New step kind → Value kind
  initialFinite : Finite (Packed Initial)
  newFinite : {a b : State} → (step : Step a b) → Finite (Packed (New step))
  Frame : Type u
  recorded : Frame → (target : State) × History Step origin target
  Ref : Frame → Kind → Type
  Node : Frame → Kind → Type u
  read : (frame : Frame) → ∀ kind, Ref frame kind → Value kind
  node : (frame : Frame) → ∀ kind, Ref frame kind → Node frame kind
  inputs : {frame : Frame} → {kind : Kind} → Node frame kind → List (Packed (Ref frame))
  eval : {frame : Frame} → (∀ kind, Ref frame kind → Value kind) → {kind : Kind} → Node frame kind → Value kind
  map : {a b : Frame} → (∀ kind, Ref a kind → Ref b kind) → {kind : Kind} → Node a kind → Node b kind
  map_id : {a : Frame} → {kind : Kind} → (node : Node a kind) → map (fun _ r => r) node = node
  map_comp : {a b c : Frame} → (one : ∀ kind, Ref a kind → Ref b kind) →
    (two : ∀ kind, Ref b kind → Ref c kind) → {kind : Kind} → (node : Node a kind) →
    map two (map one node) = map (fun kind ref => two kind (one kind ref)) node
  inputs_map : {a b : Frame} → (f : ∀ kind, Ref a kind → Ref b kind) → {kind : Kind} →
    (node : Node a kind) → inputs (map f node) = (inputs node).map (rename f)
  eval_map : {a b : Frame} → (f : ∀ kind, Ref a kind → Ref b kind) →
    (read : ∀ kind, Ref b kind → Value kind) → {kind : Kind} → (node : Node a kind) →
    eval read (map f node) = eval (fun kind ref => read kind (f kind ref)) node
  eval_congr : {a : Frame} → (one two : ∀ kind, Ref a kind → Value kind) →
    (same : ∀ kind ref, one kind ref = two kind ref) → {kind : Kind} → (node : Node a kind) →
    eval one node = eval two node
  initial : Frame
  initial_recorded : recorded initial = ⟨origin, .root⟩
  initialCoordinates : ∀ kind, ExactTransport (Initial kind) (Ref initial kind)
  initial_values : ∀ kind slot, read initial kind ((initialCoordinates kind).forward slot) = initialExpected kind slot
  initial_rules : ∀ kind ref, read initial kind ref = eval (read initial) (node initial kind ref)
  valid : Frame → Prop
  initial_valid : valid initial
  advance : Frame → Frame
  Result : Frame → Type u
  produce : (frame : Frame) → Result frame
  react : (frame : Frame) → Result frame → (target : State) × Step (recorded frame).1 target
  advance_recorded : ∀ frame, recorded (advance frame) =
    ⟨(react frame (produce frame)).1, .extend (recorded frame).2 (react frame (produce frame)).2⟩
  advance_valid : ∀ frame, valid frame → valid (advance frame)
  reaction_allowed : ∀ frame, valid frame → allowed (react frame (produce frame)).2
  reaction_exact : ∀ frame, valid frame → {target : State} → (step : Step (recorded frame).1 target) →
    allowed step → react frame (produce frame) = ⟨target, step⟩
  split : ∀ frame kind, ExactTransport
    (Ref frame kind ⊕ New (react frame (produce frame)).2 kind) (Ref (advance frame) kind)
  old_values : ∀ frame kind ref,
    read (advance frame) kind ((split frame kind).forward (.inl ref)) = read frame kind ref
  old_nodes : ∀ frame kind ref,
    node (advance frame) kind ((split frame kind).forward (.inl ref)) =
      map (fun kind ref => (split frame kind).forward (.inl ref)) (node frame kind ref)
  new_values : ∀ frame, valid frame → ∀ kind slot,
    read (advance frame) kind ((split frame kind).forward (.inr slot)) = newExpected (react frame (produce frame)).2 kind slot
  new_rules : ∀ frame kind slot,
    read (advance frame) kind ((split frame kind).forward (.inr slot)) =
      eval (read (advance frame)) (node (advance frame) kind ((split frame kind).forward (.inr slot)))
  visible : Frame → State
  visible_valid : ∀ frame, valid frame → visible frame = (recorded frame).1

namespace Rules
variable (rules : Rules.{u})

def reaction (frame : rules.Frame) := rules.react frame (rules.produce frame)

def Admissible {source : rules.State} : {target : rules.State} → History rules.Step source target → Prop
  | _, .root => True
  | _, .extend previous step => Admissible previous ∧ rules.allowed step
termination_by structural _ history => history

/-- Demands depend on origin slots and supplied step witnesses, before execution. -/
def Requests : {target : rules.State} → History rules.Step rules.origin target → rules.Kind → Type
  | _, .root, kind => rules.Initial kind
  | _, .extend previous step, kind => Requests previous kind ⊕ rules.New step kind
termination_by structural _ history _ => history

def expected (rules : Rules.{u}) : {target : rules.State} → (history : History rules.Step rules.origin target) →
    ∀ kind, rules.Requests history kind → rules.Value kind
  | _, .root, kind, slot => rules.initialExpected kind slot
  | _, .extend previous step, kind, request => match request with
      | .inl old => rules.expected previous kind old
      | .inr slot => rules.newExpected step kind slot
termination_by structural _ history _ _ => history

def old (frame : rules.Frame) (kind : rules.Kind) (ref : rules.Ref frame kind) : rules.Ref (rules.advance frame) kind :=
  (rules.split frame kind).forward (.inl ref)

theorem old_injective (frame : rules.Frame) (kind : rules.Kind) : Function.Injective (rules.old frame kind) := by
  intro a b same
  have both := congrArg (rules.split frame kind).backward same
  have eq : Sum.inl a = Sum.inl b :=
    ((rules.split frame kind).forwardBackward (.inl a)).symm.trans
      (both.trans ((rules.split frame kind).forwardBackward (.inl b)))
  cases eq
  rfl

theorem old_new_distinct (frame : rules.Frame) (kind : rules.Kind) (old : rules.Ref frame kind)
    (fresh : rules.New (rules.reaction frame).2 kind) :
    rules.old frame kind old ≠ (rules.split frame kind).forward (.inr fresh) := by
  intro same
  have impossible := ((rules.split frame kind).forwardBackward (.inl old)).symm.trans
    ((congrArg (rules.split frame kind).backward same).trans ((rules.split frame kind).forwardBackward (.inr fresh)))
  cases impossible

def Certified (frame : rules.Frame) := ∀ kind ref,
  rules.read frame kind ref = rules.eval (rules.read frame) (rules.node frame kind ref)

theorem advance_certified (frame : rules.Frame) (prior : rules.Certified frame) : rules.Certified (rules.advance frame) := by
  intro kind ref
  have back := (rules.split frame kind).backwardForward ref
  cases located : (rules.split frame kind).backward ref with
  | inl old =>
      have mapped :=  congrArg (rules.split frame kind).forward located
      have same := mapped.symm.trans back
      rw [← same, rules.old_values, rules.old_nodes, rules.eval_map]
      exact (prior kind old).trans (rules.eval_congr _ _ (fun k r => (rules.old_values frame k r).symm) _)
  | inr slot =>
      have mapped :=  congrArg (rules.split frame kind).forward located
      exact (congrArg (fun ref => rules.read (rules.advance frame) kind ref =
        rules.eval (rules.read (rules.advance frame)) (rules.node (rules.advance frame) kind ref))
        (mapped.symm.trans back)) ▸ rules.new_rules frame kind slot

structure Coverage {target : rules.State} (history : History rules.Step rules.origin target) (frame : rules.Frame) where
  coordinates : ∀ kind, ExactTransport (rules.Requests history kind) (rules.Ref frame kind)
  values : ∀ kind request, rules.read frame kind ((coordinates kind).forward request) = rules.expected history kind request

def initialCoverage : rules.Coverage (.root : History rules.Step rules.origin rules.origin) rules.initial :=
  ⟨rules.initialCoordinates, fun kind slot => rules.initial_values kind slot⟩

def growCoverage (frame : rules.Frame) (valid : rules.valid frame)
    (prior : rules.Coverage (rules.recorded frame).2 frame) :
    rules.Coverage (.extend (rules.recorded frame).2 (rules.reaction frame).2) (rules.advance frame) where
  coordinates := fun kind => (sumLeft (prior.coordinates kind)).compose (rules.split frame kind)
  values := fun kind request => by
    cases request with
    | inl old => exact (rules.old_values frame kind _).trans (prior.values kind old)
    | inr slot => exact rules.new_values frame valid kind slot

def recordedCoverage (frame : rules.Frame) (valid : rules.valid frame)
    (prior : rules.Coverage (rules.recorded frame).2 frame) :
    rules.Coverage (rules.recorded (rules.advance frame)).2 (rules.advance frame) :=
  (congrArg (fun record => rules.Coverage record.2 (rules.advance frame)) (rules.advance_recorded frame)).symm ▸
    rules.growCoverage frame valid prior

def requestFinite (rules : Rules.{u}) : {target : rules.State} → (history : History rules.Step rules.origin target) → Finite (Packed (rules.Requests history))
  | _, .root => rules.initialFinite
  | _, .extend previous step =>
      let left : Packed (rules.Requests previous) → Packed (rules.Requests (.extend previous step)) := rename (fun _ => Sum.inl)
      let right : Packed (rules.New step) → Packed (rules.Requests (.extend previous step)) := rename (fun _ => Sum.inr)
      { items := (rules.requestFinite previous).items.map left ++ (rules.newFinite step).items.map right
        exhaustive := fun ⟨kind, request⟩ => by
          cases request with
          | inl old => exact List.mem_append_left _ (FiniteList.mappedMember left ((rules.requestFinite previous).exhaustive ⟨kind, old⟩))
          | inr slot => exact List.mem_append_right _ (FiniteList.mappedMember right ((rules.newFinite step).exhaustive ⟨kind, slot⟩))
        unique := by
          apply Enumeration.nodup_append
            (Enumeration.nodup_map left (rename_injective _ (fun _ _ _ same => by cases same; rfl)) (rules.requestFinite previous).unique)
            (Enumeration.nodup_map right (rename_injective _ (fun _ _ _ same => by cases same; rfl)) (rules.newFinite step).unique)
          intro one oneMem two twoMem same
          obtain ⟨⟨k, old⟩, _, oldAt⟩ := Enumeration.map_origin left _ oneMem
          obtain ⟨⟨j, slot⟩, _, newAt⟩ := Enumeration.map_origin right _ twoMem
          have impossible := oldAt.trans (same.trans newAt.symm)
          cases impossible }
termination_by structural _ history => history

inductive Execution (rules : Rules.{u}) (first : rules.Frame) : rules.Frame → Type u where
  | idle : rules.Execution first first
  | step {middle : rules.Frame} : rules.Execution first middle → rules.Execution first (rules.advance middle)

namespace Execution
variable {rules} {a b c : rules.Frame}

theorem valid : {last : rules.Frame} → rules.Execution rules.initial last → rules.valid last
  | _, .idle => rules.initial_valid
  | _, .step (middle := middle) previous => rules.advance_valid middle previous.valid

theorem certified : {last : rules.Frame} → rules.Execution rules.initial last → rules.Certified last
  | _, .idle => rules.initial_rules
  | _, .step (middle := middle) previous => rules.advance_certified middle previous.certified

def coverage : {last : rules.Frame} → rules.Execution rules.initial last → rules.Coverage (rules.recorded last).2 last
  | _, .idle => (congrArg (fun record => rules.Coverage record.2 rules.initial) rules.initial_recorded).symm ▸ rules.initialCoverage
  | _, .step (middle := middle) previous => rules.recordedCoverage middle previous.valid previous.coverage

theorem admissible : {last : rules.Frame} → (execution : rules.Execution rules.initial last) → rules.Admissible (rules.recorded last).2
  | _, .idle => (congrArg (fun record => rules.Admissible record.2) rules.initial_recorded).symm ▸ True.intro
  | _, .step (middle := middle) previous =>
      (congrArg (fun record => rules.Admissible record.2) (rules.advance_recorded middle)).symm ▸
        ⟨previous.admissible, rules.reaction_allowed middle previous.valid⟩

def compose (one : rules.Execution a b) : {last : rules.Frame} → rules.Execution b last → rules.Execution a last
  | _, .idle => one
  | _, .step previous => .step (compose one previous)

def embed : {last : rules.Frame} → rules.Execution a last → ∀ kind, rules.Ref a kind → rules.Ref last kind
  | _, .idle, _, ref => ref
  | _, .step (middle := middle) previous, kind, ref => rules.old middle kind (embed previous kind ref)

theorem embed_injective (execution : rules.Execution a b) (kind : rules.Kind) : Function.Injective (execution.embed kind) := by
  induction execution with
  | idle => exact fun _ _ same => same
  | step previous ih => exact fun _ _ same => ih (rules.old_injective _ kind same)

theorem values_preserved (execution : rules.Execution a b) (kind : rules.Kind) (ref : rules.Ref a kind) :
    rules.read b kind (execution.embed kind ref) = rules.read a kind ref := by
  induction execution with
  | idle => rfl
  | step previous ih => exact (rules.old_values _ kind _).trans ih

theorem nodes_preserved (execution : rules.Execution a b) (kind : rules.Kind) (ref : rules.Ref a kind) :
    rules.node b kind (execution.embed kind ref) = rules.map execution.embed (rules.node a kind ref) := by
  induction execution with
  | idle => exact (rules.map_id _).symm
  | step previous ih => exact (rules.old_nodes _ kind _).trans ((congrArg (rules.map (rules.old _)) ih).trans (rules.map_comp _ _ _))

theorem dependencies_preserved (execution : rules.Execution a b) (kind : rules.Kind) (ref : rules.Ref a kind) :
    rules.inputs (rules.node b kind (execution.embed kind ref)) =
      (rules.inputs (rules.node a kind ref)).map (rename execution.embed) :=
  (congrArg rules.inputs (execution.nodes_preserved kind ref)).trans (rules.inputs_map _ _)

theorem embed_compose (one : rules.Execution a b) (two : rules.Execution b c) (kind : rules.Kind) (ref : rules.Ref a kind) :
    (one.compose two).embed kind ref = two.embed kind (one.embed kind ref) := by
  induction two with
  | idle => rfl
  | step previous ih => exact congrArg (rules.old _ kind) ih

theorem compose_associative {d : rules.Frame} (one : rules.Execution a b) (two : rules.Execution b c) (three : rules.Execution c d) :
    (one.compose two).compose three = one.compose (two.compose three) := by
  induction three with
  | idle => rfl
  | step previous ih => exact congrArg Execution.step ih
end Execution

structure Realization {target : rules.State} (history : History rules.Step rules.origin target) where
  frame : rules.Frame
  execution : rules.Execution rules.initial frame
  exact : rules.recorded frame = ⟨target, history⟩

def extendRecord (record : (target : rules.State) × History rules.Step rules.origin target)
    (step : (target : rules.State) × rules.Step record.1 target) :
    (target : rules.State) × History rules.Step rules.origin target := ⟨step.1, .extend record.2 step.2⟩

theorem advance_exact (frame : rules.Frame) (valid : rules.valid frame)
    (record : (target : rules.State) × History rules.Step rules.origin target)
    (same : rules.recorded frame = record) {target : rules.State}
    (step : rules.Step record.1 target) (allowed : rules.allowed step) :
    rules.recorded (rules.advance frame) = ⟨target, .extend record.2 step⟩ := by
  cases same
  exact (rules.advance_recorded frame).trans
    (congrArg (rules.extendRecord (rules.recorded frame)) (rules.reaction_exact frame valid step allowed))

def build (rules : Rules.{u}) : {target : rules.State} → (history : History rules.Step rules.origin target) → rules.Admissible history → rules.Realization history
  | _, .root, _ => ⟨rules.initial, .idle, rules.initial_recorded⟩
  | _, .extend previous step, admitted =>
      let prior := rules.build previous admitted.1
      have exact : rules.recorded (rules.advance prior.frame) = ⟨_, .extend previous step⟩ :=
        rules.advance_exact prior.frame prior.execution.valid ⟨_, previous⟩ prior.exact step admitted.2
      ⟨rules.advance prior.frame, .step prior.execution, exact⟩
termination_by structural _ history _ => history

structure Complete {target : rules.State} (history : History rules.Step rules.origin target) where
  realization : rules.Realization history
  coverage : rules.Coverage history realization.frame
  certified : rules.Certified realization.frame
  resources : Finite (Packed (rules.Ref realization.frame))
  terminal : rules.visible realization.frame = target

def certify {target : rules.State} (history : History rules.Step rules.origin target) (actual : rules.Realization history) : rules.Complete history :=
  let cov : rules.Coverage history actual.frame :=
    (congrArg (fun record => rules.Coverage record.2 actual.frame) actual.exact) ▸ actual.execution.coverage
  let forward := rename (fun kind => (cov.coordinates kind).forward)
  let backward := rename (fun kind => (cov.coordinates kind).backward)
  { realization := actual
    coverage := cov
    certified := actual.execution.certified
    resources :=
      { items := (rules.requestFinite history).items.map forward
        exhaustive := fun ref => by
          have mapped :=  FiniteList.mappedMember forward ((rules.requestFinite history).exhaustive (backward ref))
          cases ref with
          | mk kind ref => exact ((congrArg (Sigma.mk kind) ((cov.coordinates kind).backwardForward ref))) ▸ mapped
        unique := Enumeration.nodup_map forward
          (rename_injective _ (fun kind a b same =>
            ((cov.coordinates kind).forwardBackward a).symm.trans
              ((congrArg (cov.coordinates kind).backward same).trans ((cov.coordinates kind).forwardBackward b))))
          (rules.requestFinite history).unique }
    terminal := (rules.visible_valid actual.frame actual.execution.valid).trans (congrArg Sigma.fst actual.exact) }

def complete {target : rules.State} (history : History rules.Step rules.origin target) (admitted : rules.Admissible history) : rules.Complete history :=
  rules.certify history (rules.build history admitted)

theorem coverage_iff {target : rules.State} (history : History rules.Step rules.origin target) :
    rules.Admissible history ↔ Nonempty (rules.Complete history) :=
  ⟨fun admitted => ⟨rules.complete history admitted⟩, fun ⟨actual⟩ =>
    (congrArg (fun record => rules.Admissible record.2) actual.realization.exact) ▸ actual.realization.execution.admissible⟩

def run (rules : Rules.{u}) (first : rules.Frame) : Nat → (last : rules.Frame) × rules.Execution first last
  | 0 => ⟨first, .idle⟩
  | depth + 1 => let prior := rules.run first depth; ⟨rules.advance prior.1, .step prior.2⟩

theorem run_add (first : rules.Frame) (one two : Nat) : (rules.run first (one + two)).1 = (rules.run (rules.run first one).1 two).1 := by
  induction two with
  | zero => rfl
  | succ two ih => exact congrArg rules.advance ih

theorem build_run {target : rules.State} (history : History rules.Step rules.origin target) (admitted : rules.Admissible history) :
    (rules.build history admitted).frame = (rules.run rules.initial history.length).1 := by
  induction history with
  | root => rfl
  | extend previous step ih => exact congrArg rules.advance (ih admitted.1)

namespace Execution
variable {rules} {first last : rules.Frame}

def length : {last : rules.Frame} → rules.Execution first last → Nat
  | _, .idle => 0
  | _, .step previous => previous.length + 1

def continuation : {last : rules.Frame} → rules.Execution first last → History rules.Step (rules.recorded first).1 (rules.recorded last).1
  | _, .idle => .root
  | _, .step (middle := middle) previous =>
      (congrArg (fun record : (target : rules.State) × History rules.Step rules.origin target => History rules.Step (rules.recorded first).1 record.1) (rules.advance_recorded middle)).symm ▸
        .extend previous.continuation (rules.reaction middle).2

theorem append_transport {a b c : rules.State} (one : History rules.Step rules.origin a)
    (two : History rules.Step a b) (combined : History rules.Step rules.origin b)
    (prior : History.append one two = combined) (step : rules.Step b c)
    (record : (target : rules.State) × History rules.Step rules.origin target)
    (same : record = ⟨c, .extend combined step⟩) :
    History.append one ((congrArg (fun r => History rules.Step a r.1) same).symm ▸ .extend two step) = record.2 := by
  cases same
  exact congrArg (fun h => History.extend h step) prior

theorem history_exact (execution : rules.Execution first last) :
    History.append (rules.recorded first).2 execution.continuation = (rules.recorded last).2 := by
  induction execution with
  | idle => rfl
  | @step middle previous ih =>
      exact append_transport (rules.recorded first).2 previous.continuation (rules.recorded middle).2 ih
        (rules.reaction middle).2 (rules.recorded (rules.advance middle)) (rules.advance_recorded middle)

theorem append_cast {a b : rules.State}
    {one two : (target : rules.State) × History rules.Step rules.origin target} (same : one = two)
    (first : History rules.Step a b) (last : History rules.Step b one.1) :
    ((congrArg (fun record : (target : rules.State) × History rules.Step rules.origin target => History rules.Step a record.1) same) ▸ History.append first last) =
      History.append first ((congrArg (fun record : (target : rules.State) × History rules.Step rules.origin target => History rules.Step b record.1) same) ▸ last) := by
  cases same
  rfl

theorem continuation_compose {middle : rules.Frame} (one : rules.Execution first middle) (two : rules.Execution middle last) :
    (one.compose two).continuation = History.append one.continuation two.continuation := by
  induction two with
  | idle => rfl
  | @step current previous ih =>
      exact (congrArg (fun h : History rules.Step (rules.recorded first).1 (rules.recorded current).1 =>
        (congrArg (fun record : (target : rules.State) × History rules.Step rules.origin target => History rules.Step (rules.recorded first).1 record.1) (rules.advance_recorded current)).symm ▸
          History.extend h (rules.reaction current).2) ih).trans
        (append_cast (rules.advance_recorded current).symm one.continuation (.extend previous.continuation (rules.reaction current).2))

theorem frame_run (execution : rules.Execution first last) : last = (rules.run first execution.length).1 := by
  induction execution with
  | idle => rfl
  | step previous ih => exact congrArg rules.advance ih

theorem history_length (execution : rules.Execution first last) :
    (rules.recorded last).2.length = (rules.recorded first).2.length + execution.length := by
  induction execution with
  | idle => exact (Nat.add_zero _).symm
  | @step middle previous ih =>
      exact (congrArg (fun record => record.2.length) (rules.advance_recorded middle)).trans
        ((congrArg (fun n => n + 1) ih).trans (Nat.add_assoc _ _ _))
end Execution

theorem realization_frame {target : rules.State} {history : History rules.Step rules.origin target}
    (prior : rules.Realization history) (admitted : rules.Admissible history) :
    prior.frame = (rules.build history admitted).frame := by
  have length := prior.execution.history_length
  have actualLength := congrArg (fun record => record.2.length) prior.exact
  have originLength := congrArg (fun record => record.2.length) rules.initial_recorded
  rw [actualLength, originLength] at length
  change history.length = 0 + prior.execution.length at length
  rw [Nat.zero_add] at length
  exact (prior.execution.frame_run.trans
    (congrArg (fun n => (rules.run rules.initial n).1) length.symm)).trans (rules.build_run history admitted).symm

theorem admissible_append {a b c : rules.State} (one : History rules.Step a b) (two : History rules.Step b c) :
    rules.Admissible (History.append one two) ↔ rules.Admissible one ∧ rules.Admissible two := by
  induction two with
  | root => exact ⟨fun admitted => ⟨admitted, True.intro⟩, fun admitted => admitted.1⟩
  | extend previous step ih =>
      exact ⟨fun admitted => let prior := ih.mp admitted.1; ⟨prior.1, prior.2, admitted.2⟩,
        fun admitted => ⟨ih.mpr ⟨admitted.1, admitted.2.1⟩, admitted.2.2⟩⟩

def resumeFrom {middle target : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) (prior : rules.Realization history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following) :
    rules.Realization (History.append history following) :=
  let further := rules.run prior.frame following.length
  have exact : rules.recorded further.1 = ⟨_, History.append history following⟩ := by
    have both := (rules.admissible_append history following).mpr ⟨admitted, allowed⟩
    have combined := (rules.build (History.append history following) both).exact
    have all := rules.build_run (History.append history following) both
    rw [History.length_append] at all
    have priorFrame : prior.frame = (rules.build history admitted).frame := by
      exact rules.realization_frame prior admitted
    exact (congrArg rules.recorded
      (((congrArg (fun frame => (rules.run frame following.length).1) (priorFrame.trans (rules.build_run history admitted))).trans
        (rules.run_add rules.initial _ _).symm).trans all.symm)).trans combined
  ⟨further.1, prior.execution.compose further.2, exact⟩

def resumeCompleteFrom {middle target : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) (prior : rules.Realization history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following) :
    rules.Complete (History.append history following) :=
  rules.certify _ (rules.resumeFrom history admitted prior following allowed)

def resumeExecutionFrom {middle target : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) (prior : rules.Realization history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following) :
    rules.Execution prior.frame (rules.resumeFrom history admitted prior following allowed).frame :=
  (rules.run prior.frame following.length).2

theorem resume_compose {middle next target : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) (prior : rules.Realization history)
    (one : History rules.Step middle next) (two : History rules.Step next target)
    (allowedOne : rules.Admissible one) (allowedTwo : rules.Admissible two) :
    (rules.resumeFrom history admitted prior (History.append one two)
      ((rules.admissible_append one two).mpr ⟨allowedOne, allowedTwo⟩)).frame =
    (rules.run (rules.resumeFrom history admitted prior one allowedOne).frame two.length).1 := by
  change (rules.run prior.frame (History.append one two).length).1 = _
  rw [History.length_append]
  exact rules.run_add _ _ _

def dependencies (frame : rules.Frame) : Packed (rules.Ref frame) → List (Packed (rules.Ref frame))
  | ⟨kind, ref⟩ => rules.inputs (rules.node frame kind ref)

def Depends (frame : rules.Frame) (parent child : Packed (rules.Ref frame)) := child ∈ rules.dependencies frame parent

theorem dependencies_preserved {a b : rules.Frame} (execution : rules.Execution a b) (ref : Packed (rules.Ref a)) :
    rules.dependencies b (rename execution.embed ref) = (rules.dependencies a ref).map (rename execution.embed) := by
  cases ref with | mk kind ref => exact execution.dependencies_preserved kind ref

theorem relation_preserved {a b : rules.Frame} (execution : rules.Execution a b) {parent child : Packed (rules.Ref a)}
    (related : rules.Depends a parent child) : rules.Depends b (rename execution.embed parent) (rename execution.embed child) := by
  change rename execution.embed child ∈ rules.dependencies b (rename execution.embed parent)
  rw [rules.dependencies_preserved execution parent]
  exact FiniteList.mappedMember _ related

theorem relation_reflected {a b : rules.Frame} (execution : rules.Execution a b) {parent child : Packed (rules.Ref a)}
    (related : rules.Depends b (rename execution.embed parent) (rename execution.embed child)) : rules.Depends a parent child := by
  change rename execution.embed child ∈ rules.dependencies b (rename execution.embed parent) at related
  rw [rules.dependencies_preserved execution parent] at related
  exact ResourceGraph.Extension.mapped_member_reflects _ (rename_injective _ execution.embed_injective) _ related

/-- Every ordered prerequisite has a unique declared demand; transporting it
back and forth preserves order and repeated slots as well as identities. -/
theorem dependencies_covered {target : rules.State} {history : History rules.Step rules.origin target}
    (actual : rules.Complete history) (kind : rules.Kind) (request : rules.Requests history kind) :
    let forward := rename (fun kind => (actual.coverage.coordinates kind).forward)
    let backward := rename (fun kind => (actual.coverage.coordinates kind).backward)
    ((rules.inputs (rules.node actual.realization.frame kind
      ((actual.coverage.coordinates kind).forward request))).map backward).map forward =
      rules.inputs (rules.node actual.realization.frame kind ((actual.coverage.coordinates kind).forward request)) := by
  let inputs := rules.inputs (rules.node actual.realization.frame kind ((actual.coverage.coordinates kind).forward request))
  exact (FiniteList.mapCompose _ _ inputs).trans
    ((FiniteList.mapAgree _ id (fun ⟨kind, ref⟩ =>
      congrArg (Sigma.mk kind) ((actual.coverage.coordinates kind).backwardForward ref)) inputs).trans
      (list_id inputs))

/-- Independent operational invariants are propagated using only their local
initial and successor rules, then extracted from the actual terminal view. -/
theorem extract_guarantee (P : rules.State → Nat → Prop)
    (initial : P rules.origin 0)
    (successor : ∀ {a b} (step : rules.Step a b), rules.allowed step → ∀ depth, P a depth → P b (depth + 1))
    {target : rules.State} (history : History rules.Step rules.origin target) (admitted : rules.Admissible history) :
    P (rules.visible (rules.complete history admitted).realization.frame) history.length := by
  have operational : P target history.length := by
    induction history with
    | root => exact initial
    | extend previous step ih => exact successor step admitted.2 previous.length (ih admitted.1)
  exact (congrArg (fun state => P state history.length) (rules.complete history admitted).terminal).symm ▸ operational

def fragmentSize : {target : rules.State} → History rules.Step rules.origin target → Nat
  | _, .root => rules.initialFinite.items.length
  | _, .extend previous step => fragmentSize previous + (rules.newFinite step).items.length
termination_by structural _ history => history

theorem request_count {target : rules.State} (history : History rules.Step rules.origin target) :
    (rules.requestFinite history).items.length = rules.fragmentSize history := by
  induction history with
  | root => rfl
  | extend previous step ih =>
      exact (FiniteList.appendLength _ _).trans
        ((congrArg (fun n => n + ((rules.newFinite step).items.map _).length) (FiniteList.mapLength _ _)).trans
          ((congrArg (fun n => (rules.requestFinite previous).items.length + n) (FiniteList.mapLength _ _)).trans
            (congrArg (fun n => n + (rules.newFinite step).items.length) ih)))

theorem resource_count {target : rules.State} (history : History rules.Step rules.origin target) (admitted : rules.Admissible history) :
    (rules.complete history admitted).resources.items.length = rules.fragmentSize history :=
  (FiniteList.mapLength _ _).trans (rules.request_count history)

theorem resume_expected {middle target : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) (prior : rules.Realization history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following)
    (kind : rules.Kind) (request : rules.Requests history kind) :
    rules.read (rules.resumeFrom history admitted prior following allowed).frame kind
      ((rules.resumeExecutionFrom history admitted prior following allowed).embed kind
        (((rules.certify history prior).coverage.coordinates kind).forward request)) = rules.expected history kind request :=
  ((rules.resumeExecutionFrom history admitted prior following allowed).values_preserved kind _).trans
    ((rules.certify history prior).coverage.values kind request)

def frameCoordinates {one two : rules.Frame} (same : one = two) (kind : rules.Kind) :
    ExactTransport (rules.Ref one kind) (rules.Ref two kind) :=
  ExactTransport.ofEquality (congrArg (fun frame => rules.Ref frame kind) same)

theorem frame_values {one two : rules.Frame} (same : one = two) (kind : rules.Kind) (ref : rules.Ref one kind) :
    rules.read two kind ((rules.frameCoordinates same kind).forward ref) = rules.read one kind ref := by
  cases same
  rfl

theorem frame_nodes {one two : rules.Frame} (same : one = two) (kind : rules.Kind) (ref : rules.Ref one kind) :
    rules.node two kind ((rules.frameCoordinates same kind).forward ref) =
      rules.map (fun kind => (rules.frameCoordinates same kind).forward) (rules.node one kind ref) := by
  cases same
  exact (rules.map_id _).symm

theorem frame_dependencies {one two : rules.Frame} (same : one = two) (kind : rules.Kind) (ref : rules.Ref one kind) :
    rules.inputs (rules.node two kind ((rules.frameCoordinates same kind).forward ref)) =
      (rules.inputs (rules.node one kind ref)).map (rename (fun kind => (rules.frameCoordinates same kind).forward)) :=
  (congrArg rules.inputs (rules.frame_nodes same kind ref)).trans (rules.inputs_map _ _)

end Rules
end RelationalFoundations.FiniteRuleConstruction
