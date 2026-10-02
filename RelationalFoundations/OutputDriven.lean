import RelationalFoundations.ResourceGraph
import RelationalFoundations.Cardinalization
set_option genInjectivity false

/-!
# Outputs produce operational succession

The driver supplies two effective local procedures: proposing a finite
expression over existing resources and reacting to its produced output by
constructing a typed step. The executor supplies that actual output to the
reaction. No complete operational history is an input to `run`.

These local procedures are primitive data. The general executor does not
claim that a value alone determines a transition independently of its rule.
-/

namespace RelationalFoundations.OutputDriven
open ResourceGraph
universe u v w
variable {Token : Type u} {State : Type v} {Step : State → State → Type w} {source : State}

structure Frame (Token : Type u) {State : Type v} (Step : State → State → Type w) (source : State) where
  target : State
  history : History Step source target
  layout : Layout
  support : Support Token layout
  focus : Address layout

namespace Frame
def initial (Token : Type u) {State : Type v} (Step : State → State → Type w) (source : State) :
    Frame Token Step source where
  target := source
  history := .root
  layout := .initial .leaf
  support := .initial .empty
  focus := .initial .root

def output (frame : Frame Token Step source) : List Token := frame.support.read frame.focus
end Frame

structure Rule (Token : Type u) {State : Type v} (Step : State → State → Type w) (source : State) where
  plan : (frame : Frame Token Step source) → (shape : Shape) × Expr Token (Address frame.layout) shape
  react : (frame : Frame Token Step source) → List Token → (target : State) × Step frame.target target

namespace Rule
def produced (rule : Rule Token Step source) (frame : Frame Token Step source) : List Token :=
  (rule.plan frame).2.eval frame.support.read

def advance (rule : Rule Token Step source) (frame : Frame Token Step source) : Frame Token Step source :=
  let request := rule.plan frame
  let reaction := rule.react frame (rule.produced frame)
  { target := reaction.1
    history := .extend frame.history reaction.2
    layout := .extend frame.layout request.1
    support := .extend frame.support request.2
    focus := .fresh .root }

theorem advance_output (rule : Rule Token Step source) (frame : Frame Token Step source) :
    (rule.advance frame).output = rule.produced frame := (rule.plan frame).2.readAt_root _

/-- The witness in the new history is constructed by reacting to the realized output. -/
theorem advance_history (rule : Rule Token Step source) (frame : Frame Token Step source) :
    (rule.advance frame).history = .extend frame.history (rule.react frame (rule.produced frame)).2 := rfl
end Rule

inductive Execution (rule : Rule Token Step source) (first : Frame Token Step source) :
    Frame Token Step source → Type (max u v w) where
  | idle : Execution rule first first
  | step {middle : Frame Token Step source} : Execution rule first middle →
      Execution rule first (rule.advance middle)

namespace Execution
variable {rule : Rule Token Step source} {first second third : Frame Token Step source}

def length : {last : Frame Token Step source} → Execution rule first last → Nat
  | _, .idle => 0
  | _, .step previous => previous.length + 1

def continuation : {last : Frame Token Step source} → (execution : Execution rule first last) →
    History Step first.target last.target
  | _, .idle => .root
  | _, .step (middle := middle) previous =>
      .extend previous.continuation (rule.react middle (rule.produced middle)).2

def resources : {last : Frame Token Step source} → (execution : Execution rule first last) →
    Extension first.support last.support
  | _, .idle => .refl
  | _, .step (middle := middle) previous => .step previous.resources (rule.plan middle).2

def embed (execution : Execution rule first second) : Address first.layout → Address second.layout :=
  execution.resources.embed

theorem history_exact (execution : Execution rule first second) :
    History.append first.history execution.continuation = second.history := by
  induction execution with
  | idle => rfl
  | step previous ih => exact congrArg (fun h => History.extend h _) ih

theorem history_length (execution : Execution rule first second) :
    second.history.length = first.history.length + execution.length := by
  induction execution with
  | idle => rfl
  | step previous ih =>
      exact (congrArg (fun n => n + 1) ih).trans (Nat.add_assoc _ _ _)

theorem finite_growth (execution : Execution rule first second) :
    first.layout.size + execution.length ≤ second.layout.size := by
  induction execution with
  | idle => exact Nat.le_refl _
  | step previous ih =>
      change first.layout.size + (previous.length + 1) ≤ _ + _
      exact (Nat.add_assoc _ _ _).symm ▸
        Nat.add_le_add ih (Nat.succ_le_of_lt (Shape.size_positive _))

theorem embed_injective (execution : Execution rule first second) : Function.Injective execution.embed :=
  execution.resources.embed_injective

theorem read_preserved (execution : Execution rule first second) (address : Address first.layout) :
    second.support.read (execution.embed address) = first.support.read address :=
  execution.resources.read_preserved address

theorem node_preserved (execution : Execution rule first second) (address : Address first.layout) :
    second.support.nodeAt (execution.embed address) = (first.support.nodeAt address).map execution.embed :=
  execution.resources.node_preserved address

theorem relation_preserved (execution : Execution rule first second) {parent child : Address first.layout}
    (related : first.support.Depends parent child) :
    second.support.Depends (execution.embed parent) (execution.embed child) :=
  execution.resources.relation_preserved related

theorem relation_reflected (execution : Execution rule first second) {parent child : Address first.layout}
    (related : second.support.Depends (execution.embed parent) (execution.embed child)) :
    first.support.Depends parent child := execution.resources.relation_reflected related

def compose (initial : Execution rule first second) : {last : Frame Token Step source} →
    Execution rule second last → Execution rule first last
  | _, .idle => initial
  | _, .step previous => .step (compose initial previous)

theorem continuation_compose (initial : Execution rule first second) (following : Execution rule second third) :
    (initial.compose following).continuation = History.append initial.continuation following.continuation := by
  induction following with
  | idle => rfl
  | step previous ih => exact congrArg (fun h => History.extend h _) ih

theorem resources_compose (initial : Execution rule first second) (following : Execution rule second third) :
    (initial.compose following).resources = initial.resources.compose following.resources := by
  induction following with
  | idle => rfl
  | step previous ih => exact congrArg (fun prior => Extension.step prior _) ih

theorem embed_compose (initial : Execution rule first second) (following : Execution rule second third)
    (address : Address first.layout) :
    (initial.compose following).embed address = following.embed (initial.embed address) :=
  (congrArg (fun growth => Extension.embed growth address) (resources_compose initial following)).trans
    (Extension.embed_compose _ _ _)

theorem compose_associative {fourth : Frame Token Step source}
    (one : Execution rule first second) (two : Execution rule second third) (three : Execution rule third fourth) :
    (one.compose two).compose three = one.compose (two.compose three) := by
  induction three with
  | idle => rfl
  | step previous ih => exact congrArg Execution.step ih
end Execution

namespace Rule
def run (rule : Rule Token Step source) (first : Frame Token Step source) :
    Nat → (last : Frame Token Step source) × Execution rule first last
  | 0 => ⟨first, .idle⟩
  | depth + 1 =>
      let previous := rule.run first depth
      ⟨rule.advance previous.1, .step previous.2⟩

theorem run_length (rule : Rule Token Step source) (first : Frame Token Step source) (depth : Nat) :
    (rule.run first depth).2.length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact congrArg Nat.succ ih

/-- The finite scheduling input controls operational length, not semantic closure. -/
theorem run_history_length (rule : Rule Token Step source) (first : Frame Token Step source) (depth : Nat) :
    (rule.run first depth).1.history.length = first.history.length + depth :=
  ((rule.run first depth).2.history_length).trans (congrArg (Nat.add first.history.length) (rule.run_length first depth))

/-- Splitting the schedule preserves the complete frame, including history and support. -/
theorem run_add (rule : Rule Token Step source) (first : Frame Token Step source) (firstDepth secondDepth : Nat) :
    (rule.run first (firstDepth + secondDepth)).1 = (rule.run (rule.run first firstDepth).1 secondDepth).1 := by
  induction secondDepth with
  | zero => rfl
  | succ secondDepth ih => exact congrArg rule.advance ih
end Rule

end RelationalFoundations.OutputDriven
