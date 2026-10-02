import RelationalFoundations.OutputDriven
import RelationalFoundations.WordSupport
set_option genInjectivity false

/-!
# A complete output-driven family with actual historical reuse

For any total token choice procedure, the next expression emits the token
selected from the actual previous output and reuses its identified resource.
The produced result constructs the next typed operational witness. The proofs
cover every finite execution from the initial frame, not only sample traces.
-/

namespace RelationalFoundations.HistoricalFeedback
open ResourceGraph OutputDriven
universe u
variable {Token : Type u}

inductive Step (Token : Type u) : List Token → List Token → Type u where
  | record (previous : List Token) (token : Token) : Step Token previous (token :: previous)

abbrev Configuration (Token : Type u) := Frame Token (Step Token) []

def initial (Token : Type u) : Configuration Token := Frame.initial Token (Step Token) []

def rule (choose : List Token → Token) : Rule Token (Step Token) [] where
  plan := fun frame => ⟨.branch .leaf .leaf, .join (.emit (choose frame.output)) (.reuse frame.focus)⟩
  react := fun frame result =>
    let token := match result with
      | [] => choose frame.output
      | token :: _ => token
    ⟨token :: frame.target, .record frame.target token⟩

theorem produced_exact (choose : List Token → Token) (frame : Configuration Token) :
    (rule choose).produced frame = choose frame.output :: frame.output := rfl

theorem advance_output (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).output = choose frame.output :: frame.output :=
  (rule choose).advance_output frame

/-- The operational witness contains the token selected from the previous produced output. -/
theorem advance_history (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).history =
      .extend frame.history (.record frame.target (choose frame.output)) := rfl

theorem advance_target (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).target = choose frame.output :: frame.target := rfl

/-- The reuse expression position reads one exact earlier resource. -/
theorem reuse_reference (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).support.nodeAt (.fresh (.right .root)) = .reuse (.old frame.focus) := rfl

theorem reuse_value (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).support.read (.fresh (.right .root)) = frame.output := rfl

theorem reuse_link (choose : List Token → Token) (frame : Configuration Token) :
    ((rule choose).advance frame).support.Depends (.fresh (.right .root)) (.old frame.focus) := .head _

theorem reuse_is_fresh (choose : List Token → Token) (frame : Configuration Token) :
    (Address.old frame.focus : Address ((rule choose).advance frame).layout) ≠ .fresh (.right .root) :=
  Support.old_fresh_distinct _ _

def token {previous next : List Token} : Step Token previous next → Token
  | .record _ value => value

/-- Independent specification of the feedback trajectory. -/
def trajectory (choose : List Token → Token) : Nat → List Token
  | 0 => []
  | depth + 1 => choose (trajectory choose depth) :: trajectory choose depth

theorem state_eq_output (choose : List Token → Token) {last : Configuration Token}
    (execution : Execution (rule choose) (initial Token) last) : last.target = last.output := by
  induction execution with
  | idle => rfl
  | step previous ih =>
      exact (congrArg (List.cons _) ih).trans (advance_output choose _).symm

theorem trace_eq_output (choose : List Token → Token) {last : Configuration Token}
    (execution : Execution (rule choose) (initial Token) last) :
    WordSupport.trace token last.history = last.output := by
  induction execution with
  | idle => rfl
  | step previous ih =>
      exact (congrArg (List.cons _) ih).trans (advance_output choose _).symm

theorem run_output (choose : List Token → Token) (depth : Nat) :
    ((rule choose).run (initial Token) depth).1.output = trajectory choose depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      exact (advance_output choose _).trans
        (congrArg (fun output => choose output :: output) ih)

theorem run_target (choose : List Token → Token) (depth : Nat) :
    ((rule choose).run (initial Token) depth).1.target = trajectory choose depth :=
  (state_eq_output choose ((rule choose).run (initial Token) depth).2).trans (run_output choose depth)

/-- Three new expression resources per reaction; earlier records are shared by address. -/
theorem run_size (choose : List Token → Token) (depth : Nat) :
    ((rule choose).run (initial Token) depth).1.layout.size = 1 + depth * 3 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change ((rule choose).run (initial Token) depth).1.layout.size + 3 = 1 + (depth + 1) * 3
      exact (congrArg (fun size => size + 3) ih).trans (by rw [Nat.succ_mul, Nat.add_assoc])

/-- No common finite bound exists, while every particular support has a finite enumeration. -/
theorem supports_unbounded (choose : List Token → Token) (bound : Nat) :
    ∃ depth : Nat, bound < ((rule choose).run (initial Token) depth).1.layout.size := by
  refine ⟨bound, ?_⟩
  have lower := ((rule choose).run (initial Token) bound).2.finite_growth
  rw [(rule choose).run_length] at lower
  change 1 + bound ≤ _ at lower
  rw [Nat.add_comm 1 bound] at lower
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) lower

end RelationalFoundations.HistoricalFeedback
