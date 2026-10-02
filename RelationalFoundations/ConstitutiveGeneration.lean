import RelationalFoundations.Generation
import RelationalFoundations.Regime
set_option genInjectivity false

namespace RelationalFoundations.ConstitutiveGeneration
universe u v
variable {State : Type u} {Step : State → State → Type v}

def appendExactlyOneOccurrenceTransport {a b c : State} (first : History Step a b)
    {continuation : History Step b c} (one : History.ExactlyOne continuation) :
    ExactTransport (History.Occurrence first ⊕ Unit) (History.Occurrence (History.append first continuation)) := by
  cases one with
  | single step =>
    exact
      { forward := fun occurrence => match occurrence with
          | .inl old => .earlier old
          | .inr _ => .last
        backward := fun occurrence => match occurrence with
          | .last => .inr ()
          | .earlier old => .inl old
        forwardBackward := fun occurrence => by cases occurrence with
          | inl old => rfl
          | inr point => cases point; rfl
        backwardForward := fun occurrence => by cases occurrence <;> rfl }

def iterate {root : State} (initial : RootedConstruction Step root)
    (producer : (state : State) → Σ next : State, Step state next) : Nat → RootedConstruction Step root
  | 0 => initial
  | n + 1 =>
    let previous := iterate initial producer n
    let next := producer previous.endpoint
    ⟨next.1, .extend previous.history next.2⟩

def successorSplit {root : State} (initial : RootedConstruction Step root)
    (producer : (state : State) → Σ next : State, Step state next) (n : Nat) :
    ExactTransport (History.Occurrence (iterate initial producer n).history ⊕ Unit)
      (History.Occurrence (iterate initial producer (n + 1)).history) :=
  appendExactlyOneOccurrenceTransport _ (.single (producer (iterate initial producer n).endpoint).2)

theorem successor_old {root : State} (initial : RootedConstruction Step root)
    (producer : (state : State) → Σ next : State, Step state next) (n : Nat)
    (old : History.Occurrence (iterate initial producer n).history) :
    (successorSplit initial producer n).forward (.inl old) = .earlier old := rfl

theorem successor_fresh {root : State} (initial : RootedConstruction Step root)
    (producer : (state : State) → Σ next : State, Step state next) (n : Nat) :
    (successorSplit initial producer n).forward (.inr ()) = .last := rfl

theorem old_fresh_distinct {root : State} (initial : RootedConstruction Step root)
    (producer : (state : State) → Σ next : State, Step state next) (n : Nat)
    (old : History.Occurrence (iterate initial producer n).history) :
    (successorSplit initial producer n).forward (.inl old) ≠
      (successorSplit initial producer n).forward (.inr ()) := by
  intro eq
  cases eq
end RelationalFoundations.ConstitutiveGeneration
