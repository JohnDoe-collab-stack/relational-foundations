import RelationalFoundations.GroupingTraces
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping
universe u

/-- Steps are independently declared effective, locally admitted operations.
The list and its positive matcher enumerate that declared domain. -/
structure Rules where
  State : Type u
  Step : State → State → Type u
  rank : State → Nat
  choices : (x : State) → List ((y : State) × Step x y)
  locate : {x y : State} → (step : Step x y) →
    {entry : (z : State) × Step x z // entry ∈ choices x ∧ HEq entry (⟨y, step⟩ : (z : State) × Step x z)}
  decreases : ∀ {x y}, Step x y → rank y < rank x
  diamond : ∀ {x y z}, Step x y → Step x z → Join Step y z

namespace Rules
def Terminal (rules : Rules.{u}) (x : rules.State) : Prop :=
  ∀ {y}, rules.Step x y → False

structure Normalized (rules : Rules.{u}) (x : rules.State) where
  target : rules.State
  trace : Trace rules.Step x target
  terminal : rules.Terminal target

theorem terminal_of_empty (rules : Rules.{u}) (x : rules.State)
    (empty : rules.choices x = []) : rules.Terminal x := by
  intro y step
  obtain ⟨entry, member, _⟩ := rules.locate step
  rw [empty] at member
  cases member

theorem zero_terminal (rules : Rules.{u}) (x : rules.State)
    (zero : rules.rank x = 0) : rules.Terminal x := by
  intro y step
  have lt := rules.decreases step
  rw [zero] at lt
  exact Nat.not_lt_zero _ lt
end Rules
end RelationalFoundations.CertifiedGrouping

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Rules
#print axioms RelationalFoundations.CertifiedGrouping.Rules.terminal_of_empty
#print axioms RelationalFoundations.CertifiedGrouping.Rules.zero_terminal
/- AXIOM_AUDIT_END -/
