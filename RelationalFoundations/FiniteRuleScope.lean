import RelationalFoundations.FiniteRuleConstruction
set_option genInjectivity false

namespace RelationalFoundations.FiniteRuleScope
open FiniteRuleConstruction
universe u
variable (rules : Rules.{u})

/-- Admission determines the entire history at each finite horizon for fixed rules. -/
theorem admissible_unique {one two : rules.State}
    (left : History rules.Step rules.origin one) (right : History rules.Step rules.origin two)
    (leftAllowed : rules.Admissible left) (rightAllowed : rules.Admissible right)
    (sameLength : left.length = right.length) :
    (⟨one, left⟩ : (target : rules.State) × History rules.Step rules.origin target) = ⟨two, right⟩ :=
  (rules.build left leftAllowed).exact.symm.trans
    ((congrArg rules.recorded ((rules.build_run left leftAllowed).trans
      ((congrArg (fun depth => (rules.run rules.initial depth).1) sameLength).trans
        (rules.build_run right rightAllowed).symm))).trans (rules.build right rightAllowed).exact)

theorem realization_at_horizon {target : rules.State}
    (history : History rules.Step rules.origin target) (allowed : rules.Admissible history) :
    (rules.complete history allowed).realization.frame = (rules.run rules.initial history.length).1 :=
  rules.build_run history allowed

theorem every_horizon_admitted (depth : Nat) :
    rules.Admissible (rules.recorded (rules.run rules.initial depth).1).2 :=
  (rules.run rules.initial depth).2.admissible

theorem run_length (frame : rules.Frame) (depth : Nat) : (rules.run frame depth).2.length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact congrArg Nat.succ ih

theorem recorded_horizon (depth : Nat) : (rules.recorded (rules.run rules.initial depth).1).2.length = depth := by
  have length := (rules.run rules.initial depth).2.history_length
  have initialLength := congrArg (fun record => record.2.length) rules.initial_recorded
  rw [initialLength, run_length] at length
  exact length.trans (Nat.zero_add depth)

/-- Extraction transfers a predicate justified by its separate local invariant proof. -/
theorem terminal_predicate_iff (predicate : rules.State → Nat → Prop) {target : rules.State}
    (history : History rules.Step rules.origin target) (allowed : rules.Admissible history) :
    predicate (rules.visible (rules.complete history allowed).realization.frame) history.length ↔
      predicate target history.length := by
  rw [(rules.complete history allowed).terminal]

end RelationalFoundations.FiniteRuleScope

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.FiniteRuleScope.admissible_unique
#print axioms RelationalFoundations.FiniteRuleScope.realization_at_horizon
#print axioms RelationalFoundations.FiniteRuleScope.every_horizon_admitted
#print axioms RelationalFoundations.FiniteRuleScope.run_length
#print axioms RelationalFoundations.FiniteRuleScope.recorded_horizon
#print axioms RelationalFoundations.FiniteRuleScope.terminal_predicate_iff
/- AXIOM_AUDIT_END -/
