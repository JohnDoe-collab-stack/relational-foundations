import RelationalFoundations.HistoricalFeedback
set_option genInjectivity false

namespace RelationalFoundations.OutputDrivenTests
open ResourceGraph OutputDriven

def choose : List Bool → Bool
  | [] => true
  | previous :: _ => !previous

def driver := HistoricalFeedback.rule choose
def start := HistoricalFeedback.initial Bool
def first := driver.advance start
def second := driver.advance first
def complete := driver.run start 4
def following := driver.run second 2

/-- Output dependence reaches the operational witness, not only the demand label. -/
theorem second_step_from_first_output : second.history =
    History.extend first.history (HistoricalFeedback.Step.record [true] false) := rfl

theorem complete_history_guarantee : WordSupport.trace HistoricalFeedback.token complete.1.history =
    HistoricalFeedback.trajectory choose 4 :=
  (HistoricalFeedback.trace_eq_output choose complete.2).trans (HistoricalFeedback.run_output choose 4)

theorem identified_reuse : second.support.nodeAt (.fresh (.right .root)) = .reuse (.old first.focus) :=
  HistoricalFeedback.reuse_reference choose first

theorem identified_link_survives : following.1.support.Depends
    (following.2.embed (.fresh (.right .root))) (following.2.embed (.old first.focus)) :=
  following.2.relation_preserved (HistoricalFeedback.reuse_link choose first)

theorem prefix_resources_keep_values (address : Address second.layout) :
    following.1.support.read (following.2.embed address) = second.support.read address :=
  following.2.read_preserved address

theorem split_preserves_complete_frame : complete.1 = following.1 := driver.run_add start 2 2

def initialExpression : Expr Bool Empty (.branch .leaf .leaf) := .join (.emit true) (.emit true)
def twins : Support Bool (.initial (.branch .leaf .leaf)) := .initial initialExpression
def leftTwin : Address (.initial (.branch .leaf .leaf)) := .initial (.left .root)
def rightTwin : Address (.initial (.branch .leaf .leaf)) := .initial (.right .root)

/-- Equal produced values do not identify the resources used by later steps. -/
theorem twin_values_equal : twins.read leftTwin = twins.read rightTwin := rfl

theorem twin_addresses_distinct : leftTwin ≠ rightTwin := by
  intro equality
  cases equality

def distinctReferences : Expr Bool (Address (.initial (.branch .leaf .leaf))) (.branch .leaf .leaf) :=
  .join (.reuse leftTwin) (.reuse rightTwin)

def reusedTwins := Support.extend twins distinctReferences
def twinsGrowth : Extension twins reusedTwins := .step .refl distinctReferences

theorem reuse_retains_first_identity : reusedTwins.dependencies (.fresh (.left .root)) = [.old leftTwin] := rfl
theorem reuse_retains_second_identity : reusedTwins.dependencies (.fresh (.right .root)) = [.old rightTwin] := rfl

theorem later_twins_still_distinct : twinsGrowth.embed leftTwin ≠ twinsGrowth.embed rightTwin :=
  fun equality => twin_addresses_distinct (twinsGrowth.embed_injective equality)

/-- Two slots can also reuse one resource without being identified themselves. -/
def repeatedReference : Expr Bool (Address (.initial (.branch .leaf .leaf))) (.branch .leaf .leaf) :=
  .join (.reuse leftTwin) (.reuse leftTwin)
def repeated := Support.extend twins repeatedReference

theorem same_reference_two_resources :
    repeated.nodeAt (.fresh (.left .root)) = repeated.nodeAt (.fresh (.right .root)) ∧
    (Address.fresh (.left .root) : Address (.extend (.initial (.branch .leaf .leaf)) (.branch .leaf .leaf))) ≠
      .fresh (.right .root) := by
  constructor
  · rfl
  · intro equality; cases equality

theorem all_internal_resources_certified (address : Address complete.1.layout) :
    complete.1.support.read address = (complete.1.support.nodeAt address).eval complete.1.support.read :=
  complete.1.support.read_correct address

theorem all_internal_resources_enumerated (address : Address complete.1.layout) :
    address ∈ complete.1.layout.addresses := complete.1.layout.addresses_complete address

#guard first.output == [true]
#guard second.output == [false, true]
#guard complete.1.output == [false, true, false, true]
#guard complete.1.target == complete.1.output
#guard complete.1.history.length == 4
#guard complete.1.layout.size == 13
#guard complete.1.layout.addresses.length == 13

end RelationalFoundations.OutputDrivenTests
