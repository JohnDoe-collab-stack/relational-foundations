import RelationalFoundations.FeedbackCoverage
set_option genInjectivity false

namespace RelationalFoundations.FeedbackCoverageTests
open ResourceGraph OutputDriven HistoricalFeedback FeedbackCoverage
universe u

/-- Coverage needs neither decidable token equality nor a supplied semantic certificate. -/
def arbitrary_realization {Token : Type u} (choose : List Token → Token)
    {target : List Token} (history : History (Step Token) [] target)
    (admitted : Admissible choose history) : CompleteRealization choose history :=
  FeedbackCoverage.complete choose history admitted

def alternating : List Bool → Bool
  | [] => true
  | previous :: _ => !previous

/-- The test inputs are independent operational histories, not executor outputs. -/
def firstHistory : History (Step Bool) [] [false, true] :=
  .extend (.extend .root (.record [] true)) (.record [true] false)

def suffix : History (Step Bool) [false, true] [false, true, false, true] :=
  .extend (.extend .root (.record [false, true] true)) (.record [true, false, true] false)

def whole := History.append firstHistory suffix

theorem prefix_admitted : Admissible alternating firstHistory := ⟨⟨True.intro, rfl⟩, rfl⟩
theorem suffix_admitted : Admissible alternating suffix := ⟨⟨True.intro, rfl⟩, rfl⟩
theorem whole_admitted : Admissible alternating whole :=
  (admissible_append alternating firstHistory suffix).mpr ⟨prefix_admitted, suffix_admitted⟩

def built := FeedbackCoverage.complete alternating whole whole_admitted
def continued := resume alternating firstHistory prefix_admitted suffix

theorem input_history_reconstructed : packed built.realization.frame =
    ⟨[false, true, false, true], whole⟩ := built.realization.exact

theorem independently_specified_terminal : built.realization.frame.output =
    [false, true, false, true] := built.terminal

theorem all_operational_demands_certified (demand : Demand whole) :
    built.realization.frame.support.read (built.coordinates.forward demand) = expected demand :=
  built.certified demand

theorem all_addresses_have_a_unique_demand (address : Address built.realization.frame.layout) :
    built.coordinates.forward (built.coordinates.backward address) = address :=
  built.coordinates.backwardForward address

theorem demand_identity_preserved {first second : Demand whole}
    (same : built.coordinates.forward first = built.coordinates.forward second) : first = second :=
  (built.coordinates.forwardBackward first).symm.trans
    ((congrArg built.coordinates.backward same).trans (built.coordinates.forwardBackward second))

theorem complete_dependency_list (demand : Demand whole) :
    built.realization.frame.support.dependencies (built.coordinates.forward demand) =
      (declaredDependencies demand).map built.coordinates.forward := built.coveredDependencies demand

theorem every_certificate_uses_the_constructed_support (address : Address built.realization.frame.layout) :
    built.realization.frame.support.read address =
      (built.realization.frame.support.nodeAt address).eval built.realization.frame.support.read :=
  built.ruleCertified address

theorem finite_enumeration_complete (address : Address built.realization.frame.layout) :
    address ∈ built.resources := built.exhaustive address

theorem finite_enumeration_unique : built.resources.Nodup := built.unique

/-- The last reuse points to the actual previous result, rather than an equal reconstructed value. -/
theorem last_reuse_has_historical_identity :
    built.realization.frame.support.nodeAt
        (built.coordinates.forward (.atStep .last .reuse)) =
      .reuse (built.coordinates.forward (.atStep (.earlier .last) .result)) := rfl

theorem last_reuse_obligation_is_previous_result :
    declaredDependencies (Demand.atStep (history := whole) .last .reuse) =
      [.atStep (.earlier .last) .result] := rfl

theorem reuse_and_reused_resource_remain_distinct :
    built.coordinates.forward (.atStep .last .reuse) ≠
      built.coordinates.forward (.atStep (.earlier .last) .result) := by
  intro same
  cases same

theorem split_reconstructs_all_witnesses : packed continued.1 =
    ⟨[false, true, false, true], whole⟩ :=
  resume_history_exact alternating firstHistory prefix_admitted suffix suffix_admitted

theorem split_preserves_complete_configuration : continued.1 = built.realization.frame :=
  resume_equals_build alternating firstHistory prefix_admitted suffix suffix_admitted

theorem prefix_certificates_survive (demand : Demand firstHistory) :
    continued.1.support.read
        (continued.2.embed (locate alternating firstHistory prefix_admitted demand)) =
      expected (appendDemand firstHistory suffix demand) :=
  resume_certified_old alternating firstHistory prefix_admitted suffix demand

theorem prefix_constructors_and_references_survive
    (address : Address (build alternating firstHistory prefix_admitted).frame.layout) :
    continued.1.support.nodeAt (continued.2.embed address) =
      ((build alternating firstHistory prefix_admitted).frame.support.nodeAt address).map continued.2.embed :=
  resume_preserves alternating firstHistory prefix_admitted suffix address

theorem prefix_relations_preserved_and_reflected
    (parent child : Address (build alternating firstHistory prefix_admitted).frame.layout) :
    continued.1.support.Depends (continued.2.embed parent) (continued.2.embed child) ↔
      (build alternating firstHistory prefix_admitted).frame.support.Depends parent child :=
  resume_relation_iff alternating firstHistory prefix_admitted suffix parent child

theorem further_transport_composes
    (address : Address (build alternating firstHistory prefix_admitted).frame.layout) :
    let next := (rule alternating).run continued.1 3
    (continued.2.compose next.2).embed address = next.2.embed (continued.2.embed address) :=
  resume_transport_compose alternating firstHistory prefix_admitted suffix 3 address

/-- A legal relation witness alone does not imply admission under a fixed choice procedure. -/
def alwaysTrue : List Bool → Bool := fun _ => true
def otherFirst : History (Step Bool) [] [false] := .extend .root (.record [] false)
def otherLater : History (Step Bool) [] [false, true] := firstHistory

theorem other_first_excluded : ¬ Admissible alwaysTrue otherFirst := by
  intro admitted
  have impossible : false = true := admitted.2
  cases impossible

theorem other_later_excluded : ¬ Admissible alwaysTrue otherLater := by
  intro admitted
  have impossible : false = true := admitted.2
  cases impossible

theorem no_realization_outside_admission : ¬ Nonempty (Realization alwaysTrue otherFirst) :=
  fun realized => other_first_excluded ((coverage_iff alwaysTrue otherFirst).mpr realized)

theorem no_complete_realization_outside_admission :
    ¬ Nonempty (CompleteRealization alwaysTrue otherLater) :=
  fun realized => other_later_excluded ((complete_coverage_iff alwaysTrue otherLater).mpr realized)

theorem no_canonical_run_outside_admission :
    ¬ (∃ depth, packed ((rule alwaysTrue).run (initial Bool) depth).1 = ⟨[false], otherFirst⟩) :=
  fun generated => other_first_excluded ((generated_iff_admissible alwaysTrue otherFirst).mp generated)

theorem checking_accepted_input_returns_all_certificates :
    ∃ result, check alternating whole = .inl result := check_complete alternating whole whole_admitted

theorem checking_rejected_input_returns_a_reason :
    ∃ reason, check alwaysTrue otherLater = .inr ⟨reason⟩ :=
  check_rejects alwaysTrue otherLater other_later_excluded

def checkedOutput {target : List Bool} (history : History (Step Bool) [] target) : Option (List Bool) :=
  match check alternating history with
  | .inl result => some result.realization.frame.output
  | .inr _ => none

/- Executed checks include origin, acceptance, first-step rejection and later rejection. -/
#guard checkedOutput (.root : History (Step Bool) [] []) == some []
#guard checkedOutput whole == some [false, true, false, true]
#guard checkedOutput otherFirst == none
#guard (match check alwaysTrue otherLater with | .inl _ => false | .inr _ => true)
#guard built.resources.length == 13
#guard built.realization.frame.history.length == 4
#guard built.realization.frame.output == [false, true, false, true]
#guard continued.1.layout.size == 13

end RelationalFoundations.FeedbackCoverageTests
