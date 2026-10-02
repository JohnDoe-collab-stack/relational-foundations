import RelationalFoundations.NativeForgettingSeparationV1
import Tests.ReducedHeterogeneous
set_option genInjectivity false

namespace RelationalFoundations.NativeForgettingTestsV1
open TypedResources NativeForgettingV1

def observed : Memory := ⟨1, 0⟩

theorem both_origins_have_one_memory : forget prefixZero = forget prefixTwo := same_erased

theorem all_continuations_agree (count : Nat) : nativeObservations prefixZero count = nativeObservations prefixTwo count :=
  same_all_future_observations count

theorem actual_nonempty_reuse : events shared reuseSuffix.length = historyEvents reuseSuffix :=
  all_admissible_events shared reuseSuffix reuseSuffix_admitted

theorem both_certifications_are_constructed :
    (certify shared).value = (certify shared).node.eval (read (ReducedHeterogeneous.phaseAt shared.position) shared.active) :=
  reuse_certified

theorem preserved_consumer_order : (observation observed).inputs = [⟨.truth, 1⟩, ⟨.number, 0⟩] := rfl

theorem actual_native_ports_at_two :
    frontierFor shared prefixZero zero_matches .number .head = (.head : Ref prefixZero.2.context .number) := rfl

theorem new_reuse_operator_exact :
    (HeterogeneousFeedback.advance prefixZero).2.support.nodeAt .number .head = .reuse (.old .head) := rfl

theorem reuse_source_and_result_are_distinct :
    (Ref.head : Ref (HeterogeneousFeedback.advance prefixZero).2.context .number) ≠ .old .head := Ref.head_ne_old _

theorem reused_number_has_identified_source : (observation shared).inputs = [⟨.number, 2⟩] := rfl

theorem native_new_occurrence_is_three : address (outputRef prefixZero) = 3 := new_occurrence_memory shared prefixZero zero_matches

theorem current_reference_correspondence :
    Corresponding shared prefixZero prefixTwo zero_matches two_matches .number .head .head := ⟨.head, rfl, rfl⟩

theorem corresponding_values_equal : prefixZero.2.support.read .number .head = prefixTwo.2.support.read .number .head :=
  corresponding_values shared prefixZero prefixTwo zero_matches two_matches .number .head .head current_reference_correspondence

theorem initial_values_still_separate :
    prefixZero.2.support.read .number (.old (.old .head)) ≠ prefixTwo.2.support.read .number (.old (.old .head)) :=
  initial_observation_separates

theorem numeric_port_retained_at_observe : Retained (initial 0) .number .head (.old .head) := rfl

theorem retained_numeric_identity_in_native_execution :
    frontierFor (step (initial 0)) (HeterogeneousFeedback.advance (HeterogeneousFeedback.initial 0))
      (matches_step (initial 0) (HeterogeneousFeedback.initial 0) (forget_matches (.idle : HeterogeneousFeedback.Execution
        (HeterogeneousFeedback.initial 0) (HeterogeneousFeedback.initial 0)))) .number (.old .head) =
      (HeterogeneousFeedback.advanceResources (HeterogeneousFeedback.initial 0)).embed .number .head :=
  retained_native_identity (initial 0) (HeterogeneousFeedback.initial 0)
    (forget_matches (.idle : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial 0) (HeterogeneousFeedback.initial 0)))
    .number .head (.old .head)
    numeric_port_retained_at_observe

theorem every_new_operator (count : Nat) :
    (⟨Result (ReducedHeterogeneous.phaseAt (run shared count).position),
      (certify (run shared count)).node.map
        (intoNextFor (run shared count) (HeterogeneousFeedback.run prefixZero count).1 (matches_run shared prefixZero zero_matches count))⟩ :
      (kind : Kind) × Operation (HeterogeneousFeedback.advance (HeterogeneousFeedback.run prefixZero count).1).2.context kind) =
    ⟨Result (ReducedHeterogeneous.phase (HeterogeneousFeedback.run prefixZero count).1.1),
      (HeterogeneousFeedback.advance (HeterogeneousFeedback.run prefixZero count).1).2.support.nodeAt
        (Result (ReducedHeterogeneous.phase (HeterogeneousFeedback.run prefixZero count).1.1))
          (outputRef (HeterogeneousFeedback.run prefixZero count).1)⟩ :=
  new_operator_memory _ _ (matches_run _ _ zero_matches count)

theorem every_new_certificate (count : Nat) :
    (certify (run shared count)).value = ((certify (run shared count)).node.map
      (frontierFor (run shared count) (HeterogeneousFeedback.run prefixZero count).1 (matches_run shared prefixZero zero_matches count))).eval
        (HeterogeneousFeedback.run prefixZero count).1.2.support.read := zero_new_certificates count

theorem every_new_node_certified_after_extension (count : Nat) :
    (certify (run shared count)).value = ((certify (run shared count)).node.map
      (intoNextFor (run shared count) (HeterogeneousFeedback.run prefixTwo count).1
        (matches_run shared prefixTwo two_matches count))).eval
          (HeterogeneousFeedback.advance (HeterogeneousFeedback.run prefixTwo count).1).2.support.read :=
  every_new_evaluation _ _ two_matches count

theorem every_old_prefix_ref_gets_a_distinct_transport (kind : Kind) (count : Nat) :
    Function.Injective ((HeterogeneousFeedback.run prefixZero count).2.embed kind) := transport_identity _ _ _

theorem native_future_witnesses_complete {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view shared) target) (allowed : HeterogeneousFeedback.Admissible following) :
    (⟨(HeterogeneousFeedback.run prefixZero following.length).1.1, (HeterogeneousFeedback.run prefixZero following.length).2.continuation⟩ :
      (last : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (view shared) last) = ⟨target, following⟩ :=
  (same_all_admitted_suffixes following allowed).1

theorem terminal_exact : view (run shared reuseSuffix.length) = .ready 1 := all_admissible_terminal shared reuseSuffix reuseSuffix_admitted

theorem three_stages_compose : run shared (1 + (2 + 3)) = run (run (run shared 1) 2) 3 :=
  (run_add shared 1 5).trans (run_add (run shared 1) 2 3)

theorem lost_origin_cannot_be_recovered :
    ¬ (∃ recover : Memory → Nat, ∀ old : ReducedHeterogeneous.Memory, ReducedHeterogeneous.Coherent old → recover (erase old) = old.origin) :=
  origin_irrecoverable

theorem cache_comparison (old : ReducedHeterogeneous.Memory) :
    ReducedHeterogeneous.cacheCost old = cost (erase old) + (1 + ReducedHeterogeneous.digits old.origin) := cost_removed_origin old

def numeric (o : Observation) : Nat := match o.kind, o.value with
  | .number, value => value
  | .truth, _ => 0

def truth (o : Observation) : Bool := match o.kind, o.value with
  | .truth, value => value
  | .number, _ => false

def kindTag : Kind → Bool
  | .number => false
  | .truth => true

def sameInputs : List (Kind × Nat) → List (Kind × Nat) → Bool
  | [], other => match other with | [] => true | _ :: _ => false
  | (a, n) :: first, other => match other with
      | [] => false
      | (b, m) :: second => (kindTag a == kindTag b) && n == m && sameInputs first second

#guard truth (observation (initial 0))
#guard truth (observation (initial 7)) == false
#guard numeric (observation observed) == 1
#guard numeric (observation ⟨4, 1⟩) == 0
#guard numeric (observation shared) == 1
#guard (step shared).position == 3
#guard (step shared).active == 1
#guard (run (initial 4) 60).active == 0
#guard sameInputs (observation observed).inputs [⟨.truth, 1⟩, ⟨.number, 0⟩]
#guard sameInputs (observation observed).inputs [⟨.number, 0⟩, ⟨.truth, 1⟩] == false
#guard sameInputs (observation shared).inputs [⟨.number, 2⟩]
#guard Nat.beq (((tick shared).2.2.2).node.eval (read (ReducedHeterogeneous.phaseAt shared.position) shared.active)) 1
#guard (observations shared 7).length == 7
#guard cost shared < ReducedHeterogeneous.cacheCost (ReducedHeterogeneous.run (ReducedHeterogeneous.initial 0) 2)
#guard cost (erase (ReducedHeterogeneous.run (ReducedHeterogeneous.initial 0) 60)) ==
  ReducedHeterogeneous.kernelCost (ReducedHeterogeneous.erase (ReducedHeterogeneous.run (ReducedHeterogeneous.initial 0) 60))

end RelationalFoundations.NativeForgettingTestsV1
