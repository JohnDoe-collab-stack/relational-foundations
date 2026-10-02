import RelationalFoundations.ReducedWeakening
import Tests.HeterogeneousFeedback
set_option genInjectivity false

namespace RelationalFoundations.ReducedHeterogeneousTests
open TypedResources ReducedHeterogeneous

def m2 : Memory := run (initial 0) 2
def m6 : Memory := run (initial 0) 6
theorem c2 : Coherent m2 := run_coherent _ (initial_coherent 0) 2
theorem c6 : Coherent m6 := run_coherent _ (initial_coherent 0) 6

theorem exact_entire_original_frame : reconstruct m6 = HeterogeneousFeedback.specified HeterogeneousFeedbackTests.h6 :=
  all_finite_continuations (initial 0) HeterogeneousFeedbackTests.h6 HeterogeneousFeedbackTests.a6

theorem round_trip (seed depth : Nat) : reduce (reconstruct (run (initial seed) depth)) = run (initial seed) depth :=
  reduce_reconstruct _ (run_coherent _ (initial_coherent seed) depth)

theorem exact_native_round_trip (seed depth : Nat) :
    reconstruct (reduce (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) depth).1) =
      (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) depth).1 :=
  reconstruct_reduce (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) depth).2

theorem emitted_increase : (erase (step (initial 0))).tick.emitted =
    ⟨.observed 0 true, .updated 1, HeterogeneousFeedback.Step.act 0 true true 1⟩ := rfl

theorem emitted_decrease : (erase (run (initial 0) 4)).tick.emitted =
    ⟨.observed 1 false, .updated 0, HeterogeneousFeedback.Step.act 1 false false 0⟩ := rfl

theorem emitted_typed_reuse : (erase m2).tick.emitted =
    ⟨.updated 1, .ready 1, HeterogeneousFeedback.Step.reuse 1 1⟩ := rfl

def resumed := continuationCertificate m2 HeterogeneousFeedbackTests.suffix HeterogeneousFeedbackTests.suffix_admitted

theorem independently_admitted_suffix : resumed.realization.frame =
    HeterogeneousFeedback.specified HeterogeneousFeedbackTests.h6 := resumed.realization.exact

theorem reduced_terminal : view (run m2 HeterogeneousFeedbackTests.suffix.length) = .ready 0 :=
  continuation_terminal m2 c2 _ HeterogeneousFeedbackTests.suffix_admitted

theorem active_interface_terminal : view (continueFrom m2 HeterogeneousFeedbackTests.suffix) = .ready 0 :=
  active_terminal m2 c2 _ HeterogeneousFeedbackTests.suffix_admitted

theorem kernel_terminal_frame : reconstruct (inflate (erase (run m2 HeterogeneousFeedbackTests.suffix.length))) =
    HeterogeneousFeedback.specified HeterogeneousFeedbackTests.h6 :=
  kernel_continuation m2 _ HeterogeneousFeedbackTests.suffix_admitted

theorem restored_all_values (kind : Kind)
    (ref : Ref (HeterogeneousFeedback.declaredContext HeterogeneousFeedbackTests.h6) kind) :
    resumed.realization.frame.2.support.read kind ((resumed.coordinates kind).forward ref) =
      HeterogeneousFeedback.expected HeterogeneousFeedbackTests.h6 kind ref := resumed.certified kind ref

theorem restored_all_ordered_inputs (kind : Kind)
    (ref : Ref (HeterogeneousFeedback.declaredContext HeterogeneousFeedbackTests.h6) kind) :
    (resumed.realization.frame.2.support.nodeAt kind ((resumed.coordinates kind).forward ref)).inputs =
      (HeterogeneousFeedback.declaredDependencies HeterogeneousFeedbackTests.h6 kind ref).map
        (AnyRef.map (fun kind => (resumed.coordinates kind).forward)) := resumed.coveredDependencies kind ref

theorem reconstructed_act_still_has_boolean_first :
    ((reconstruct m2).2.support.nodeAt .number .head).inputs =
      [.truth (.old .head), .number (.old (.old .head))] := rfl

theorem old_truth_is_recovered :
    (reconstruct (run m2 4)).2.support.read .truth ((transport m2 4).embed .truth (.old .head)) = true :=
  old_value m2 4 .truth (.old .head)

theorem old_operator_is_recovered :
    (reconstruct (run m2 4)).2.support.nodeAt .truth ((transport m2 4).embed .truth (.old .head)) =
      ((reconstruct m2).2.support.nodeAt .truth (.old .head)).map (transport m2 4).embed :=
  old_operator m2 4 .truth (.old .head)

theorem old_relation_is_reflected (parent child : AnyRef (reconstruct m2).2.context) :
    (reconstruct (run m2 4)).2.support.Depends
      (AnyRef.map (transport m2 4).embed parent) (AnyRef.map (transport m2 4).embed child) ↔
        (reconstruct m2).2.support.Depends parent child := old_relation m2 4 parent child

theorem three_continuations_compose : run m2 (1 + (2 + 1)) = run (run (run m2 1) 2) 1 :=
  (run_add m2 1 3).trans (run_add (run m2 1) 2 1)

theorem phase_restored_from_position : phase (view m6) = phaseAt m6.position := rfl

theorem boolean_weakening_is_exact : view (run (initial 0) 1) = .observed 0 true := rfl

theorem scalar_cache_weakening_is_exact : inflate (erase m6) = m6 := inflate_erase m6 c6

theorem material_reduction (seed depth : Nat) (longEnough : 3 ≤ depth) :
    kernelCost (erase (run (initial seed) depth)) < expandedLowerCost (run (initial seed) depth) := by
  apply strict_reduction
  change 3 ≤ 0 + depth
  exact (Nat.zero_add depth).symm ▸ longEnough

theorem temporary_support_bound (seed depth earlier : Nat) (within : earlier ≤ depth) :
    (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) earlier).1.2.context.length ≤
      workingSupportBound (run (initial seed) depth) := by
  apply working_support_bound (run (initial seed) depth) earlier
  change earlier ≤ 0 + depth
  exact (Nat.zero_add depth).symm ▸ within

theorem corrupt_active_cache : ¬ Coherent (⟨0, 0, 7⟩ : Memory) := by
  intro same
  have numeric := congrArg number same
  exact Nat.noConfusion numeric

theorem same_value_distinct_reference :
    originalRef m6 ≠ (Ref.head : Ref (reconstruct m6).2.context .number) := repeated_zero_distinct

def truthStep : {source target : HeterogeneousFeedback.State} → HeterogeneousFeedback.Step source target → Bool
  | _, _, .observe _ b => b
  | _, _, .act _ _ _ _ => false
  | _, _, .reuse _ _ => false

def numberStep : {source target : HeterogeneousFeedback.State} → HeterogeneousFeedback.Step source target → Nat
  | _, _, .observe n _ => n
  | _, _, .act _ _ _ n => n
  | _, _, .reuse _ n => n

def emittedTruth (e : Event) : Bool := truthStep e.2.2
def emittedNumber (e : Event) : Nat := numberStep e.2.2

#guard emittedTruth (Kernel.initial 0).tick.emitted
#guard emittedTruth (Kernel.initial 7).tick.emitted == false
#guard emittedNumber (erase (run (initial 0) 1)).tick.emitted == 1
#guard emittedNumber (erase (run (initial 0) 4)).tick.emitted == 0
#guard emittedNumber (erase (run (initial 4) 1)).tick.emitted == 3
#guard emittedNumber (erase m2).tick.emitted == 1
#guard (run (initial 4) 6).active == 2
#guard (run (initial 4) 60).active == 0
#guard (run (initial 0) 63).active == 1
#guard (erase (run (initial 0) 63)).tick.next.position == 64
#guard kernelCost (erase m6) < expandedLowerCost m6
#guard cacheCost m6 < expandedLowerCost m6
#guard (certificate m6).resources.length == 7
#guard resumed.resources.length == 7

end RelationalFoundations.ReducedHeterogeneousTests
