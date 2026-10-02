import RelationalFoundations.FiniteRuleInstances
import Tests.FeedbackCoverage
import Tests.HeterogeneousFeedback
set_option genInjectivity false

namespace RelationalFoundations.FiniteRuleConstructionTests
open FiniteRuleConstruction FiniteRuleInstances
open ResourceGraph
universe u

/-- The public constructors take local operational admission, with no complete
support, supplied global certificate, or equality decision on token values. -/
def arbitrary_homogeneous (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :=
  homogeneousComplete Token choose history allowed

def arbitrary_heterogeneous {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :=
  heterogeneousComplete history allowed

def hom := homogeneous Bool FeedbackCoverageTests.alternating
def homAll := homogeneousComplete Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole FeedbackCoverageTests.whole_admitted
def homLegacy := homogeneousNativeComplete Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole FeedbackCoverageTests.whole_admitted
def homPrefix := homogeneousComplete Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.firstHistory FeedbackCoverageTests.prefix_admitted

def het := heterogeneous 0
def hetTwo := heterogeneousComplete HeterogeneousFeedbackTests.h2 HeterogeneousFeedbackTests.a2
def hetFive := heterogeneousComplete HeterogeneousFeedbackTests.h5 HeterogeneousFeedbackTests.a5
def hetAll := heterogeneousComplete HeterogeneousFeedbackTests.h6 HeterogeneousFeedbackTests.a6
def hetLegacy := heterogeneousNativeComplete HeterogeneousFeedbackTests.h6 HeterogeneousFeedbackTests.a6

theorem whole_homogeneous_frame : homAll.realization.frame = FeedbackCoverageTests.built.realization.frame :=
  homogeneousFrame _ _ _ _

theorem whole_heterogeneous_frame : hetAll.realization.frame = HeterogeneousFeedbackTests.p6.realization.frame :=
  heterogeneousFrame _ _

theorem homogeneous_covers_independent_dependencies (demand : FeedbackCoverage.Demand FeedbackCoverageTests.whole) :
    homLegacy.realization.frame.support.dependencies (homLegacy.coordinates.forward demand) =
      (FeedbackCoverage.declaredDependencies demand).map homLegacy.coordinates.forward := homLegacy.coveredDependencies demand

theorem heterogeneous_covers_independent_dependencies (kind : TypedResources.Kind)
    (ref : TypedResources.Ref (HeterogeneousFeedback.declaredContext HeterogeneousFeedbackTests.h6) kind) :
    (hetLegacy.realization.frame.2.support.nodeAt kind ((hetLegacy.coordinates kind).forward ref)).inputs =
      (HeterogeneousFeedback.declaredDependencies HeterogeneousFeedbackTests.h6 kind ref).map
        (TypedResources.AnyRef.map (fun kind => (hetLegacy.coordinates kind).forward)) := hetLegacy.coveredDependencies kind ref

theorem all_generic_requests_certified (kind : het.Kind) (request : het.Requests HeterogeneousFeedbackTests.h6 kind) :
    het.read hetAll.realization.frame kind ((hetAll.coverage.coordinates kind).forward request) =
      het.expected HeterogeneousFeedbackTests.h6 kind request := hetAll.coverage.values kind request

theorem all_generic_resources_exhaustive (ref : Packed (het.Ref hetAll.realization.frame)) :
    ref ∈ hetAll.resources.items := hetAll.resources.exhaustive ref

theorem all_generic_local_rules (kind : het.Kind) (ref : het.Ref hetAll.realization.frame kind) :
    het.read hetAll.realization.frame kind ref = het.eval (het.read hetAll.realization.frame)
      (het.node hetAll.realization.frame kind ref) := hetAll.certified kind ref

theorem same_homogeneous_demands_have_inverses (request : hom.Requests FeedbackCoverageTests.whole ()) :
    (homogeneousRequests Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole).backward
      ((homogeneousRequests Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole).forward request) = request :=
  (homogeneousRequests _ _ _).forwardBackward request

theorem same_heterogeneous_demands_have_inverses (kind : TypedResources.Kind)
    (request : het.Requests HeterogeneousFeedbackTests.h6 kind) :
    (heterogeneousRequests HeterogeneousFeedbackTests.h6 kind).backward
      ((heterogeneousRequests HeterogeneousFeedbackTests.h6 kind).forward request) = request :=
  (heterogeneousRequests _ _).forwardBackward request

theorem fragment_has_three_positions : homAll.realization.frame.support.nodeAt (.fresh .root) =
    .join (.fresh (.left .root)) (.fresh (.right .root)) := rfl

theorem fragment_internal_inputs_keep_order : homAll.realization.frame.support.dependencies (.fresh .root) =
    [.fresh (.left .root), .fresh (.right .root)] := rfl

theorem heterogeneous_operator_has_two_sorts : hetTwo.realization.frame.2.support.nodeAt .number .head =
    .adjust (.old .head) (.old (.old .head)) := rfl

theorem selected_false_is_actual_data : hetFive.realization.frame.2.history =
    History.extend HeterogeneousFeedbackTests.h4 (HeterogeneousFeedback.Step.act 1 false false 0) := rfl

theorem equal_values_retain_distinct_typed_identities :
    (TypedResources.Ref.head : TypedResources.Ref hetAll.realization.frame.2.context .number) ≠
      .old (.old (.old (.old (.old (.old .head))))) := TypedResources.Ref.head_ne_old _

/-- A concrete separator for replacing reference identity by numerical value. -/
theorem numerical_reading_is_not_injective : ¬ Function.Injective (hetAll.realization.frame.2.support.read .number) := by
  intro injective
  have same := injective (show hetAll.realization.frame.2.support.read .number .head =
    hetAll.realization.frame.2.support.read .number (.old (.old (.old (.old (.old (.old .head)))))) from rfl)
  exact equal_values_retain_distinct_typed_identities same

def resumed := het.resumeCompleteFrom HeterogeneousFeedbackTests.h2
  ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.a2) hetTwo.realization
  HeterogeneousFeedbackTests.suffix ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.suffix_admitted)

def extension := het.resumeExecutionFrom HeterogeneousFeedbackTests.h2
  ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.a2) hetTwo.realization
  HeterogeneousFeedbackTests.suffix ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.suffix_admitted)

theorem resumed_matches_native : resumed.realization.frame = HeterogeneousFeedbackTests.resumed.realization.frame :=
  (heterogeneousResume _ HeterogeneousFeedbackTests.a2 _ _ HeterogeneousFeedbackTests.suffix_admitted).trans
    (congrArg (fun frame => (HeterogeneousFeedback.run frame HeterogeneousFeedbackTests.suffix.length).1)
      (heterogeneousFrame HeterogeneousFeedbackTests.h2 HeterogeneousFeedbackTests.a2))

theorem old_numeric_value_retained : resumed.realization.frame.2.support.read .number (extension.embed .number .head) = (1 : Nat) :=
  extension.values_preserved .number .head

theorem old_truth_value_retained : resumed.realization.frame.2.support.read .truth (extension.embed .truth (.old .head)) = true :=
  extension.values_preserved .truth (.old .head)

theorem old_numeric_operator_retained :
    het.node resumed.realization.frame .number (extension.embed .number .head) =
      het.map extension.embed (het.node hetTwo.realization.frame .number .head) := extension.nodes_preserved .number .head

theorem old_relations_preserved_and_reflected (parent child : Packed (het.Ref hetTwo.realization.frame)) :
    het.Depends resumed.realization.frame (rename extension.embed parent) (rename extension.embed child) ↔
      het.Depends hetTwo.realization.frame parent child :=
  ⟨het.relation_reflected extension, het.relation_preserved extension⟩

theorem old_certification_retained (kind : het.Kind) (request : het.Requests HeterogeneousFeedbackTests.h2 kind) :
    het.read resumed.realization.frame kind (extension.embed kind
      (((het.certify HeterogeneousFeedbackTests.h2 hetTwo.realization).coverage.coordinates kind).forward request)) =
      het.expected HeterogeneousFeedbackTests.h2 kind request := het.resume_expected _ _ _ _ _ kind request

def one := het.run het.initial 2
def two := het.run one.1 4
def three := het.run two.1 3

theorem typed_transports_compose (kind : het.Kind) (ref : het.Ref het.initial kind) :
    (one.2.compose two.2).embed kind ref = two.2.embed kind (one.2.embed kind ref) := one.2.embed_compose two.2 kind ref

theorem execution_composition_associative : (one.2.compose two.2).compose three.2 = one.2.compose (two.2.compose three.2) :=
  one.2.compose_associative two.2 three.2

theorem historical_continuations_compose :
    (one.2.compose two.2).continuation = History.append one.2.continuation two.2.continuation :=
  one.2.continuation_compose two.2

theorem historical_occurrences_retained : History.append HeterogeneousFeedbackTests.h2 extension.continuation =
    resumed.realization.frame.2.history := extension.history_exact

theorem native_transport_same_identity (kind : het.Kind) (ref : het.Ref hetTwo.realization.frame kind) :
    extension.embed kind ref = (heterogeneousExecution extension).embed kind ref := heterogeneousTransport extension kind ref

theorem native_continuation_same_witnesses : extension.continuation = (heterogeneousExecution extension).continuation :=
  heterogeneousContinuation extension

def wrong := History.extend HeterogeneousFeedbackTests.h0 (HeterogeneousFeedback.Step.observe 0 false)

theorem wrong_not_admissible : ¬ het.Admissible wrong := fun allowed => Bool.noConfusion allowed.2

theorem wrong_has_no_complete_realization : ¬ Nonempty (het.Complete wrong) :=
  fun complete => wrong_not_admissible ((het.coverage_iff wrong).mpr complete)

theorem extracted_independent_guarantee : homAll.realization.frame.output.length = FeedbackCoverageTests.whole.length :=
  hom.extract_guarantee (fun state depth => state.length = depth) rfl
    (fun step _ depth prior => by cases step; exact congrArg Nat.succ prior) _ ((homogeneousAdmission _ _ _).mpr FeedbackCoverageTests.whole_admitted)

#guard homAll.resources.items.length == 13
#guard hetAll.resources.items.length == 7
#guard homAll.realization.frame.output == [false, true, false, true]
#guard Nat.beq (hetTwo.realization.frame.2.support.read .number .head) 1
#guard Nat.beq (hetFive.realization.frame.2.support.read .number .head) 0
#guard resumed.resources.items.length == 7
#guard Nat.beq (resumed.realization.frame.2.support.read .number (extension.embed .number .head)) 1
#guard resumed.realization.frame.2.support.read .truth (extension.embed .truth (.old .head))
#guard HeterogeneousFeedbackTests.readsReady 1 (het.visible (het.run het.initial 9).1)
#guard (homogeneousNativeComplete Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole FeedbackCoverageTests.whole_admitted).resources.length == 13

end RelationalFoundations.FiniteRuleConstructionTests
