import RelationalFoundations.HeterogeneousFeedback
set_option genInjectivity false

namespace RelationalFoundations.HeterogeneousFeedbackTests
open TypedResources HeterogeneousFeedback

/-- Inputs are operational witnesses built independently of the executor. -/
def h0 : History Step (.ready 0) (.ready 0) := .root
def h1 := History.extend h0 (Step.observe 0 true)
def h2 := History.extend h1 (Step.act 0 true true 1)
def h3 := History.extend h2 (Step.reuse 1 1)
def h4 := History.extend h3 (Step.observe 1 false)
def h5 := History.extend h4 (Step.act 1 false false 0)
def h6 := History.extend h5 (Step.reuse 0 0)

theorem a0 : Admissible h0 := True.intro
theorem a1 : Admissible h1 := ⟨a0, rfl⟩
theorem a2 : Admissible h2 := ⟨a1, rfl, rfl⟩
theorem a3 : Admissible h3 := ⟨a2, rfl⟩
theorem a4 : Admissible h4 := ⟨a3, rfl⟩
theorem a5 : Admissible h5 := ⟨a4, rfl, rfl⟩
theorem a6 : Admissible h6 := ⟨a5, rfl⟩

def p1 := complete h1 a1
def p2 := complete h2 a2
def p3 := complete h3 a3
def p5 := complete h5 a5
def p6 := complete h6 a6

theorem numerical_input_produces_truth :
    p1.realization.frame.2.support.read .truth .head = true := rfl

theorem boolean_and_numeric_inputs_are_both_identified :
    p2.realization.frame.2.support.nodeAt .number .head =
      .adjust (.old .head) (.old (.old .head)) := rfl

theorem two_sorted_dependencies_keep_their_order :
    (p2.realization.frame.2.support.nodeAt .number .head).inputs =
      [.truth (.old .head), .number (.old (.old .head))] := rfl

theorem produced_truth_selects_increase_witness :
    p2.realization.frame.2.history = History.extend h1 (Step.act 0 true true 1) := rfl

theorem produced_false_selects_decrease_witness :
    p5.realization.frame.2.history = History.extend h4 (Step.act 1 false false 0) := rfl

theorem reuse_points_to_the_numeric_resource :
    p3.realization.frame.2.support.nodeAt .number .head = .reuse (.old .head) := rfl

theorem reuse_value_equals_its_source :
    p3.realization.frame.2.support.read .number .head =
      p3.realization.frame.2.support.read .number (.old .head) := rfl

theorem reuse_identity_differs_from_its_source :
    (Ref.head : Ref p3.realization.frame.2.context .number) ≠ .old .head := Ref.head_ne_old _

theorem every_declared_typed_demand_certified (kind : Kind) (ref : Ref (declaredContext h6) kind) :
    p6.realization.frame.2.support.read kind ((p6.coordinates kind).forward ref) = expected h6 kind ref :=
  p6.certified kind ref

theorem every_actual_typed_ref_has_a_demand (kind : Kind) (ref : Ref p6.realization.frame.2.context kind) :
    (p6.coordinates kind).forward ((p6.coordinates kind).backward ref) = ref :=
  (p6.coordinates kind).backwardForward ref

theorem exhaustive_semantic_dependencies (kind : Kind) (ref : Ref (declaredContext h6) kind) :
    (p6.realization.frame.2.support.nodeAt kind ((p6.coordinates kind).forward ref)).inputs =
      (declaredDependencies h6 kind ref).map (AnyRef.map (fun kind => (p6.coordinates kind).forward)) :=
  p6.coveredDependencies kind ref

def suffix : History Step (.updated 1) (.ready 0) :=
  .extend (.extend (.extend (.extend .root (.reuse 1 1)) (.observe 1 false)) (.act 1 false false 0)) (.reuse 0 0)

theorem suffix_admitted : Admissible suffix := ⟨⟨⟨⟨True.intro, rfl⟩, rfl⟩, rfl, rfl⟩, rfl⟩
def resumed := resumeCompleteFrom h2 a2 p2.realization suffix suffix_admitted
def extension := resumeResourcesFrom h2 a2 p2.realization suffix suffix_admitted

theorem resumed_frame_is_the_complete_specification : resumed.realization.frame = specified h6 :=
  resumed.realization.exact

theorem resumed_terminal_is_independent : visible resumed.realization.frame = .ready 0 := resumed.terminal

theorem prefix_certification_is_preserved (kind : Kind) (ref : Ref (declaredContext h2) kind) :
    resumed.realization.frame.2.support.read kind (extension.embed kind ((p2.coordinates kind).forward ref)) =
      expected h2 kind ref := resumeFrom_certified_old h2 a2 p2.realization suffix suffix_admitted kind ref

theorem earlier_typed_identity_is_preserved (kind : Kind) {one two : Ref p2.realization.frame.2.context kind}
    (separate : one ≠ two) : extension.embed kind one ≠ extension.embed kind two :=
  fun same => separate (extension.embed_injective kind same)

theorem earlier_operation_and_provenance_preserved (kind : Kind) (ref : Ref p2.realization.frame.2.context kind) :
    resumed.realization.frame.2.support.nodeAt kind (extension.embed kind ref) =
      (p2.realization.frame.2.support.nodeAt kind ref).map extension.embed := extension.node_preserved kind ref

theorem earlier_dependencies_preserved (ref : AnyRef p2.realization.frame.2.context) :
    resumed.realization.frame.2.support.dependencies (AnyRef.map extension.embed ref) =
      (p2.realization.frame.2.support.dependencies ref).map (AnyRef.map extension.embed) :=
  extension.dependencies_preserved ref

theorem earlier_relations_preserved_and_reflected (parent child : AnyRef p2.realization.frame.2.context) :
    resumed.realization.frame.2.support.Depends (AnyRef.map extension.embed parent) (AnyRef.map extension.embed child) ↔
      p2.realization.frame.2.support.Depends parent child :=
  ⟨extension.relation_reflected, extension.relation_preserved⟩

theorem further_typed_transport_composes (kind : Kind) (ref : Ref p2.realization.frame.2.context kind) :
    let further := run resumed.realization.frame 3
    (extension.compose further.2.resources).embed kind ref =
      further.2.resources.embed kind (extension.embed kind ref) := Extension.embed_compose _ _ kind ref

def tailAfterSuffix : History Step (.ready 0) (.observed 0 true) := .extend .root (.observe 0 true)
theorem tail_admitted : Admissible tailAfterSuffix := ⟨True.intro, rfl⟩

theorem complete_configurations_compose :
    (resume h2 a2 (History.append suffix tailAfterSuffix)
      ((admissible_append suffix tailAfterSuffix).mpr ⟨suffix_admitted, tail_admitted⟩)).frame =
      (run resumed.realization.frame 1).1 :=
  resume_compose h2 a2 suffix tailAfterSuffix suffix_admitted tail_admitted

def wrongTest := History.extend h0 (Step.observe 0 false)
def wrongChoice := History.extend h1 (Step.act 0 true false 1)
def wrongResult := History.extend h1 (Step.act 0 true true 9)
def wrongReuse := History.extend h2 (Step.reuse 1 2)

theorem wrong_choice_excluded : ¬ Admissible wrongChoice := by
  intro admitted
  have impossible : false = true := admitted.2.1
  cases impossible

theorem wrong_choice_has_no_complete_realization : ¬ Nonempty (CompleteRealization wrongChoice) :=
  fun realized => wrong_choice_excluded ((complete_coverage_iff wrongChoice).mpr realized)

theorem checker_returns_rejection_witness : ∃ reason, check wrongChoice = .inr ⟨reason⟩ :=
  check_rejects wrongChoice wrong_choice_excluded

def accepted {seed : Nat} {target : State} (history : History Step (.ready seed) target) : Bool :=
  match check history with | .inl _ => true | .inr _ => false

/- Executable checks complement the general proofs; each tests the constructed data. -/
#guard accepted h0
#guard accepted h6
#guard !accepted wrongTest
#guard !accepted wrongChoice
#guard !accepted wrongResult
#guard !accepted wrongReuse
#guard p1.realization.frame.2.support.read .truth .head
#guard Nat.beq (p2.realization.frame.2.support.read .number .head) 1
#guard Nat.beq (p5.realization.frame.2.support.read .number .head) 0
#guard p6.resources.length == 7
#guard resumed.resources.length == 7
def readsReady (number : Nat) : State → Bool
  | .ready produced => Nat.beq produced number
  | .observed _ _ => false
  | .updated _ => false

#guard readsReady 0 (visible p6.realization.frame)
#guard readsReady 2 (run (initial 4) 6).1.1

end RelationalFoundations.HeterogeneousFeedbackTests
