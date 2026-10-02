import RelationalFoundations.HistoricalFeedback
set_option genInjectivity false

/-!
# Independent admission and constructive coverage of feedback histories

Admission is specified on operational states and step witnesses, before any
support or executor is introduced. A step records the token prescribed by
`choose` on its source state. Coverage reconstructs the whole supplied history,
including its witnesses, and returns an actual execution and resource support.
-/

namespace RelationalFoundations.FeedbackCoverage
open ResourceGraph OutputDriven HistoricalFeedback
universe u
variable {Token : Type u}

def LocalAdmission (choose : List Token → Token) {source target : List Token}
    (step : Step Token source target) : Prop := token step = choose source

/-- Independent local operational conditions; no resource or realization is an input. -/
def Admissible (choose : List Token → Token) {source : List Token} :
    {target : List Token} → History (Step Token) source target → Prop
  | _, .root => True
  | _, .extend previous step => Admissible choose previous ∧ LocalAdmission choose step
termination_by structural _ history => history

abbrev OperationalHistory (Token : Type u) := (target : List Token) × History (Step Token) [] target

def packed (frame : Configuration Token) : OperationalHistory Token := ⟨frame.target, frame.history⟩

def recordAfter (value : Token) (previous : OperationalHistory Token) : OperationalHistory Token :=
  ⟨value :: previous.1, .extend previous.2 (.record previous.1 value)⟩

theorem advance_packed (choose : List Token → Token) (frame : Configuration Token) :
    packed ((rule choose).advance frame) = recordAfter (choose frame.output) (packed frame) := rfl

theorem recordAfter_exact {middle target : List Token} (history : History (Step Token) [] middle)
    (step : Step Token middle target) :
    recordAfter (token step) ⟨middle, history⟩ = ⟨target, .extend history step⟩ := by
  cases step
  rfl

structure Realization (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) where
  frame : Configuration Token
  execution : Execution (rule choose) (initial Token) frame
  exact : packed frame = ⟨target, history⟩

namespace Realization
variable {choose : List Token → Token} {target : List Token} {history : History (Step Token) [] target}

theorem target_exact (realization : Realization choose history) : realization.frame.target = target :=
  congrArg Sigma.fst realization.exact

theorem output_exact (realization : Realization choose history) : realization.frame.output = target :=
  (state_eq_output choose realization.execution).symm.trans realization.target_exact
end Realization

/-- The producer recurses on the supplied history, with only its local admission proof. -/
def build (choose : List Token → Token) : {target : List Token} →
    (history : History (Step Token) [] target) → Admissible choose history → Realization choose history
  | _, .root, _ => ⟨initial Token, .idle, rfl⟩
  | _, .extend previous step, admitted =>
      let old := build choose previous admitted.1
      let selected : choose old.frame.output = token step :=
        (congrArg choose old.output_exact).trans admitted.2.symm
      { frame := (rule choose).advance old.frame
        execution := .step old.execution
        exact := (advance_packed choose old.frame).trans
          ((congrArg (fun token => recordAfter token (packed old.frame)) selected).trans
            ((congrArg (recordAfter (token step)) old.exact).trans (recordAfter_exact previous step))) }
termination_by structural _ history _ => history

/-- All produced executions satisfy the independently declared admission conditions. -/
theorem execution_admissible (choose : List Token → Token) {last : Configuration Token}
    (execution : Execution (rule choose) (initial Token) last) : Admissible choose last.history := by
  induction execution with
  | idle => exact True.intro
  | step previous ih =>
      exact ⟨ih, (congrArg choose (state_eq_output choose previous)).symm⟩

theorem realization_admissible (choose : List Token → Token) {target : List Token}
    {history : History (Step Token) [] target} (realization : Realization choose history) :
    Admissible choose history :=
  (congrArg (fun recorded : OperationalHistory Token => Admissible choose recorded.2) realization.exact) ▸
    execution_admissible choose realization.execution

/-- Coverage is proved in both directions; the positive witness is supplied by `build`. -/
theorem coverage_iff (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) :
    Admissible choose history ↔ Nonempty (Realization choose history) :=
  ⟨fun admitted => ⟨build choose history admitted⟩,
    fun ⟨realization⟩ => realization_admissible choose realization⟩

theorem build_frame (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    (build choose history admitted).frame = ((rule choose).run (initial Token) history.length).1 := by
  induction history with
  | root => rfl
  | extend previous step ih =>
      exact congrArg (rule choose).advance (ih admitted.1)

theorem admissible_append (choose : List Token → Token) {source middle target : List Token}
    (first : History (Step Token) source middle) (following : History (Step Token) middle target) :
    Admissible choose (History.append first following) ↔
      Admissible choose first ∧ Admissible choose following := by
  induction following with
  | root => exact ⟨fun prior => ⟨prior, True.intro⟩, fun combined => combined.1⟩
  | extend previous step ih =>
      constructor
      · intro admitted
        have prior := ih.mp admitted.1
        exact ⟨prior.1, prior.2, admitted.2⟩
      · intro admitted
        exact ⟨ih.mpr ⟨admitted.1, admitted.2.1⟩, admitted.2.2⟩

inductive Role where
  | result
  | emission
  | reuse

namespace Role
def position : Role → Position (.branch .leaf .leaf)
  | .result => .root
  | .emission => .left .root
  | .reuse => .right .root

def ofPosition : Position (.branch .leaf .leaf) → Role
  | .root => .result
  | .left .root => .emission
  | .right .root => .reuse

theorem of_position (role : Role) : ofPosition role.position = role := by
  cases role <;> rfl

theorem position_of (position : Position (.branch .leaf .leaf)) : (ofPosition position).position = position := by
  cases position with
  | root => rfl
  | left position => cases position; rfl
  | right position => cases position; rfl
end Role

/-- Semantic obligations are extracted from the operational history, before building its support. -/
inductive Demand {target : List Token} (history : History (Step Token) [] target) : Type u where
  | initial
  | atStep (occurrence : History.Occurrence history) (role : Role)

def liftDemand {middle target : List Token} {history : History (Step Token) [] middle}
    (step : Step Token middle target) : Demand history → Demand (.extend history step)
  | .initial => .initial
  | .atStep occurrence role => .atStep (.earlier occurrence) role

def latest : {target : List Token} → (history : History (Step Token) [] target) → Demand history
  | _, .root => .initial
  | _, .extend _ _ => .atStep .last .result

def previousDemand : {target : List Token} → (history : History (Step Token) [] target) →
    History.Occurrence history → Demand history
  | _, .extend previous step, .last => liftDemand step (latest previous)
  | _, .extend previous step, .earlier occurrence => liftDemand step (previousDemand previous occurrence)
termination_by structural _ history _ => history

def declaredDependencies {target : List Token} {history : History (Step Token) [] target} :
    Demand history → List (Demand history)
  | .initial => []
  | .atStep occurrence .result => [.atStep occurrence .emission, .atStep occurrence .reuse]
  | .atStep _ .emission => []
  | .atStep occurrence .reuse => [previousDemand history occurrence]

def roleExpected (located : History.LocatedStep (Step Token)) : Role → List Token
  | .result => located.target
  | .emission => [token located.step]
  | .reuse => located.source

def expected {target : List Token} {history : History (Step Token) [] target} : Demand history → List Token
  | .initial => []
  | .atStep occurrence role => roleExpected occurrence.locatedStep role

/-- Locate an independently declared obligation in the support actually produced. -/
def locate (choose : List Token → Token) : {target : List Token} →
    (history : History (Step Token) [] target) → (admitted : Admissible choose history) →
    Demand history → Address (build choose history admitted).frame.layout
  | _, .root, _, .initial => .initial .root
  | _, .extend previous _, admitted, .initial => .old (locate choose previous admitted.1 .initial)
  | _, .extend _ _, _, .atStep .last role => .fresh role.position
  | _, .extend previous _, admitted, .atStep (.earlier occurrence) role =>
      .old (locate choose previous admitted.1 (.atStep occurrence role))
termination_by structural _ history _ _ => history

def classify (choose : List Token → Token) : {target : List Token} →
    (history : History (Step Token) [] target) → (admitted : Admissible choose history) →
    Address (build choose history admitted).frame.layout → Demand history
  | _, .root, _ => fun address =>
      match address with
      | .initial .root => .initial
  | _, .extend previous step, admitted => fun address =>
      match address with
      | .old old => liftDemand step (classify choose previous admitted.1 old)
      | .fresh position => .atStep .last (Role.ofPosition position)
termination_by structural _ history _ => history

theorem locate_lift (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (step : Step Token middle target)
    (admitted : Admissible choose (.extend history step)) (demand : Demand history) :
    locate choose (.extend history step) admitted (liftDemand step demand) =
      .old (locate choose history admitted.1 demand) := by
  cases demand <;> rfl

theorem locate_latest (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    locate choose history admitted (latest history) = (build choose history admitted).frame.focus := by
  cases history <;> rfl

theorem classify_locate (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) (demand : Demand history) :
    classify choose history admitted (locate choose history admitted demand) = demand := by
  induction history with
  | root =>
      cases demand with
      | initial => rfl
      | atStep occurrence role => cases occurrence
  | extend previous step ih =>
      cases demand with
      | initial => exact congrArg (liftDemand step) (ih admitted.1 .initial)
      | atStep occurrence role =>
          cases occurrence with
          | last => exact congrArg (Demand.atStep .last) (Role.of_position role)
          | earlier old => exact congrArg (liftDemand step) (ih admitted.1 (.atStep old role))

theorem locate_classify (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history)
    (address : Address (build choose history admitted).frame.layout) :
    locate choose history admitted (classify choose history admitted address) = address := by
  induction history with
  | root => cases address with | initial position => cases position; rfl
  | extend previous step ih =>
      cases address with
      | old address =>
          exact (locate_lift choose previous step admitted _).trans (congrArg Address.old (ih admitted.1 address))
      | fresh position => exact congrArg Address.fresh (Role.position_of position)

def demandTransport (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    ExactTransport (Demand history) (Address (build choose history admitted).frame.layout) where
  forward := locate choose history admitted
  backward := classify choose history admitted
  forwardBackward := classify_locate choose history admitted
  backwardForward := locate_classify choose history admitted

/-- All independently declared meanings are certified from the actual constructed values. -/
theorem fulfills (choose : List Token → Token) : {target : List Token} →
    (history : History (Step Token) [] target) → (admitted : Admissible choose history) →
    (demand : Demand history) →
    (build choose history admitted).frame.support.read (locate choose history admitted demand) = expected demand
  | _, .root, _, .initial => rfl
  | _, .extend previous _, admitted, .initial => fulfills choose previous admitted.1 .initial
  | _, .extend previous _, admitted, .atStep (.earlier occurrence) role =>
      fulfills choose previous admitted.1 (.atStep occurrence role)
  | _, .extend previous step, admitted, .atStep .last role => by
      let old := build choose previous admitted.1
      have output := old.output_exact
      have selected : choose old.frame.output = token step := (congrArg choose output).trans admitted.2.symm
      cases step with
      | record value =>
          cases role with
          | result =>
              exact (congrArg (fun token => token :: old.frame.output) selected).trans
                (congrArg (List.cons value) output)
          | emission => exact congrArg (fun value => [value]) selected
          | reuse => exact output
termination_by structural _ history _ _ => history

theorem every_resource_certified (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history)
    (address : Address (build choose history admitted).frame.layout) :
    (build choose history admitted).frame.support.read address = expected (classify choose history admitted address) :=
  (congrArg (build choose history admitted).frame.support.read (locate_classify choose history admitted address)).symm.trans
    (fulfills choose history admitted _)

namespace ListMaps
universe a b c
theorem compose {A : Type a} {B : Type b} {C : Type c} (first : A → B) (second : B → C) (items : List A) :
    (items.map first).map second = items.map (fun value => second (first value)) :=
  DemandClosure.FiniteList.mapCompose first second items

theorem agree {A : Type a} {B : Type b} (first second : A → B) (same : ∀ value, first value = second value)
    (items : List A) : items.map first = items.map second :=
  DemandClosure.FiniteList.mapAgree first second same items
end ListMaps

theorem declared_dependencies_lift {middle target : List Token} {history : History (Step Token) [] middle}
    (step : Step Token middle target) (demand : Demand history) :
    declaredDependencies (liftDemand step demand) = (declaredDependencies demand).map (liftDemand step) := by
  cases demand with
  | initial => rfl
  | atStep occurrence role => cases role <;> rfl

theorem dependencies_lift_covered (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (step : Step Token middle target)
    (admitted : Admissible choose (.extend history step)) (demand : Demand history)
    (prior : (build choose history admitted.1).frame.support.dependencies (locate choose history admitted.1 demand) =
      (declaredDependencies demand).map (locate choose history admitted.1)) :
    (build choose (.extend history step) admitted).frame.support.dependencies
        (locate choose (.extend history step) admitted (liftDemand step demand)) =
      (declaredDependencies (liftDemand step demand)).map (locate choose (.extend history step) admitted) := by
  rw [locate_lift, declared_dependencies_lift]
  change ((build choose history admitted.1).frame.support.nodeAt
    (locate choose history admitted.1 demand) |>.map Address.old).inputs = _
  exact (Node.inputs_map _ _).trans
    ((congrArg (List.map Address.old) prior).trans
      ((ListMaps.compose _ _ _).trans
        ((ListMaps.agree _ _ (fun old => (locate_lift choose history step admitted old).symm) _).trans
          (ListMaps.compose _ _ _).symm)))

/-- Every direct prerequisite is represented exactly, including its slot and multiplicity. -/
theorem dependencies_covered (choose : List Token → Token) : {target : List Token} →
    (history : History (Step Token) [] target) → (admitted : Admissible choose history) →
    (demand : Demand history) →
    (build choose history admitted).frame.support.dependencies (locate choose history admitted demand) =
      (declaredDependencies demand).map (locate choose history admitted)
  | _, .root, _, .initial => rfl
  | _, .extend previous step, admitted, .initial =>
      dependencies_lift_covered choose previous step admitted .initial
        (dependencies_covered choose previous admitted.1 .initial)
  | _, .extend previous step, admitted, .atStep (.earlier occurrence) role =>
      dependencies_lift_covered choose previous step admitted (.atStep occurrence role)
        (dependencies_covered choose previous admitted.1 (.atStep occurrence role))
  | _, .extend _ _, _, .atStep .last .result => rfl
  | _, .extend _ _, _, .atStep .last .emission => rfl
  | _, .extend previous step, admitted, .atStep .last .reuse =>
      congrArg (fun address => [address])
        ((locate_lift choose previous step admitted (latest previous)).trans
          (congrArg Address.old (locate_latest choose previous admitted.1))).symm
termination_by structural _ history _ _ => history

/-- Positive data combining coverage, every semantic certificate, and a finite enumeration. -/
structure CompleteRealization (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) where
  realization : Realization choose history
  coordinates : ExactTransport (Demand history) (Address realization.frame.layout)
  certified : ∀ demand, realization.frame.support.read (coordinates.forward demand) = expected demand
  ruleCertified : ∀ address, realization.frame.support.read address =
    (realization.frame.support.nodeAt address).eval realization.frame.support.read
  coveredDependencies : ∀ demand, realization.frame.support.dependencies (coordinates.forward demand) =
    (declaredDependencies demand).map coordinates.forward
  resources : List (Address realization.frame.layout)
  exhaustive : ∀ address, address ∈ resources
  unique : resources.Nodup
  counted : resources.length = realization.frame.layout.size
  terminal : realization.frame.output = target

def complete (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    CompleteRealization choose history where
  realization := build choose history admitted
  coordinates := demandTransport choose history admitted
  certified := fulfills choose history admitted
  ruleCertified := (build choose history admitted).frame.support.read_correct
  coveredDependencies := dependencies_covered choose history admitted
  resources := (build choose history admitted).frame.layout.addresses
  exhaustive := (build choose history admitted).frame.layout.addresses_complete
  unique := (build choose history admitted).frame.layout.addresses_nodup
  counted := (build choose history admitted).frame.layout.addresses_length
  terminal := (build choose history admitted).output_exact

theorem complete_coverage_iff (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) :
    Admissible choose history ↔ Nonempty (CompleteRealization choose history) :=
  ⟨fun admitted => ⟨complete choose history admitted⟩,
    fun ⟨result⟩ => realization_admissible choose result.realization⟩

theorem complete_size (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    (complete choose history admitted).realization.frame.layout.size = 1 + history.length * 3 :=
  (congrArg (fun frame : Configuration Token => frame.layout.size) (build_frame choose history admitted)).trans
    (run_size choose history.length)

theorem admitted_history_exact (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    packed ((rule choose).run (initial Token) history.length).1 = ⟨target, history⟩ :=
  (congrArg packed (build_frame choose history admitted)).symm.trans (build choose history admitted).exact

theorem generated_iff_admissible (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) :
    (∃ depth, packed ((rule choose).run (initial Token) depth).1 = ⟨target, history⟩) ↔
      Admissible choose history := by
  constructor
  · intro ⟨depth, equality⟩
    exact (congrArg (fun recorded : OperationalHistory Token => Admissible choose recorded.2) equality) ▸
      execution_admissible choose ((rule choose).run (initial Token) depth).2
  · intro admitted
    exact ⟨history.length, admitted_history_exact choose history admitted⟩

theorem admitted_target (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    target = trajectory choose history.length :=
  (build choose history admitted).output_exact.symm.trans
    ((congrArg Frame.output (build_frame choose history admitted)).trans (run_output choose history.length))

/-- Token equality is the sole additional parameter needed for executable admission checking. -/
def admissionDecision (choose : List Token → Token) [DecidableEq Token] {source : List Token} :
    {target : List Token} → (history : History (Step Token) source target) → Decidable (Admissible choose history)
  | _, .root => .isTrue True.intro
  | _, .extend previous step =>
      match admissionDecision choose previous with
      | .isFalse rejected => .isFalse (fun admitted => rejected admitted.1)
      | .isTrue prior =>
          match (inferInstanceAs (Decidable (token step = choose _)) :
              Decidable (LocalAdmission choose step)) with
          | .isTrue allowed => .isTrue ⟨prior, allowed⟩
          | .isFalse rejected => .isFalse (fun admitted => rejected admitted.2)
termination_by structural _ history => history

/-- Eliminate a constructive decision into the complete producer or its rejection witness. -/
def checkAdmission (choose : List Token → Token) {target : List Token}
    (history : History (Step Token) [] target) :
    Decidable (Admissible choose history) →
    CompleteRealization choose history ⊕ PLift (¬ Admissible choose history)
  | .isTrue admitted => .inl (complete choose history admitted)
  | .isFalse rejected => .inr ⟨rejected⟩

/-- Successful checking returns the whole certified construction, including all its witnesses. -/
def check (choose : List Token → Token) [DecidableEq Token] {target : List Token}
    (history : History (Step Token) [] target) :
    CompleteRealization choose history ⊕ PLift (¬ Admissible choose history) :=
  checkAdmission choose history (admissionDecision choose history)

theorem check_complete (choose : List Token → Token) [DecidableEq Token] {target : List Token}
    (history : History (Step Token) [] target) (admitted : Admissible choose history) :
    ∃ result, check choose history = .inl result := by
  cases decision : admissionDecision choose history with
  | isTrue allowed =>
      exact ⟨complete choose history allowed, congrArg (checkAdmission choose history) decision⟩
  | isFalse rejected => exact False.elim (rejected admitted)

theorem check_rejects (choose : List Token → Token) [DecidableEq Token] {target : List Token}
    (history : History (Step Token) [] target) (rejected : ¬ Admissible choose history) :
    ∃ reason, check choose history = .inr ⟨reason⟩ := by
  cases decision : admissionDecision choose history with
  | isTrue allowed => exact False.elim (rejected allowed)
  | isFalse reason => exact ⟨reason, congrArg (checkAdmission choose history) decision⟩

def appendDemand {middle : List Token} (history : History (Step Token) [] middle) :
    {target : List Token} → (following : History (Step Token) middle target) →
    Demand history → Demand (History.append history following)
  | _, .root, demand => demand
  | _, .extend previous step, demand => liftDemand step (appendDemand history previous demand)
termination_by structural _ following _ => following

theorem expected_lift {middle target : List Token} {history : History (Step Token) [] middle}
    (step : Step Token middle target) (demand : Demand history) :
    expected (liftDemand step demand) = expected demand := by
  cases demand <;> rfl

theorem expected_appendDemand {middle target : List Token} (history : History (Step Token) [] middle)
    (following : History (Step Token) middle target) (demand : Demand history) :
    expected (appendDemand history following demand) = expected demand := by
  induction following with
  | root => rfl
  | extend previous step ih => exact (expected_lift step _).trans ih

/-- Continue from the support actually built for the prefix. -/
def resume (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target) :
    (last : Configuration Token) × Execution (rule choose) (build choose history admitted).frame last :=
  (rule choose).run (build choose history admitted).frame following.length

theorem resume_equals_build (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target) (allowed : Admissible choose following) :
    (resume choose history admitted following).1 =
      (build choose (History.append history following) ((admissible_append choose history following).mpr
        ⟨admitted, allowed⟩)).frame := by
  have built := build_frame choose (History.append history following)
    ((admissible_append choose history following).mpr ⟨admitted, allowed⟩)
  rw [History.length_append] at built
  exact ((congrArg (fun frame => ((rule choose).run frame following.length).1)
    (build_frame choose history admitted)).trans ((rule choose).run_add (initial Token) _ _).symm).trans built.symm

theorem resume_history_exact (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target) (allowed : Admissible choose following) :
    packed (resume choose history admitted following).1 = ⟨target, History.append history following⟩ :=
  (congrArg packed (resume_equals_build choose history admitted following allowed)).trans
    (build choose (History.append history following)
      ((admissible_append choose history following).mpr ⟨admitted, allowed⟩)).exact

theorem resume_preserves (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target)
    (address : Address (build choose history admitted).frame.layout) :
    (resume choose history admitted following).1.support.nodeAt
        ((resume choose history admitted following).2.embed address) =
      ((build choose history admitted).frame.support.nodeAt address).map
        (resume choose history admitted following).2.embed :=
  (resume choose history admitted following).2.node_preserved address

theorem resume_certified_old (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target) (demand : Demand history) :
    (resume choose history admitted following).1.support.read
        ((resume choose history admitted following).2.embed (locate choose history admitted demand)) =
      expected (appendDemand history following demand) :=
  ((resume choose history admitted following).2.read_preserved _).trans
    ((fulfills choose history admitted demand).trans (expected_appendDemand history following demand).symm)

theorem resume_dependencies_preserved (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target)
    (address : Address (build choose history admitted).frame.layout) :
    (resume choose history admitted following).1.support.dependencies
        ((resume choose history admitted following).2.embed address) =
      ((build choose history admitted).frame.support.dependencies address).map
        (resume choose history admitted following).2.embed :=
  (resume choose history admitted following).2.resources.dependencies_preserved address

theorem resume_relation_iff (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target)
    (parent child : Address (build choose history admitted).frame.layout) :
    (resume choose history admitted following).1.support.Depends
        ((resume choose history admitted following).2.embed parent)
        ((resume choose history admitted following).2.embed child) ↔
      (build choose history admitted).frame.support.Depends parent child :=
  ⟨(resume choose history admitted following).2.relation_reflected,
    (resume choose history admitted following).2.relation_preserved⟩

/-- Actual continuation transports compose, independently of any equality of terminal values. -/
theorem resume_transport_compose (choose : List Token → Token) {middle target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (following : History (Step Token) middle target) (depth : Nat)
    (address : Address (build choose history admitted).frame.layout) :
    let one := resume choose history admitted following
    let two := (rule choose).run one.1 depth
    (one.2.compose two.2).embed address = two.2.embed (one.2.embed address) :=
  Execution.embed_compose _ _ _

theorem resume_compose (choose : List Token → Token) {middle next target : List Token}
    (history : History (Step Token) [] middle) (admitted : Admissible choose history)
    (one : History (Step Token) middle next) (two : History (Step Token) next target) :
    (resume choose history admitted (History.append one two)).1 =
      ((rule choose).run (resume choose history admitted one).1 two.length).1 := by
  change ((rule choose).run (build choose history admitted).frame (History.append one two).length).1 = _
  rw [History.length_append]
  exact (rule choose).run_add _ _ _

/-- The independently admitted family retains the already established absence of a common bound. -/
theorem admitted_supports_unbounded (choose : List Token → Token) (bound : Nat) :
    ∃ recorded : OperationalHistory Token, ∃ admitted : Admissible choose recorded.2,
      bound < (complete choose recorded.2 admitted).resources.length := by
  obtain ⟨depth, growth⟩ := supports_unbounded choose bound
  let actual := (rule choose).run (initial Token) depth
  have admitted := execution_admissible choose actual.2
  refine ⟨packed actual.1, admitted, ?_⟩
  have length_exact : actual.1.history.length = depth :=
    ((rule choose).run_history_length (initial Token) depth).trans (Nat.zero_add _)
  have same_frame := build_frame choose actual.1.history admitted
  rw [length_exact] at same_frame
  exact (complete choose actual.1.history admitted).counted ▸
    (congrArg (fun frame : Configuration Token => frame.layout.size) same_frame).symm ▸ growth

end RelationalFoundations.FeedbackCoverage
