import RelationalFoundations.FiniteRuleConstruction
import RelationalFoundations.HeterogeneousFeedback
set_option genInjectivity false

namespace RelationalFoundations.FiniteRuleInstances
open FiniteRuleConstruction
open ResourceGraph DemandClosure




universe u

def unitFinite : Finite (Packed (fun _ : Unit => Unit)) where
  items := [⟨(), ()⟩]
  exhaustive := fun ⟨kind, value⟩ => by cases kind; cases value; exact .head _
  unique := .cons (fun _ impossible => nomatch impossible) .nil

def positionsFinite : Finite (Packed (fun _ : Unit => Position (.branch .leaf .leaf))) where
  items := (Shape.positions (.branch .leaf .leaf)).map (fun p => ⟨(), p⟩)
  exhaustive := fun ⟨kind, position⟩ => by
    cases kind
    exact FiniteList.mappedMember (fun p => (⟨(), p⟩ : Packed (fun _ : Unit => Position (.branch .leaf .leaf)))) (Shape.positions_complete _ position)
  unique := Enumeration.nodup_map (fun p => (⟨(), p⟩ : Packed (fun _ : Unit => Position (.branch .leaf .leaf))))
    (fun _ _ same => eq_of_heq (Sigma.mk.inj same).2) (Shape.positions_nodup _)

def homogeneousSplit {Token : Type u} (choose : List Token → Token) (frame : HistoricalFeedback.Configuration Token) :
    ExactTransport (Address frame.layout ⊕ Position (.branch .leaf .leaf)) (Address ((HistoricalFeedback.rule choose).advance frame).layout) where
  forward := fun value => match value with | .inl ref => .old ref | .inr slot => .fresh slot
  backward := fun ref => match ref with | .old old => .inl old | .fresh slot => .inr slot
  forwardBackward := fun value => by cases value <;> rfl
  backwardForward := fun ref => by cases ref <;> rfl

def homogeneousExpected {Token : Type u} {source target : List Token} (step : HistoricalFeedback.Step Token source target) :
    Position (.branch .leaf .leaf) → List Token
  | .root => target
  | .left .root => [HistoricalFeedback.token step]
  | .right .root => source

def homogeneous (Token : Type u) (choose : List Token → Token) : Rules.{u} where
  State := List Token
  Step := HistoricalFeedback.Step Token
  origin := []
  allowed := FeedbackCoverage.LocalAdmission choose
  Kind := Unit
  Value := fun _ => List Token
  Initial := fun _ => Unit
  New := fun {a b} step kind => Position (.branch .leaf .leaf)
  initialExpected := fun _ _ => []
  newExpected := fun {a b} step kind => homogeneousExpected step
  initialFinite := unitFinite
  newFinite := fun {a b} step => positionsFinite
  Frame := HistoricalFeedback.Configuration Token
  recorded := FeedbackCoverage.packed
  Ref := fun frame _ => Address frame.layout
  Node := fun frame _ => ResourceGraph.Node Token (Address frame.layout)
  read := fun frame _ => frame.support.read
  node := fun frame _ => frame.support.nodeAt
  inputs := fun {frame} {kind} node => node.inputs.map (fun ref => ⟨(), ref⟩)
  eval := fun {frame} read {kind} node => node.eval (read ())
  map := fun {a b} f {kind} node => node.map (f ())
  map_id := fun {a} {kind} node => Node.map_id node
  map_comp := fun {a b c} one two {kind} node => Node.map_comp (one ()) (two ()) node
  inputs_map := fun {a b} f {kind} node => by cases node <;> rfl
  eval_map := fun {a b} f read {kind} node => Node.eval_map (f ()) (read ()) node
  eval_congr := fun {a} one two same {kind} node => by
    cases node with
    | empty => rfl
    | emit _ => rfl
    | reuse ref => exact same () ref
    | join left right =>
        exact (congrArg (fun value => value ++ one () right) (same () left)).trans
          (congrArg (List.append (two () left)) (same () right))
  initial := HistoricalFeedback.initial Token
  initial_recorded := rfl
  initialCoordinates := fun _ =>
    { forward := fun _ => .initial .root
      backward := fun _ => ()
      forwardBackward := fun value => by cases value; rfl
      backwardForward := fun ref => by cases ref with | initial position => cases position; rfl }
  initial_values := fun _ _ => rfl
  initial_rules := fun _ ref => Support.read_correct _ ref
  valid := fun frame => frame.output = frame.target
  initial_valid := rfl
  advance := (HistoricalFeedback.rule choose).advance
  Result := fun _ => List Token
  produce := (HistoricalFeedback.rule choose).produced
  react := (HistoricalFeedback.rule choose).react
  advance_recorded := fun _ => rfl
  advance_valid := fun frame valid => congrArg (List.cons (choose frame.output)) valid
  reaction_allowed := fun frame valid => congrArg choose valid
  reaction_exact := fun frame valid {target} step allowed => by
    cases step with
    | record token =>
        change token = choose frame.target at allowed
        change (⟨choose frame.output :: frame.target, HistoricalFeedback.Step.record frame.target (choose frame.output)⟩ :
          (target : List Token) × HistoricalFeedback.Step Token frame.target target) =
          ⟨token :: frame.target, HistoricalFeedback.Step.record frame.target token⟩
        rw [valid, ← allowed]
  split := fun frame _ => homogeneousSplit choose frame
  old_values := fun _ _ _ => rfl
  old_nodes := fun _ _ _ => rfl
  new_values := fun frame valid _ slot => by
    cases slot with
    | root => exact congrArg (List.cons (choose frame.output)) valid
    | left position => cases position; rfl
    | right position => cases position; exact valid
  new_rules := fun frame _ slot => Support.read_correct ((HistoricalFeedback.rule choose).advance frame).support (.fresh slot)
  visible := OutputDriven.Frame.output
  visible_valid := fun _ valid => valid

def unpack {context : List TypedResources.Kind} : TypedResources.AnyRef context → Packed (TypedResources.Ref context)
  | .number ref => ⟨.number, ref⟩
  | .truth ref => ⟨.truth, ref⟩

def pack {context : List TypedResources.Kind} : Packed (TypedResources.Ref context) → TypedResources.AnyRef context
  | ⟨kind, ref⟩ => TypedResources.AnyRef.pack kind ref

theorem unpack_pack {context : List TypedResources.Kind} (ref : Packed (TypedResources.Ref context)) : unpack (pack ref) = ref := by
  cases ref with | mk kind ref => cases kind <;> rfl

theorem pack_unpack {context : List TypedResources.Kind} (ref : TypedResources.AnyRef context) : pack (unpack ref) = ref := by
  cases ref <;> rfl

def typedFinite (context : List TypedResources.Kind) : Finite (Packed (TypedResources.Ref context)) where
  items := (TypedResources.references context).map unpack
  exhaustive := fun ref => (unpack_pack ref) ▸ FiniteList.mappedMember unpack (TypedResources.references_all context (pack ref))
  unique := Enumeration.nodup_map unpack
    (fun a b same => (pack_unpack a).symm.trans ((congrArg pack same).trans (pack_unpack b))) (TypedResources.references_unique context)

def singletonValue (added : TypedResources.Kind) (value : TypedResources.Value added) : ∀ kind, TypedResources.Ref [added] kind → TypedResources.Value kind
  | _, .head => value
  | _, .old ref => nomatch ref

def typedSplit (context : List TypedResources.Kind) (added kind : TypedResources.Kind) :
    ExactTransport (TypedResources.Ref context kind ⊕ TypedResources.Ref [added] kind) (TypedResources.Ref (added :: context) kind) where
  forward := fun value => match value with
    | .inl old => .old old
    | .inr fresh => match fresh with | .head => .head | .old ref => nomatch ref
  backward := fun ref => match ref with | .head => .inr .head | .old old => .inl old
  forwardBackward := fun value => by
    cases value with
    | inl _ => rfl
    | inr fresh => cases fresh with | head => rfl | old ref => cases ref
  backwardForward := fun ref => by cases ref <;> rfl

def heteroProduce {seed : Nat} : HeterogeneousFeedback.Frame seed → Nat × Bool
  | ⟨.ready number, data⟩ => match data.focus with
      | .ready numeric => (number, TypedResources.test (data.support.read .number numeric))
  | ⟨.observed _ _, data⟩ => match data.focus with
      | .observed numeric boolean =>
          (TypedResources.adjust (data.support.read .truth boolean) (data.support.read .number numeric), data.support.read .truth boolean)
  | ⟨.updated _, data⟩ => match data.focus with
      | .updated numeric => (data.support.read .number numeric, false)

def heteroReact {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (result : Nat × Bool) : (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step frame.1 target :=
  match frame with
  | ⟨.ready number, _⟩ => ⟨.observed number result.2, .observe number result.2⟩
  | ⟨.observed number flag, _⟩ => ⟨.updated result.1, .act number flag result.2 result.1⟩
  | ⟨.updated number, _⟩ => ⟨.ready result.1, .reuse number result.1⟩

def heteroSplit {seed : Nat} (frame : HeterogeneousFeedback.Frame seed) (kind : TypedResources.Kind) :
    ExactTransport (TypedResources.Ref frame.2.context kind ⊕ TypedResources.Ref [(heteroReact frame (heteroProduce frame)).2.kind] kind)
      (TypedResources.Ref (HeterogeneousFeedback.advance frame).2.context kind) := by
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> exact typedSplit context _ kind

theorem unpack_map {a b : List TypedResources.Kind} (f : ∀ kind, TypedResources.Ref a kind → TypedResources.Ref b kind) (ref : TypedResources.AnyRef a) :
    unpack (TypedResources.AnyRef.map f ref) = rename f (unpack ref) := by cases ref <;> rfl

def heterogeneous (seed : Nat) : Rules where
  State := HeterogeneousFeedback.State
  Step := HeterogeneousFeedback.Step
  origin := .ready seed
  allowed := HeterogeneousFeedback.LocalAdmission
  Kind := TypedResources.Kind
  Value := TypedResources.Value
  Initial := TypedResources.Ref [.number]
  New := fun {a b} step => TypedResources.Ref [step.kind]
  initialExpected := singletonValue .number seed
  newExpected := fun {a b} step => singletonValue step.kind step.value
  initialFinite := typedFinite [.number]
  newFinite := fun {a b} step => typedFinite [step.kind]
  Frame := HeterogeneousFeedback.Frame seed
  recorded := fun frame => ⟨frame.1, frame.2.history⟩
  Ref := fun frame => TypedResources.Ref frame.2.context
  Node := fun frame => TypedResources.Operation frame.2.context
  read := fun frame => frame.2.support.read
  node := fun frame => frame.2.support.nodeAt
  inputs := fun {frame} {kind} node => node.inputs.map unpack
  eval := fun {frame} read {kind} node => TypedResources.Operation.eval read node
  map := fun {a b} f {kind} node => TypedResources.Operation.map f node
  map_id := fun {a} {kind} node => TypedResources.Operation.map_id node
  map_comp := fun {a b c} one two {kind} node => TypedResources.Operation.map_comp one two node
  inputs_map := fun {a b} f {kind} node =>
    (congrArg (List.map unpack) (TypedResources.Operation.inputs_map f node)).trans
      ((FeedbackCoverage.ListMaps.compose _ _ _).trans
        ((FeedbackCoverage.ListMaps.agree _ _ (unpack_map f) _).trans (FeedbackCoverage.ListMaps.compose _ _ _).symm))
  eval_map := fun {a b} f read {kind} node => TypedResources.Operation.eval_map f read node
  eval_congr := fun {a} one two same {kind} node => by
    cases node with
    | literal _ => rfl
    | test numeric => exact congrArg TypedResources.test (same .number numeric)
    | adjust boolean numeric =>
        exact (congrArg (fun flag => TypedResources.adjust flag (one .number numeric)) (same .truth boolean)).trans
          (congrArg (TypedResources.adjust (two .truth boolean)) (same .number numeric))
    | reuse ref => exact same _ ref
  initial := HeterogeneousFeedback.initial seed
  initial_recorded := rfl
  initialCoordinates := fun kind => ExactTransport.reflexive (TypedResources.Ref [.number] kind)
  initial_values := fun kind ref => by cases ref with | head => rfl | old ref => cases ref
  initial_rules := (HeterogeneousFeedback.initial seed).2.support.read_correct
  valid := HeterogeneousFeedback.Valid
  initial_valid := HeterogeneousFeedback.initial_valid seed
  advance := HeterogeneousFeedback.advance
  Result := fun _ => Nat × Bool
  produce := heteroProduce
  react := heteroReact
  advance_recorded := fun frame => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus <;> rfl
  advance_valid := HeterogeneousFeedback.advance_valid
  reaction_allowed := fun frame valid => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus with
    | ready numeric => exact congrArg TypedResources.test valid
    | observed numeric boolean => exact ⟨valid.2,
        (congrArg (fun flag => TypedResources.adjust flag (support.read .number numeric)) valid.2).trans
          (congrArg (TypedResources.adjust _) valid.1)⟩
    | updated numeric => exact valid
  reaction_exact := fun frame valid {target} step allowed => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus with
    | @ready number numeric =>
        cases step
        change _ = TypedResources.test _ at allowed
        change support.read .number numeric = _ at valid
        have valueSame := (congrArg TypedResources.test valid).trans allowed.symm
        exact congrArg (fun flag => (⟨.observed number flag, .observe number flag⟩ :
          (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step (.ready number) target)) valueSame
    | @observed number flag numeric boolean =>
        cases step
        change _ = _ ∧ _ = TypedResources.adjust _ _ at allowed
        change support.read .number numeric = _ ∧ support.read .truth boolean = _ at valid
        have valueSame := ((congrArg (fun flag => TypedResources.adjust flag (support.read .number numeric)) valid.2).trans
          (congrArg (TypedResources.adjust _) valid.1)).trans allowed.2.symm
        exact congrArg (fun result : Nat × Bool => (⟨.updated result.1, .act number flag result.2 result.1⟩ :
          (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step (.observed number flag) target))
          ((congrArg (fun number => (number, support.read .truth boolean)) valueSame).trans
            (congrArg (Prod.mk _) (valid.2.trans allowed.1.symm)))
    | @updated number numeric =>
        cases step
        change _ = _ at allowed
        change support.read .number numeric = _ at valid
        exact congrArg (fun result => (⟨.ready result, .reuse number result⟩ :
          (target : HeterogeneousFeedback.State) × HeterogeneousFeedback.Step (.updated number) target)) (valid.trans allowed.symm)
  split := heteroSplit
  old_values := fun frame kind ref => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus <;> rfl
  old_nodes := fun frame kind ref => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus <;> rfl
  new_values := fun frame _ kind slot => by
    rcases frame with ⟨state, history, context, support, focus⟩
    cases focus <;> cases slot with
    | head => rfl
    | old ref => cases ref
  new_rules := fun frame kind slot => (HeterogeneousFeedback.advance frame).2.support.read_correct kind ((heteroSplit frame kind).forward (.inr slot))
  visible := HeterogeneousFeedback.visible
  visible_valid := HeterogeneousFeedback.visible_valid

theorem homogeneousAdmission (Token : Type u) (choose : List Token → Token) {source target : List Token}
    (history : History (HistoricalFeedback.Step Token) source target) :
    (homogeneous Token choose).Admissible history ↔ FeedbackCoverage.Admissible choose history := by
  induction history with
  | root => exact ⟨fun h => h, fun h => h⟩
  | extend previous step ih => exact ⟨fun h => ⟨ih.mp h.1, h.2⟩, fun h => ⟨ih.mpr h.1, h.2⟩⟩

theorem heterogeneousAdmission (seed : Nat) {source target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step source target) :
    (heterogeneous seed).Admissible history ↔ HeterogeneousFeedback.Admissible history := by
  induction history with
  | root => exact ⟨fun h => h, fun h => h⟩
  | extend previous step ih => exact ⟨fun h => ⟨ih.mp h.1, h.2⟩, fun h => ⟨ih.mpr h.1, h.2⟩⟩

/-- These constructors invoke the common result; every contract field above is
closed by an origin or one-step producer and proof, without global coverage. -/
def homogeneousComplete (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :=
  (homogeneous Token choose).complete history ((homogeneousAdmission Token choose history).mpr allowed)

def heterogeneousComplete {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :=
  (heterogeneous seed).complete history ((heterogeneousAdmission seed history).mpr allowed)

theorem homogeneousRun (Token : Type u) (choose : List Token → Token) (frame : HistoricalFeedback.Configuration Token) (depth : Nat) :
    ((homogeneous Token choose).run frame depth).1 = ((HistoricalFeedback.rule choose).run frame depth).1 := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact congrArg (HistoricalFeedback.rule choose).advance ih

theorem heterogeneousRun (seed : Nat) (frame : HeterogeneousFeedback.Frame seed) (depth : Nat) :
    ((heterogeneous seed).run frame depth).1 = (HeterogeneousFeedback.run frame depth).1 := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact congrArg HeterogeneousFeedback.advance ih

/-- Equality of the entire frame includes history, all resource identities,
operator syntax, ordered input references, and the operational focus. -/
theorem homogeneousFrame (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :
    (homogeneousComplete Token choose history allowed).realization.frame = (FeedbackCoverage.complete choose history allowed).realization.frame :=
  ((homogeneous Token choose).build_run history _).trans
    ((homogeneousRun Token choose _ _).trans (FeedbackCoverage.build_frame choose history allowed).symm)

theorem heterogeneousFrame {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :
    (heterogeneousComplete history allowed).realization.frame = (HeterogeneousFeedback.complete history allowed).realization.frame :=
  ((heterogeneous seed).build_run history _).trans
    ((heterogeneousRun seed _ _).trans (HeterogeneousFeedback.build_run history allowed).symm)

def homogeneousRequest (Token : Type u) (choose : List Token → Token) : {target : List Token} →
    (history : History (HistoricalFeedback.Step Token) [] target) →
    (homogeneous Token choose).Requests history () → FeedbackCoverage.Demand history
  | _, .root, _ => .initial
  | _, .extend previous step, request => match request with
      | .inl old => FeedbackCoverage.liftDemand step (homogeneousRequest Token choose previous old)
      | .inr slot => .atStep .last (FeedbackCoverage.Role.ofPosition slot)
termination_by structural _ history _ => history

def homogeneousRequestBack (Token : Type u) (choose : List Token → Token) : {target : List Token} →
    (history : History (HistoricalFeedback.Step Token) [] target) → FeedbackCoverage.Demand history →
    (homogeneous Token choose).Requests history ()
  | _, .root, .initial => ()
  | _, .root, .atStep occurrence _ => nomatch occurrence
  | _, .extend previous _, .initial => .inl (homogeneousRequestBack Token choose previous .initial)
  | _, .extend _ _, .atStep .last role => .inr role.position
  | _, .extend previous _, .atStep (.earlier occurrence) role =>
      .inl (homogeneousRequestBack Token choose previous (.atStep occurrence role))
termination_by structural _ history _ => history

theorem homogeneousRequest_lift (Token : Type u) (choose : List Token → Token) {middle target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] middle) (step : HistoricalFeedback.Step Token middle target)
    (demand : FeedbackCoverage.Demand history) :
    homogeneousRequestBack Token choose (.extend history step) (FeedbackCoverage.liftDemand step demand) =
      .inl (homogeneousRequestBack Token choose history demand) := by cases demand <;> rfl

def homogeneousRequests (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) :
    ExactTransport ((homogeneous Token choose).Requests history ()) (FeedbackCoverage.Demand history) where
  forward := homogeneousRequest Token choose history
  backward := homogeneousRequestBack Token choose history
  forwardBackward := fun request => by
    induction history with
    | root => cases request; rfl
    | extend previous step ih =>
        cases request with
        | inl old => exact (homogeneousRequest_lift Token choose previous step _).trans (congrArg Sum.inl (ih old))
        | inr slot => exact congrArg Sum.inr (FeedbackCoverage.Role.position_of slot)
  backwardForward := fun demand => by
    induction history with
    | root => cases demand with | initial => rfl | atStep occurrence _ => cases occurrence
    | extend previous step ih =>
        cases demand with
        | initial => exact congrArg (FeedbackCoverage.liftDemand step) (ih .initial)
        | atStep occurrence role =>
            cases occurrence with
            | last => exact congrArg (FeedbackCoverage.Demand.atStep .last) (FeedbackCoverage.Role.of_position role)
            | earlier occurrence => exact congrArg (FeedbackCoverage.liftDemand step) (ih (.atStep occurrence role))

theorem homogeneous_expected_lift {Token : Type u} {middle target : List Token}
    {history : History (HistoricalFeedback.Step Token) [] middle} (step : HistoricalFeedback.Step Token middle target)
    (demand : FeedbackCoverage.Demand history) :
    FeedbackCoverage.expected (FeedbackCoverage.liftDemand step demand) = FeedbackCoverage.expected demand := by
  cases demand <;> rfl

theorem homogeneousMeanings (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (request : (homogeneous Token choose).Requests history ()) :
    (homogeneous Token choose).expected history () request = FeedbackCoverage.expected ((homogeneousRequests Token choose history).forward request) := by
  induction history with
  | root => rfl
  | extend previous step ih =>
      cases request with
      | inl old => exact (ih old).trans (homogeneous_expected_lift step (homogeneousRequest Token choose previous old)).symm
      | inr slot => cases slot with
          | root => rfl
          | left position => cases position; rfl
          | right position => cases position; rfl

def heterogeneousRequests {seed : Nat} : {target : HeterogeneousFeedback.State} →
    (history : History HeterogeneousFeedback.Step (.ready seed) target) → (kind : TypedResources.Kind) →
    ExactTransport ((heterogeneous seed).Requests history kind) (TypedResources.Ref (HeterogeneousFeedback.declaredContext history) kind)
  | _, .root, _kind => ExactTransport.reflexive _
  | _, .extend previous step, kind =>
      (sumLeft (heterogeneousRequests previous kind)).compose (typedSplit (HeterogeneousFeedback.declaredContext previous) step.kind kind)
termination_by structural _ history _ => history

theorem heterogeneousMeanings {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (kind : TypedResources.Kind)
    (request : (heterogeneous seed).Requests history kind) :
    (heterogeneous seed).expected history kind request = HeterogeneousFeedback.expected history kind
      ((heterogeneousRequests history kind).forward request) := by
  induction history with
  | root => cases request with | head => rfl | old ref => cases ref
  | extend previous step ih =>
      cases request with
      | inl old => cases step <;> exact ih old
      | inr slot => cases step <;> cases slot with | head => rfl | old ref => cases ref

def homogeneousExecution (Token : Type u) (choose : List Token → Token) {first : HistoricalFeedback.Configuration Token} :
    {last : HistoricalFeedback.Configuration Token} → (homogeneous Token choose).Execution first last →
    OutputDriven.Execution (HistoricalFeedback.rule choose) first last
  | _, .idle => .idle
  | _, .step previous => .step (homogeneousExecution Token choose previous)

def heterogeneousExecution {seed : Nat} {first : HeterogeneousFeedback.Frame seed} : {last : HeterogeneousFeedback.Frame seed} →
    (heterogeneous seed).Execution first last → HeterogeneousFeedback.Execution first last
  | _, .idle => .idle
  | _, .step previous => .step (heterogeneousExecution previous)

theorem homogeneousTransport (Token : Type u) (choose : List Token → Token) {first : HistoricalFeedback.Configuration Token} :
    {last : HistoricalFeedback.Configuration Token} → (execution : (homogeneous Token choose).Execution first last) →
    (ref : Address first.layout) → execution.embed () ref = (homogeneousExecution Token choose execution).embed ref
  | _, .idle, _ => rfl
  | _, .step previous, ref => congrArg Address.old (homogeneousTransport Token choose previous ref)

theorem heterogeneousTransport {seed : Nat} {first : HeterogeneousFeedback.Frame seed} :
    {last : HeterogeneousFeedback.Frame seed} → (execution : (heterogeneous seed).Execution first last) →
    (kind : TypedResources.Kind) → (ref : TypedResources.Ref first.2.context kind) →
    execution.embed kind ref = (heterogeneousExecution execution).embed kind ref
  | _, .idle, _, _ => rfl
  | _, .step (middle := middle) previous, kind, ref => by
      have ih := heterogeneousTransport previous kind ref
      rcases middle with ⟨state, history, context, support, focus⟩
      cases focus <;> exact congrArg TypedResources.Ref.old ih

theorem homogeneousContinuation (Token : Type u) (choose : List Token → Token) {first : HistoricalFeedback.Configuration Token} :
    {last : HistoricalFeedback.Configuration Token} → (execution : (homogeneous Token choose).Execution first last) →
    execution.continuation = (homogeneousExecution Token choose execution).continuation
  | _, .idle => rfl
  | _, .step previous => congrArg (fun h => History.extend h _) (homogeneousContinuation Token choose previous)

theorem heterogeneousContinuation {seed : Nat} {first : HeterogeneousFeedback.Frame seed} :
    {last : HeterogeneousFeedback.Frame seed} → (execution : (heterogeneous seed).Execution first last) →
    execution.continuation = (heterogeneousExecution execution).continuation
  | _, .idle => rfl
  | _, .step (middle := middle) previous => by
      have ih := heterogeneousContinuation previous
      rcases middle with ⟨state, history, context, support, focus⟩
      cases focus <;> exact congrArg (fun h => History.extend h _) ih

def homogeneousRealization (Token : Type u) (choose : List Token → Token) {target : List Token}
    {history : History (HistoricalFeedback.Step Token) [] target}
    (actual : (homogeneous Token choose).Realization history) : FeedbackCoverage.Realization choose history :=
  ⟨actual.frame, homogeneousExecution Token choose actual.execution, actual.exact⟩

def homogeneousFrameRefs {Token : Type u} {one two : HistoricalFeedback.Configuration Token} (same : one = two) :
    ExactTransport (Address one.layout) (Address two.layout) :=
  ExactTransport.ofEquality (congrArg (fun frame => Address frame.layout) same)

theorem homogeneousFrameValues {Token : Type u} {one two : HistoricalFeedback.Configuration Token} (same : one = two)
    (ref : Address one.layout) : two.support.read ((homogeneousFrameRefs same).forward ref) = one.support.read ref := by
  cases same
  rfl

theorem homogeneousFrameDependencies {Token : Type u} {one two : HistoricalFeedback.Configuration Token} (same : one = two)
    (ref : Address one.layout) : two.support.dependencies ((homogeneousFrameRefs same).forward ref) =
      (one.support.dependencies ref).map (homogeneousFrameRefs same).forward := by
  cases same
  exact (list_id _).symm

/-- Retain the original independently declared demand and dependency API while
the actual frame and execution are supplied by the common constructor. -/
def homogeneousNativeComplete (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :
    FeedbackCoverage.CompleteRealization choose history :=
  let actual := homogeneousComplete Token choose history allowed
  let same := (homogeneousFrame Token choose history allowed).symm
  let frameRefs := homogeneousFrameRefs same
  let coordinates := (FeedbackCoverage.demandTransport choose history allowed).compose frameRefs
  { realization := homogeneousRealization Token choose actual.realization
    coordinates := coordinates
    certified := fun demand =>
      (homogeneousFrameValues same _).trans (FeedbackCoverage.fulfills choose history allowed demand)
    ruleCertified := actual.certified ()
    coveredDependencies := fun demand =>
      (homogeneousFrameDependencies same _).trans
        ((congrArg (List.map frameRefs.forward) (FeedbackCoverage.dependencies_covered choose history allowed demand)).trans
          (FeedbackCoverage.ListMaps.compose _ _ _))
    resources := actual.realization.frame.layout.addresses
    exhaustive := actual.realization.frame.layout.addresses_complete
    unique := actual.realization.frame.layout.addresses_nodup
    counted := actual.realization.frame.layout.addresses_length
    terminal := actual.terminal }

def heterogeneousRealization {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history)
    (actual : (heterogeneous seed).Realization history) : HeterogeneousFeedback.Realization history :=
  { frame := actual.frame
    execution := heterogeneousExecution actual.execution
    exact := ((heterogeneous seed).realization_frame actual ((heterogeneousAdmission seed history).mpr allowed)).trans
      ((heterogeneousFrame history allowed).trans (HeterogeneousFeedback.build history allowed).exact) }

/-- The legacy heterogeneous certificate API now accepts an actual witness
constructed by the common executor, including its whole historical support. -/
def heterogeneousNativeComplete {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :
    HeterogeneousFeedback.CompleteRealization history :=
  HeterogeneousFeedback.certify history allowed
    (heterogeneousRealization history allowed (heterogeneousComplete history allowed).realization)

theorem homogeneousOperators (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history)
    (ref : Address (homogeneousComplete Token choose history allowed).realization.frame.layout) :
    let transport := (homogeneous Token choose).frameCoordinates (homogeneousFrame Token choose history allowed) ()
    (FeedbackCoverage.complete choose history allowed).realization.frame.support.nodeAt (transport.forward ref) =
      ((homogeneousComplete Token choose history allowed).realization.frame.support.nodeAt ref).map transport.forward :=
  (homogeneous Token choose).frame_nodes (homogeneousFrame Token choose history allowed) () ref

theorem heterogeneousOperators {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (ref : TypedResources.Ref (heterogeneousComplete history allowed).realization.frame.2.context kind) :
    let transport := fun kind => ((heterogeneous seed).frameCoordinates (heterogeneousFrame history allowed) kind).forward
    (HeterogeneousFeedback.complete history allowed).realization.frame.2.support.nodeAt kind (transport kind ref) =
      ((heterogeneousComplete history allowed).realization.frame.2.support.nodeAt kind ref).map transport :=
  (heterogeneous seed).frame_nodes (heterogeneousFrame history allowed) kind ref

theorem homogeneousCount (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :
    (homogeneousComplete Token choose history allowed).resources.items.length = 1 + history.length * 3 := by
  have counts : (homogeneous Token choose).fragmentSize history = 1 + history.length * 3 := by
    induction history with
    | root => rfl
    | extend previous step ih =>
        have arithmetic : 1 + previous.length * 3 + 3 = 1 + (previous.length + 1) * 3 := by
          rw [Nat.succ_mul, Nat.add_assoc]
        exact (congrArg (fun n => n + 3) (ih allowed.1)).trans arithmetic
  exact ((homogeneous Token choose).resource_count history _).trans counts

theorem heterogeneousCount {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :
    (heterogeneousComplete history allowed).resources.items.length = 1 + history.length := by
  have counts : (heterogeneous seed).fragmentSize history = 1 + history.length := by
    induction history with
    | root => rfl
    | extend previous step ih =>
        have added : ((heterogeneous seed).newFinite step).items.length = 1 := by cases step <;> rfl
        exact (congrArg (fun n => n + ((heterogeneous seed).newFinite step).items.length) (ih allowed.1)).trans
          ((congrArg (fun n => (1 + previous.length) + n) added).trans (Nat.add_assoc 1 previous.length 1))
  exact ((heterogeneous seed).resource_count history _).trans counts

theorem heterogeneousResume {seed : Nat} {middle target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) middle) (allowed : HeterogeneousFeedback.Admissible history)
    (prior : (heterogeneous seed).Realization history) (following : History HeterogeneousFeedback.Step middle target)
    (followingAllowed : HeterogeneousFeedback.Admissible following) :
    ((heterogeneous seed).resumeFrom history ((heterogeneousAdmission seed history).mpr allowed) prior following
      ((heterogeneousAdmission seed following).mpr followingAllowed)).frame =
    (HeterogeneousFeedback.resumeFrom history allowed (heterogeneousRealization history allowed prior) following followingAllowed).frame :=
  heterogeneousRun seed prior.frame following.length

theorem homogeneousTerminal (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (allowed : FeedbackCoverage.Admissible choose history) :
    (homogeneousComplete Token choose history allowed).realization.frame.output = HistoricalFeedback.trajectory choose history.length :=
  (homogeneousComplete Token choose history allowed).terminal.trans (FeedbackCoverage.admitted_target choose history allowed)

theorem heterogeneousTerminal {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (allowed : HeterogeneousFeedback.Admissible history) :
    HeterogeneousFeedback.visible (heterogeneousComplete history allowed).realization.frame = HeterogeneousFeedback.trajectory seed history.length :=
  (heterogeneousComplete history allowed).terminal.trans (HeterogeneousFeedback.admitted_target history allowed)

end RelationalFoundations.FiniteRuleInstances
