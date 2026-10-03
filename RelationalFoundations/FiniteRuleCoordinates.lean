import RelationalFoundations.FiniteRuleInstances
set_option genInjectivity false

/-! Coordinates identify resources of the actual constructors, including
certification of prior realizations and their admitted continuations. -/

namespace RelationalFoundations.FiniteRuleCoordinates
open FiniteRuleConstruction
universe u

theorem cast_cancel {A B : Sort u} (same : A = B) (value : B) : same ▸ same.symm ▸ value = value := by
  cases same
  rfl

theorem execution_heq {rules : Rules.{u}} {first oneLast twoLast : rules.Frame}
    (one : rules.Execution first oneLast) (two : rules.Execution first twoLast)
    (same : one.length = two.length) : HEq one two := by
  induction one generalizing twoLast with
  | idle =>
      cases two with
      | idle => rfl
      | step _ => exact Nat.noConfusion same
  | step previous ih =>
      cases two with
      | idle => exact Nat.noConfusion same
      | step other =>
          have frameSame : _ = _ := congrArg (fun execution => execution.1)
            (show (⟨_, previous⟩ : (last : rules.Frame) × rules.Execution first last) =
              ⟨_, other⟩ from by
                have equal := ih other (Nat.succ.inj same)
                have endSame := previous.frame_run.trans
                  ((congrArg (fun n => (rules.run first n).1) (Nat.succ.inj same)).trans other.frame_run.symm)
                cases endSame
                exact congrArg (Sigma.mk _) (eq_of_heq equal))
          cases frameSame
          have equal := eq_of_heq (ih other (Nat.succ.inj same))
          cases equal
          rfl

theorem realization_eq {rules : Rules.{u}} {target : rules.State}
    (history : History rules.Step rules.origin target) (admitted : rules.Admissible history)
    (prior : rules.Realization history) : prior = rules.build history admitted := by
  have sameFrame := rules.realization_frame prior admitted
  have length : prior.execution.length = (rules.build history admitted).execution.length := by
    have one := prior.execution.history_length
    have two := (rules.build history admitted).execution.history_length
    rw [prior.exact, rules.initial_recorded] at one
    rw [(rules.build history admitted).exact, rules.initial_recorded] at two
    exact (Nat.zero_add _).symm.trans (one.symm.trans (two.trans (Nat.zero_add _)))
  cases prior with
  | mk frame execution exact =>
      cases sameFrame
      have sameExecution := eq_of_heq (execution_heq execution (rules.build history admitted).execution length)
      cases sameExecution
      rfl

theorem grow_old {rules : Rules.{u}} (frame : rules.Frame) (valid : rules.valid frame)
    (record : (target : rules.State) × History rules.Step rules.origin target)
    (same : rules.recorded frame = record) {target : rules.State}
    (step : rules.Step record.1 target) (allowed : rules.allowed step)
    (prior : rules.Coverage (rules.recorded frame).2 frame) (kind : rules.Kind)
    (request : rules.Requests record.2 kind) :
    let priorCov := (congrArg (fun rec : (target : rules.State) × History rules.Step rules.origin target => rules.Coverage rec.2 frame) same) ▸ prior
    let nextCov := (congrArg (fun rec : (target : rules.State) × History rules.Step rules.origin target => rules.Coverage rec.2 (rules.advance frame))
      (rules.advance_exact frame valid record same step allowed)) ▸ rules.recordedCoverage frame valid prior
    (nextCov.coordinates kind).forward (.inl request) = rules.old frame kind ((priorCov.coordinates kind).forward request) := by
  cases same
  have reaction := rules.reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  let equality := congrArg (fun rec : (target : rules.State) × History rules.Step rules.origin target =>
    rules.Coverage rec.2 (rules.advance frame)) (rules.advance_recorded frame)
  change (((equality ▸ equality.symm ▸ rules.growCoverage frame valid prior).coordinates kind).forward
    (.inl request)) = _
  exact congrArg (fun cov : rules.Coverage
      (.extend (rules.recorded frame).2 (rules.reaction frame).2) (rules.advance frame) =>
      (cov.coordinates kind).forward (.inl request)) (cast_cancel equality (rules.growCoverage frame valid prior))

def freshAt {rules : Rules.{u}} (frame : rules.Frame) (valid : rules.valid frame)
    (record : (target : rules.State) × History rules.Step rules.origin target)
    (same : rules.recorded frame = record) {target : rules.State}
    (step : rules.Step record.1 target) (allowed : rules.allowed step) (kind : rules.Kind)
    (slot : rules.New step kind) : rules.Ref (rules.advance frame) kind := by
  cases same
  have reaction := rules.reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  exact (rules.split frame kind).forward (.inr slot)

theorem grow_new {rules : Rules.{u}} (frame : rules.Frame) (valid : rules.valid frame)
    (record : (target : rules.State) × History rules.Step rules.origin target)
    (same : rules.recorded frame = record) {target : rules.State}
    (step : rules.Step record.1 target) (allowed : rules.allowed step)
    (prior : rules.Coverage (rules.recorded frame).2 frame) (kind : rules.Kind)
    (slot : rules.New step kind) :
    let nextCov := (congrArg (fun rec : (target : rules.State) × History rules.Step rules.origin target =>
      rules.Coverage rec.2 (rules.advance frame))
      (rules.advance_exact frame valid record same step allowed)) ▸ rules.recordedCoverage frame valid prior
    (nextCov.coordinates kind).forward (.inr slot) = freshAt frame valid record same step allowed kind slot := by
  cases same
  have reaction := rules.reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  let equality := congrArg (fun rec : (target : rules.State) × History rules.Step rules.origin target =>
    rules.Coverage rec.2 (rules.advance frame)) (rules.advance_recorded frame)
  change (((equality ▸ equality.symm ▸ rules.growCoverage frame valid prior).coordinates kind).forward
    (.inr slot)) = _
  exact congrArg (fun cov : rules.Coverage
      (.extend (rules.recorded frame).2 (rules.reaction frame).2) (rules.advance frame) =>
      (cov.coordinates kind).forward (.inr slot)) (cast_cancel equality (rules.growCoverage frame valid prior))
theorem complete_old {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (step : rules.Step middle target)
    (admitted : rules.Admissible (.extend history step)) (kind : rules.Kind)
    (request : rules.Requests history kind) :
    ((rules.complete (.extend history step) admitted).coverage.coordinates kind).forward (.inl request) =
      rules.old (rules.complete history admitted.1).realization.frame kind
        (((rules.complete history admitted.1).coverage.coordinates kind).forward request) :=
  grow_old (rules.build history admitted.1).frame (rules.build history admitted.1).execution.valid
    ⟨middle, history⟩ (rules.build history admitted.1).exact step admitted.2
    (rules.build history admitted.1).execution.coverage kind request

theorem complete_new {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (step : rules.Step middle target)
    (admitted : rules.Admissible (.extend history step)) (kind : rules.Kind)
    (slot : rules.New step kind) :
    ((rules.complete (.extend history step) admitted).coverage.coordinates kind).forward (.inr slot) =
      freshAt (rules.build history admitted.1).frame (rules.build history admitted.1).execution.valid
        ⟨middle, history⟩ (rules.build history admitted.1).exact step admitted.2 kind slot :=
  grow_new (rules.build history admitted.1).frame (rules.build history admitted.1).execution.valid
    ⟨middle, history⟩ (rules.build history admitted.1).exact step admitted.2
    (rules.build history admitted.1).execution.coverage kind slot

open FiniteRuleInstances ResourceGraph

theorem homogeneous_cast_old {Token : Type u} (choose : List Token → Token)
    {one two : HistoricalFeedback.Configuration Token} (same : one = two) (ref : Address one.layout) :
    ((homogeneous Token choose).frameCoordinates (congrArg (HistoricalFeedback.rule choose).advance same) ()).forward (.old ref) =
      .old (((homogeneous Token choose).frameCoordinates same ()).forward ref) := by
  cases same
  rfl

theorem homogeneous_fresh {Token : Type u} (choose : List Token → Token)
    (frame : HistoricalFeedback.Configuration Token) (valid : (homogeneous Token choose).valid frame)
    (record : (target : List Token) × History (HistoricalFeedback.Step Token) [] target)
    (same : (homogeneous Token choose).recorded frame = record) {target : List Token}
    (step : HistoricalFeedback.Step Token record.1 target)
    (allowed : (homogeneous Token choose).allowed step) (slot : Position (.branch .leaf .leaf)) :
    freshAt (rules := homogeneous Token choose) frame valid record same step allowed () slot = (.fresh slot : Address ((HistoricalFeedback.rule choose).advance frame).layout) := by
  cases same
  have reaction := (homogeneous Token choose).reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  rfl

theorem homogeneous_cast_fresh {Token : Type u} (choose : List Token → Token)
    {one two : HistoricalFeedback.Configuration Token} (same : one = two) (slot : Position (.branch .leaf .leaf)) :
    ((homogeneous Token choose).frameCoordinates (congrArg (HistoricalFeedback.rule choose).advance same) ()).forward (.fresh slot) =
      (.fresh slot : Address ((HistoricalFeedback.rule choose).advance two).layout) := by
  cases same
  rfl

theorem homogeneous_coordinates (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous Token choose).Requests history ()) :
    ((homogeneous Token choose).frameCoordinates (homogeneousFrame Token choose history admitted) ()).forward
      (((homogeneousComplete Token choose history admitted).coverage.coordinates ()).forward request) =
      (FeedbackCoverage.complete choose history admitted).coordinates.forward
        ((homogeneousRequests Token choose history).forward request) := by
  induction history with
  | root => cases request; rfl
  | extend previous step ih =>
      let admittedCommon := (homogeneousAdmission Token choose (.extend previous step)).mpr admitted
      let transport := ((homogeneous Token choose).frameCoordinates
        (homogeneousFrame Token choose (.extend previous step) admitted) ()).forward
      cases request with
      | inl old =>
          have coordinate := complete_old (rules := homogeneous Token choose) previous step admittedCommon () old
          exact (congrArg transport coordinate).trans
            ((homogeneous_cast_old choose (homogeneousFrame Token choose previous admitted.1) _).trans
              ((congrArg Address.old (ih admitted.1 old)).trans
                (FeedbackCoverage.locate_lift choose previous step admitted
                  ((homogeneousRequests Token choose previous).forward old)).symm))
      | inr slot =>
          have coordinate := complete_new (rules := homogeneous Token choose) previous step admittedCommon () slot
          let prior := (homogeneous Token choose).build previous admittedCommon.1
          have located := coordinate.trans (homogeneous_fresh choose prior.frame prior.execution.valid
            ⟨_, previous⟩ prior.exact step admittedCommon.2 slot)
          exact (congrArg transport located).trans
            ((homogeneous_cast_fresh choose (homogeneousFrame Token choose previous admitted.1) slot).trans
              (congrArg Address.fresh (FeedbackCoverage.Role.position_of slot)).symm)
def refCast {one two : List TypedResources.Kind} (same : one = two) (kind : TypedResources.Kind)
    (ref : TypedResources.Ref one kind) : TypedResources.Ref two kind :=
  (ExactTransport.ofEquality (congrArg (fun context => TypedResources.Ref context kind) same)).forward ref

theorem refCast_trans {one two three : List TypedResources.Kind} (first : one = two) (second : two = three)
    (kind : TypedResources.Kind) (ref : TypedResources.Ref one kind) :
    refCast (first.trans second) kind ref = refCast second kind (refCast first kind ref) := by
  cases first
  cases second
  rfl

theorem refCast_old {one two : List TypedResources.Kind} (same : one = two) (head kind : TypedResources.Kind)
    (ref : TypedResources.Ref one kind) :
    refCast (congrArg (List.cons head) same) kind (.old ref) = .old (refCast same kind ref) := by
  cases same
  rfl

theorem refCast_head {one two : List TypedResources.Kind} (same : one = two) (head : TypedResources.Kind) :
    refCast (congrArg (List.cons head) same) head .head = .head := by
  cases same
  rfl

theorem heterogeneous_context {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history) :
    (heterogeneousComplete history admitted).realization.frame.2.context = HeterogeneousFeedback.declaredContext history :=
  congrArg (fun frame : HeterogeneousFeedback.Frame seed => frame.2.context)
    ((heterogeneousFrame history admitted).trans (HeterogeneousFeedback.build history admitted).exact)

theorem heterogeneous_next_context {seed : Nat} (frame : (heterogeneous seed).Frame) (valid : (heterogeneous seed).valid frame)
    (record : (target : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (.ready seed) target)
    (same : (heterogeneous seed).recorded frame = record) {target : HeterogeneousFeedback.State}
    (step : HeterogeneousFeedback.Step record.1 target) (allowed : HeterogeneousFeedback.LocalAdmission step) :
    (HeterogeneousFeedback.advance frame).2.context = step.kind :: frame.2.context := by
  cases same
  have reaction := (heterogeneous seed).reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> rfl

theorem heterogeneous_old {seed : Nat} (frame : (heterogeneous seed).Frame) (valid : (heterogeneous seed).valid frame)
    (record : (target : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (.ready seed) target)
    (same : (heterogeneous seed).recorded frame = record) {target : HeterogeneousFeedback.State}
    (step : HeterogeneousFeedback.Step record.1 target) (allowed : HeterogeneousFeedback.LocalAdmission step)
    (kind : TypedResources.Kind) (ref : TypedResources.Ref frame.2.context kind) :
    refCast (heterogeneous_next_context frame valid record same step allowed) kind
      ((heterogeneous seed).old frame kind ref) = .old ref := by
  cases same
  have reaction := (heterogeneous seed).reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> rfl

theorem heterogeneous_fresh {seed : Nat} (frame : (heterogeneous seed).Frame) (valid : (heterogeneous seed).valid frame)
    (record : (target : HeterogeneousFeedback.State) × History HeterogeneousFeedback.Step (.ready seed) target)
    (same : (heterogeneous seed).recorded frame = record) {target : HeterogeneousFeedback.State}
    (step : HeterogeneousFeedback.Step record.1 target) (allowed : HeterogeneousFeedback.LocalAdmission step)
    (kind : TypedResources.Kind) (slot : TypedResources.Ref [step.kind] kind) :
    refCast (heterogeneous_next_context frame valid record same step allowed) kind
      (freshAt (rules := heterogeneous seed) frame valid record same step allowed kind slot) =
      (typedSplit frame.2.context step.kind kind).forward (.inr slot) := by
  cases same
  have reaction := (heterogeneous seed).reaction_exact frame valid step allowed
  have targetSame := congrArg Sigma.fst reaction
  cases targetSame
  have stepSame := eq_of_heq (Sigma.mk.inj reaction).2
  cases stepSame
  rcases frame with ⟨state, history, context, support, focus⟩
  cases focus <;> rfl

theorem heterogeneous_coordinates_declared {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    refCast (heterogeneous_context history admitted) kind
      (((heterogeneousComplete history admitted).coverage.coordinates kind).forward request) =
      (heterogeneousRequests history kind).forward request := by
  induction history generalizing kind with
  | root => rfl
  | extend previous step ih =>
      let admittedCommon := (heterogeneousAdmission seed (.extend previous step)).mpr admitted
      let prior := (heterogeneous seed).build previous admittedCommon.1
      have nextContext := heterogeneous_next_context prior.frame prior.execution.valid
        ⟨_, previous⟩ prior.exact step admittedCommon.2
      let witness := step
      cases step
      all_goals
        cases request with
        | inl old =>
            have coordinate := complete_old (rules := heterogeneous seed) previous witness admittedCommon kind old
            have first := congrArg (refCast (heterogeneous_context _ admitted) kind) coordinate
            exact first.trans
              ((refCast_trans nextContext (congrArg (List.cons _) (heterogeneous_context previous admitted.1)) kind _).trans
                ((congrArg (refCast (congrArg (List.cons _) (heterogeneous_context previous admitted.1)) kind)
                  (heterogeneous_old prior.frame prior.execution.valid ⟨_, previous⟩ prior.exact witness admittedCommon.2 kind _)).trans
                  ((refCast_old (heterogeneous_context previous admitted.1) _ kind _).trans
                    (congrArg TypedResources.Ref.old (ih admitted.1 kind old)))))
        | inr slot =>
            have coordinate := complete_new (rules := heterogeneous seed) previous witness admittedCommon kind slot
            have first := congrArg (refCast (heterogeneous_context _ admitted) kind) coordinate
            exact first.trans
              ((refCast_trans nextContext (congrArg (List.cons _) (heterogeneous_context previous admitted.1)) kind _).trans
                ((congrArg (refCast (congrArg (List.cons _) (heterogeneous_context previous admitted.1)) kind)
                  (heterogeneous_fresh prior.frame prior.execution.valid ⟨_, previous⟩ prior.exact witness admittedCommon.2 kind slot)).trans
                  (by cases slot with | head => exact refCast_head (heterogeneous_context previous admitted.1) _ | old ref => cases ref)))

theorem frame_backward {rules : Rules.{u}} {one two : rules.Frame} (same : one = two)
    (kind : rules.Kind) (ref : rules.Ref two kind) :
    (rules.frameCoordinates same kind).backward ref = (rules.frameCoordinates same.symm kind).forward ref := by
  cases same
  rfl

theorem homogeneous_native_coordinates (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous Token choose).Requests history ()) :
    ((homogeneousComplete Token choose history admitted).coverage.coordinates ()).forward request =
      (homogeneousNativeComplete Token choose history admitted).coordinates.forward
        ((homogeneousRequests Token choose history).forward request) := by
  let transport := (homogeneous Token choose).frameCoordinates (homogeneousFrame Token choose history admitted) ()
  exact (transport.forwardBackward _).symm.trans
    ((congrArg transport.backward (homogeneous_coordinates Token choose history admitted request)).trans
      (frame_backward (homogeneousFrame Token choose history admitted) () _))

theorem refCast_back {one two : List TypedResources.Kind} (same : one = two) (kind : TypedResources.Kind)
    (ref : TypedResources.Ref one kind) : refCast same.symm kind (refCast same kind ref) = ref := by
  cases same
  rfl

theorem heterogeneous_native_coordinates {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    ((heterogeneousComplete history admitted).coverage.coordinates kind).forward request =
      ((heterogeneousNativeComplete history admitted).coordinates kind).forward
        ((heterogeneousRequests history kind).forward request) := by
  exact (refCast_back (heterogeneous_context history admitted) kind _).symm.trans
    (congrArg (refCast (heterogeneous_context history admitted).symm kind)
      (heterogeneous_coordinates_declared history admitted kind request))

theorem backward_agreement {A : Type u} {B : Type v} {C : Type w} (one : ExactTransport A C) (two : ExactTransport B C)
    (requests : ExactTransport A B) (same : ∀ request, one.forward request = two.forward (requests.forward request))
    (ref : C) : one.backward ref = requests.backward (two.backward ref) := by
  have aligned : requests.forward (one.backward ref) = two.backward ref :=
    (two.forwardBackward _).symm.trans
      ((congrArg two.backward (same (one.backward ref)).symm).trans (congrArg two.backward (one.backwardForward ref)))
  exact (requests.forwardBackward _).symm.trans (congrArg requests.backward aligned)

theorem native_frame_coordinates {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target)
    {one two : HeterogeneousFeedback.Frame seed} (same : one = two)
    (oneExact : one = HeterogeneousFeedback.specified history) (twoExact : two = HeterogeneousFeedback.specified history)
    (kind : TypedResources.Kind) (ref : TypedResources.Ref (HeterogeneousFeedback.declaredContext history) kind) :
    ((heterogeneous seed).frameCoordinates same kind).forward
      ((HeterogeneousFeedback.coordinates history one oneExact kind).forward ref) =
      (HeterogeneousFeedback.coordinates history two twoExact kind).forward ref := by
  cases same
  rfl

theorem heterogeneous_coordinates {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    ((heterogeneous seed).frameCoordinates (heterogeneousFrame history admitted) kind).forward
      (((heterogeneousComplete history admitted).coverage.coordinates kind).forward request) =
      ((HeterogeneousFeedback.complete history admitted).coordinates kind).forward
        ((heterogeneousRequests history kind).forward request) :=
  (congrArg ((heterogeneous seed).frameCoordinates (heterogeneousFrame history admitted) kind).forward
    (heterogeneous_native_coordinates history admitted kind request)).trans
    (native_frame_coordinates history (heterogeneousFrame history admitted)
      (heterogeneousNativeComplete history admitted).realization.exact
      (HeterogeneousFeedback.complete history admitted).realization.exact kind _)

def liftRequests {rules : Rules.{u}} {middle : rules.State} (history : History rules.Step rules.origin middle) :
    {target : rules.State} → (following : History rules.Step middle target) →
      (kind : rules.Kind) → rules.Requests history kind → rules.Requests (History.append history following) kind
  | _, .root, _, request => request
  | _, .extend previous _, kind, request => .inl (liftRequests history previous kind request)
termination_by structural _ following _ _ => following

def extendExecution {rules : Rules.{u}} {middle : rules.State} (history : History rules.Step rules.origin middle)
    (admitted : rules.Admissible history) : {target : rules.State} →
    (following : History rules.Step middle target) → (allowed : rules.Admissible following) →
    rules.Execution (rules.build history admitted).frame
      (rules.build (History.append history following) ((rules.admissible_append history following).mpr ⟨admitted, allowed⟩)).frame
  | _, .root, _ => .idle
  | _, .extend previous _, allowed => .step (extendExecution history admitted previous allowed.1)
termination_by structural _ following _ => following

theorem extendExecution_length {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following) :
    (extendExecution history admitted following allowed).length = following.length := by
  induction following with
  | root => rfl
  | extend previous step ih => exact congrArg Nat.succ (ih allowed.1)

theorem extended_coordinates {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (following : History rules.Step middle target) (allowed : rules.Admissible following)
    (kind : rules.Kind) (request : rules.Requests history kind) :
    ((rules.complete (History.append history following)
        ((rules.admissible_append history following).mpr ⟨admitted, allowed⟩)).coverage.coordinates kind).forward
      (liftRequests history following kind request) =
      (extendExecution history admitted following allowed).embed kind
        (((rules.complete history admitted).coverage.coordinates kind).forward request) := by
  induction following with
  | root => rfl
  | extend previous step ih =>
      exact (complete_old (History.append history previous) step
        ((rules.admissible_append history (.extend previous step)).mpr ⟨admitted, allowed⟩)
        kind (liftRequests history previous kind request)).trans
        (congrArg (rules.old _ kind) (ih allowed.1))

theorem execution_embed_same {rules : Rules.{u}} {first a b : rules.Frame}
    (one : rules.Execution first a) (two : rules.Execution first b) (same : one.length = two.length)
    (kind : rules.Kind) (ref : rules.Ref first kind) :
    (rules.frameCoordinates (one.frame_run.trans
      ((congrArg (fun depth => (rules.run first depth).1) same).trans two.frame_run.symm)) kind).forward
      (one.embed kind ref) = two.embed kind ref := by
  have frameSame := one.frame_run.trans
    ((congrArg (fun depth => (rules.run first depth).1) same).trans two.frame_run.symm)
  cases frameSame
  have equality := eq_of_heq (execution_heq one two same)
  cases equality
  rfl

theorem run_length {rules : Rules.{u}} (frame : rules.Frame) (depth : Nat) :
    (rules.run frame depth).2.length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact congrArg Nat.succ ih

theorem certified_coordinates {rules : Rules.{u}} {target : rules.State}
    {history : History rules.Step rules.origin target} {one two : rules.Realization history}
    (same : one = two) (kind : rules.Kind) (request : rules.Requests history kind) :
    (rules.frameCoordinates (congrArg Rules.Realization.frame same) kind).forward
      (((rules.certify history one).coverage.coordinates kind).forward request) =
      ((rules.certify history two).coverage.coordinates kind).forward request := by
  cases same
  rfl

theorem resumed_coordinates {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (following : History rules.Step middle target)
    (allowed : rules.Admissible following) (kind : rules.Kind) (request : rules.Requests history kind) :
    ((rules.resumeCompleteFrom history admitted prior following allowed).coverage.coordinates kind).forward
      (liftRequests history following kind request) =
      (rules.resumeExecutionFrom history admitted prior following allowed).embed kind
        (((rules.certify history prior).coverage.coordinates kind).forward request) := by
  have oldSame := realization_eq history admitted prior
  cases oldSame
  have newSame := realization_eq (History.append history following)
    ((rules.admissible_append history following).mpr ⟨admitted, allowed⟩)
    (rules.resumeFrom history admitted (rules.build history admitted) following allowed)
  have comparison := execution_embed_same
    (rules.resumeExecutionFrom history admitted (rules.build history admitted) following allowed)
    (extendExecution history admitted following allowed)
    ((run_length _ _).trans (extendExecution_length history admitted following allowed).symm) kind
    (((rules.complete history admitted).coverage.coordinates kind).forward request)
  let transport := rules.frameCoordinates (congrArg Rules.Realization.frame newSame) kind
  have aligned := (certified_coordinates newSame kind (liftRequests history following kind request)).trans
    ((extended_coordinates history admitted following allowed kind request).trans comparison.symm)
  exact (transport.forwardBackward _).symm.trans
    ((congrArg transport.backward aligned).trans (transport.forwardBackward _))

theorem resumed_composed_coordinates {rules : Rules.{u}} {middle next target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (one : History rules.Step middle next) (allowedOne : rules.Admissible one)
    (two : History rules.Step next target) (allowedTwo : rules.Admissible two)
    (kind : rules.Kind) (request : rules.Requests history kind) :
    let extended := (rules.admissible_append history one).mpr ⟨admitted, allowedOne⟩
    let next := rules.resumeFrom history admitted prior one allowedOne
    let first := rules.resumeExecutionFrom history admitted prior one allowedOne
    let second := rules.resumeExecutionFrom (History.append history one) extended next two allowedTwo
    ((rules.resumeCompleteFrom (History.append history one) extended next two allowedTwo).coverage.coordinates kind).forward
      (liftRequests (History.append history one) two kind (liftRequests history one kind request)) =
    (first.compose second).embed kind (((rules.certify history prior).coverage.coordinates kind).forward request) :=
  (resumed_coordinates _ _ _ two allowedTwo kind _).trans
    ((congrArg ((rules.resumeExecutionFrom (History.append history one)
      ((rules.admissible_append history one).mpr ⟨admitted, allowedOne⟩)
        (rules.resumeFrom history admitted prior one allowedOne) two allowedTwo).embed kind)
          (resumed_coordinates history admitted prior one allowedOne kind request)).trans
      ((rules.resumeExecutionFrom history admitted prior one allowedOne).embed_compose _ kind _).symm)

theorem liftRequests_append {rules : Rules.{u}} {middle next target : rules.State}
    (history : History rules.Step rules.origin middle) (one : History rules.Step middle next)
    (two : History rules.Step next target) (kind : rules.Kind) (request : rules.Requests history kind) :
    (ExactTransport.ofEquality (congrArg (fun h => rules.Requests h kind)
      (History.append_associative history one two))).forward
      (liftRequests (History.append history one) two kind (liftRequests history one kind request)) =
      liftRequests history (History.append one two) kind request := by
  induction two with
  | root => rfl
  | extend previous step ih =>
      have castLeft {a b : History rules.Step rules.origin _} (same : a = b)
          (old : rules.Requests a kind) :
          (ExactTransport.ofEquality
            (congrArg (fun h => rules.Requests h kind) (congrArg (fun h => History.extend h step) same))).forward
            (Sum.inl old : rules.Requests (.extend a step) kind) =
              (Sum.inl ((ExactTransport.ofEquality (congrArg (fun h => rules.Requests h kind) same)).forward old) :
                rules.Requests (.extend b step) kind) := by
        cases same
        rfl
      exact (castLeft (History.append_associative history one previous) _).trans (congrArg Sum.inl ih)

theorem compose_length {rules : Rules.{u}} {a b c : rules.Frame}
    (one : rules.Execution a b) (two : rules.Execution b c) :
    (one.compose two).length = one.length + two.length := by
  induction two with
  | idle => rfl
  | step previous ih => exact congrArg Nat.succ ih

theorem composed_coordinates {rules : Rules.{u}} {middle next target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (one : History rules.Step middle next) (allowedOne : rules.Admissible one)
    (two : History rules.Step next target) (allowedTwo : rules.Admissible two)
    (kind : rules.Kind) (request : rules.Requests history kind) :
    ((rules.complete (History.append (History.append history one) two)
      ((rules.admissible_append _ two).mpr
        ⟨(rules.admissible_append history one).mpr ⟨admitted, allowedOne⟩, allowedTwo⟩)).coverage.coordinates kind).forward
        (liftRequests (History.append history one) two kind (liftRequests history one kind request)) =
    ((extendExecution history admitted one allowedOne).compose
      (extendExecution (History.append history one)
        ((rules.admissible_append history one).mpr ⟨admitted, allowedOne⟩) two allowedTwo)).embed kind
          (((rules.complete history admitted).coverage.coordinates kind).forward request) :=
  (extended_coordinates _ _ two allowedTwo kind _).trans
    ((congrArg ((extendExecution (History.append history one)
      ((rules.admissible_append history one).mpr ⟨admitted, allowedOne⟩) two allowedTwo).embed kind)
        (extended_coordinates history admitted one allowedOne kind request)).trans
      ((extendExecution history admitted one allowedOne).embed_compose _ kind _).symm)

theorem homogeneous_inverse (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (ref : (homogeneous Token choose).Ref (homogeneousComplete Token choose history admitted).realization.frame ()) :
    ((homogeneousComplete Token choose history admitted).coverage.coordinates ()).backward ref =
      (homogeneousRequests Token choose history).backward
        ((homogeneousNativeComplete Token choose history admitted).coordinates.backward ref) :=
  backward_agreement _ _ _ (homogeneous_native_coordinates Token choose history admitted) ref

theorem heterogeneous_inverse {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind)
    (ref : (heterogeneous seed).Ref (heterogeneousComplete history admitted).realization.frame kind) :
    ((heterogeneousComplete history admitted).coverage.coordinates kind).backward ref =
      (heterogeneousRequests history kind).backward
        (((heterogeneousNativeComplete history admitted).coordinates kind).backward ref) :=
  backward_agreement _ _ _ (heterogeneous_native_coordinates history admitted kind) ref

theorem homogeneous_operators (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous Token choose).Requests history ()) :
    (homogeneousComplete Token choose history admitted).realization.frame.support.nodeAt
        (((homogeneousComplete Token choose history admitted).coverage.coordinates ()).forward request) =
    (homogeneousNativeComplete Token choose history admitted).realization.frame.support.nodeAt
        ((homogeneousNativeComplete Token choose history admitted).coordinates.forward
          ((homogeneousRequests Token choose history).forward request)) :=
  congrArg _ (homogeneous_native_coordinates Token choose history admitted request)

theorem homogeneous_dependencies (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous Token choose).Requests history ()) :
    (homogeneousComplete Token choose history admitted).realization.frame.support.dependencies
      (((homogeneousComplete Token choose history admitted).coverage.coordinates ()).forward request) =
    (FeedbackCoverage.declaredDependencies ((homogeneousRequests Token choose history).forward request)).map
      (homogeneousNativeComplete Token choose history admitted).coordinates.forward :=
  (congrArg _ (homogeneous_native_coordinates Token choose history admitted request)).trans
    ((homogeneousNativeComplete Token choose history admitted).coveredDependencies _)

theorem heterogeneous_operators {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    (heterogeneousComplete history admitted).realization.frame.2.support.nodeAt kind
        (((heterogeneousComplete history admitted).coverage.coordinates kind).forward request) =
    (heterogeneousNativeComplete history admitted).realization.frame.2.support.nodeAt kind
        (((heterogeneousNativeComplete history admitted).coordinates kind).forward
          ((heterogeneousRequests history kind).forward request)) :=
  congrArg _ (heterogeneous_native_coordinates history admitted kind request)

theorem heterogeneous_dependencies {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    ((heterogeneousComplete history admitted).realization.frame.2.support.nodeAt kind
      (((heterogeneousComplete history admitted).coverage.coordinates kind).forward request)).inputs =
    (HeterogeneousFeedback.declaredDependencies history kind ((heterogeneousRequests history kind).forward request)).map
      (TypedResources.AnyRef.map (fun kind => ((heterogeneousNativeComplete history admitted).coordinates kind).forward)) :=
  (congrArg (fun ref => ((heterogeneousComplete history admitted).realization.frame.2.support.nodeAt kind ref).inputs)
    (heterogeneous_native_coordinates history admitted kind request)).trans
    ((heterogeneousNativeComplete history admitted).coveredDependencies kind _)

theorem resumed_operators {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (following : History rules.Step middle target)
    (allowed : rules.Admissible following) (kind : rules.Kind) (request : rules.Requests history kind) :
    rules.node (rules.resumeFrom history admitted prior following allowed).frame kind
      (((rules.resumeCompleteFrom history admitted prior following allowed).coverage.coordinates kind).forward
        (liftRequests history following kind request)) =
    rules.map (rules.resumeExecutionFrom history admitted prior following allowed).embed
      (rules.node prior.frame kind (((rules.certify history prior).coverage.coordinates kind).forward request)) :=
  (congrArg (rules.node _ kind) (resumed_coordinates history admitted prior following allowed kind request)).trans
    ((rules.resumeExecutionFrom history admitted prior following allowed).nodes_preserved kind _)

theorem resumed_dependencies {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (following : History rules.Step middle target)
    (allowed : rules.Admissible following) (kind : rules.Kind) (request : rules.Requests history kind) :
    rules.inputs (rules.node (rules.resumeFrom history admitted prior following allowed).frame kind
      (((rules.resumeCompleteFrom history admitted prior following allowed).coverage.coordinates kind).forward
        (liftRequests history following kind request))) =
    (rules.inputs (rules.node prior.frame kind (((rules.certify history prior).coverage.coordinates kind).forward request))).map
      (rename (rules.resumeExecutionFrom history admitted prior following allowed).embed) :=
  (congrArg rules.inputs (resumed_operators history admitted prior following allowed kind request)).trans
    (rules.inputs_map _ _)

theorem homogeneous_resumed_coordinates (Token : Type u) (choose : List Token → Token) {middle target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] middle) (admitted : FeedbackCoverage.Admissible choose history)
    (prior : (homogeneous Token choose).Realization history)
    (following : History (HistoricalFeedback.Step Token) middle target) (allowed : FeedbackCoverage.Admissible choose following)
    (request : (homogeneous Token choose).Requests history ()) :
    let oldAllowed := (homogeneousAdmission Token choose history).mpr admitted
    let nextAllowed := (homogeneousAdmission Token choose following).mpr allowed
    let execution := (homogeneous Token choose).resumeExecutionFrom history oldAllowed prior following nextAllowed
    (((homogeneous Token choose).resumeCompleteFrom history oldAllowed prior following nextAllowed).coverage.coordinates ()).forward
      (liftRequests (rules := homogeneous Token choose) history following () request) =
    (homogeneousExecution Token choose execution).embed
      ((((homogeneous Token choose).certify history prior).coverage.coordinates ()).forward request) :=
  (resumed_coordinates (rules := homogeneous Token choose) _ _ _ _ _ () request).trans
    (homogeneousTransport Token choose _ _)

theorem heterogeneous_resumed_coordinates {seed : Nat} {middle target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) middle) (admitted : HeterogeneousFeedback.Admissible history)
    (prior : (heterogeneous seed).Realization history)
    (following : History HeterogeneousFeedback.Step middle target) (allowed : HeterogeneousFeedback.Admissible following)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :
    let oldAllowed := (heterogeneousAdmission seed history).mpr admitted
    let nextAllowed := (heterogeneousAdmission seed following).mpr allowed
    let execution := (heterogeneous seed).resumeExecutionFrom history oldAllowed prior following nextAllowed
    (((heterogeneous seed).resumeCompleteFrom history oldAllowed prior following nextAllowed).coverage.coordinates kind).forward
      (liftRequests (rules := heterogeneous seed) history following kind request) =
    (heterogeneousExecution execution).embed kind
      ((((heterogeneous seed).certify history prior).coverage.coordinates kind).forward request) :=
  (resumed_coordinates (rules := heterogeneous seed) _ _ _ _ _ kind request).trans
    (heterogeneousTransport _ kind _)

end RelationalFoundations.FiniteRuleCoordinates

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.FiniteRuleCoordinates.cast_cancel
#print axioms RelationalFoundations.FiniteRuleCoordinates.execution_heq
#print axioms RelationalFoundations.FiniteRuleCoordinates.realization_eq
#print axioms RelationalFoundations.FiniteRuleCoordinates.grow_old
#print axioms RelationalFoundations.FiniteRuleCoordinates.freshAt
#print axioms RelationalFoundations.FiniteRuleCoordinates.grow_new
#print axioms RelationalFoundations.FiniteRuleCoordinates.complete_old
#print axioms RelationalFoundations.FiniteRuleCoordinates.complete_new
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_cast_old
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_fresh
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_cast_fresh
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.refCast
#print axioms RelationalFoundations.FiniteRuleCoordinates.refCast_trans
#print axioms RelationalFoundations.FiniteRuleCoordinates.refCast_old
#print axioms RelationalFoundations.FiniteRuleCoordinates.refCast_head
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_context
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_next_context
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_old
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_fresh
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_coordinates_declared
#print axioms RelationalFoundations.FiniteRuleCoordinates.frame_backward
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_native_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.refCast_back
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_native_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.backward_agreement
#print axioms RelationalFoundations.FiniteRuleCoordinates.native_frame_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.liftRequests
#print axioms RelationalFoundations.FiniteRuleCoordinates.extendExecution
#print axioms RelationalFoundations.FiniteRuleCoordinates.extendExecution_length
#print axioms RelationalFoundations.FiniteRuleCoordinates.extended_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.execution_embed_same
#print axioms RelationalFoundations.FiniteRuleCoordinates.run_length
#print axioms RelationalFoundations.FiniteRuleCoordinates.certified_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.resumed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.resumed_composed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.liftRequests_append
#print axioms RelationalFoundations.FiniteRuleCoordinates.compose_length
#print axioms RelationalFoundations.FiniteRuleCoordinates.composed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_inverse
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_inverse
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_operators
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_dependencies
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_operators
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_dependencies
#print axioms RelationalFoundations.FiniteRuleCoordinates.resumed_operators
#print axioms RelationalFoundations.FiniteRuleCoordinates.resumed_dependencies
#print axioms RelationalFoundations.FiniteRuleCoordinates.homogeneous_resumed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinates.heterogeneous_resumed_coordinates
/- AXIOM_AUDIT_END -/
