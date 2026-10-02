import RelationalFoundations.ReducedHeterogeneous
set_option genInjectivity false

namespace RelationalFoundations.ReducedHeterogeneous
open TypedResources

/-- Actual native transports, materialized only when restitution is requested. -/
def restorationExecution (m : Memory) (count : Nat) :
    HeterogeneousFeedback.Execution (reconstruct m) (reconstruct (run m count)) :=
  (reconstruct_run m count).symm ▸ (HeterogeneousFeedback.run (reconstruct m) count).2

def transport (m : Memory) (count : Nat) :
    Extension (reconstruct m).2.support (reconstruct (run m count)).2.support :=
  (restorationExecution m count).resources

theorem old_identity (m : Memory) (count : Nat) (kind : Kind) :
    Function.Injective ((transport m count).embed kind) := (transport m count).embed_injective kind

theorem old_value (m : Memory) (count : Nat) (kind : Kind) (ref : Ref (reconstruct m).2.context kind) :
    (reconstruct (run m count)).2.support.read kind ((transport m count).embed kind ref) =
      (reconstruct m).2.support.read kind ref := (transport m count).read_preserved kind ref

theorem old_operator (m : Memory) (count : Nat) (kind : Kind) (ref : Ref (reconstruct m).2.context kind) :
    (reconstruct (run m count)).2.support.nodeAt kind ((transport m count).embed kind ref) =
      ((reconstruct m).2.support.nodeAt kind ref).map (transport m count).embed :=
  (transport m count).node_preserved kind ref

theorem old_ordered_inputs (m : Memory) (count : Nat) (ref : AnyRef (reconstruct m).2.context) :
    (reconstruct (run m count)).2.support.dependencies (AnyRef.map (transport m count).embed ref) =
      ((reconstruct m).2.support.dependencies ref).map (AnyRef.map (transport m count).embed) :=
  (transport m count).dependencies_preserved ref

theorem old_relation (m : Memory) (count : Nat) (parent child : AnyRef (reconstruct m).2.context) :
    (reconstruct (run m count)).2.support.Depends
        (AnyRef.map (transport m count).embed parent) (AnyRef.map (transport m count).embed child) ↔
      (reconstruct m).2.support.Depends parent child :=
  ⟨(transport m count).relation_reflected, (transport m count).relation_preserved⟩

theorem old_certificate (m : Memory) (count : Nat) (kind : Kind)
    (ref : Ref (HeterogeneousFeedback.declaredContext (reconstruct m).2.history) kind) :
    (reconstruct (run m count)).2.support.read kind
        ((transport m count).embed kind ((certificate m).coordinates kind |>.forward ref)) =
      HeterogeneousFeedback.expected (reconstruct m).2.history kind ref :=
  (old_value m count kind _).trans ((certificate m).certified kind ref)

theorem transports_compose (m : Memory) (one two : Nat) (kind : Kind)
    (ref : Ref (reconstruct m).2.context kind) :
    ((restorationExecution m one).compose (restorationExecution (run m one) two)).embed kind ref =
      (transport (run m one) two).embed kind ((transport m one).embed kind ref) :=
  HeterogeneousFeedback.Execution.embed_compose _ _ kind ref

theorem histories_compose (m : Memory) (one two : Nat) :
    ((restorationExecution m one).compose (restorationExecution (run m one) two)).continuation =
      History.append (restorationExecution m one).continuation (restorationExecution (run m one) two).continuation :=
  HeterogeneousFeedback.Execution.continuation_compose _ _

theorem reconstruction_compose (m : Memory) (one two : Nat) :
    reconstruct (run m (one + two)) = reconstruct (run (run m one) two) :=
  congrArg (fun n => (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) n).1)
    (Nat.add_assoc m.position one two).symm

theorem all_finite_continuations (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (reconstruct m).1 target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    reconstruct (run m following.length) =
      HeterogeneousFeedback.specified (History.append (reconstruct m).2.history following) :=
  (reconstruct_run m following.length).trans
    (HeterogeneousFeedback.resumeFrom (reconstruct m).2.history
      (HeterogeneousFeedback.execution_admitted (realization m).execution) (realization m) following allowed).exact

def continuationCertificate (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (reconstruct m).1 target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    HeterogeneousFeedback.CompleteRealization (History.append (reconstruct m).2.history following) :=
  HeterogeneousFeedback.certify _
    ((HeterogeneousFeedback.admissible_append _ following).mpr
      ⟨HeterogeneousFeedback.execution_admitted (realization m).execution, allowed⟩)
    ⟨reconstruct (run m following.length),
      (HeterogeneousFeedback.run (HeterogeneousFeedback.initial m.origin) (m.position + following.length)).2,
      all_finite_continuations m following allowed⟩

theorem continuation_terminal (m : Memory) (coherent : Coherent m) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (reconstruct m).1 target)
    (allowed : HeterogeneousFeedback.Admissible following) : view (run m following.length) = target :=
  (terminal _ (run_coherent m coherent following.length)).symm.trans
    (continuationCertificate m following allowed).terminal

/-- Independent terminal predicates are preserved, with the same shared history witness. -/
theorem extract (m : Memory) (coherent : Coherent m) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (reconstruct m).1 target)
    (allowed : HeterogeneousFeedback.Admissible following)
    (guarantee : HeterogeneousFeedback.State → Prop) (declared : guarantee target) :
    guarantee (view (run m following.length)) := (continuation_terminal m coherent following allowed).symm ▸ declared

theorem reconstruction_history_length (m : Memory) : (reconstruct m).2.history.length = m.position :=
  (HeterogeneousFeedback.run_history_length _ _).trans (Nat.zero_add _)

theorem number_state (stage : Phase) (n : Nat) : number (state stage n) = n := by
  cases stage <;> rfl

theorem reduce_reconstruct (m : Memory) (coherent : Coherent m) : reduce (reconstruct m) = m := by
  change Memory.mk m.origin (reconstruct m).2.history.length (number (HeterogeneousFeedback.visible (reconstruct m))) = m
  rw [reconstruction_history_length, terminal m coherent]
  change Memory.mk m.origin m.position (number (state _ m.active)) = m
  rw [number_state]

theorem reduce_step {seed : Nat} {last : HeterogeneousFeedback.Frame seed}
    (execution : HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) last) :
    reduce (HeterogeneousFeedback.advance last) = step (reduce last) := by
  change Memory.mk seed _ _ = Memory.mk seed _ _
  rw [HeterogeneousFeedback.advance_history_length,
    HeterogeneousFeedback.visible_valid _ (HeterogeneousFeedback.execution_valid (.step execution)),
    HeterogeneousFeedback.advance_state last (HeterogeneousFeedback.execution_valid execution)]
  exact congrArg (Memory.mk seed (last.2.history.length + 1))
    (congrArg number ((congrArg HeterogeneousFeedback.next (reduce_view execution).symm).trans
      (nextState_eq (reduce last)).symm))

theorem reduce_run (m : Memory) (coherent : Coherent m) (count : Nat) :
    reduce (HeterogeneousFeedback.run (reconstruct m) count).1 = run m count :=
  (congrArg reduce (reconstruct_run m count).symm).trans
    (reduce_reconstruct _ (run_coherent m coherent count))

/-- Occurrence identities are reconstructed, not obtained by identifying their values. -/
def occurrenceCoordinates (m : Memory) :
    ExactTransport (History.Occurrence (reconstruct m).2.history) (Fin m.position) :=
  (History.cardinalTransport _).compose
    (ExactTransport.ofEquality (congrArg Fin (reconstruction_history_length m)))

theorem occurrence_identity (m : Memory) : Function.Injective (occurrenceCoordinates m).forward := by
  intro one two same
  exact ((occurrenceCoordinates m).forwardBackward one).symm.trans
    ((congrArg (occurrenceCoordinates m).backward same).trans ((occurrenceCoordinates m).forwardBackward two))

/-- Pointwise locality for this concrete operator language, including ordered inputs. -/
theorem evaluation_local {context : List Kind} {kind : Kind} (operation : Operation context kind)
    (first second : ∀ kind, Ref context kind → Value kind)
    (agree : ∀ k ref, AnyRef.pack k ref ∈ operation.inputs → first k ref = second k ref) :
    operation.eval first = operation.eval second := by
  cases operation with
  | literal _ => rfl
  | test ref => exact congrArg TypedResources.test (agree .number ref (by exact List.Mem.head _))
  | adjust flag numeric =>
      exact (congrArg (fun b => TypedResources.adjust b (first .number numeric))
        (agree .truth flag (List.Mem.head _))).trans
          (congrArg (TypedResources.adjust (second .truth flag))
            (agree .number numeric (List.Mem.tail _ (List.Mem.head _))))
  | reuse ref => exact agree _ ref (List.Mem.head _)

/-- The current producer reads precisely the values represented by the native focus. -/
theorem producer_consultations (m : Memory) (coherent : Coherent m) :
    produced m = ⟨(HeterogeneousFeedback.reaction (reconstruct m)).kind,
      (HeterogeneousFeedback.reaction (reconstruct m)).value⟩ := by
  have same := event_exact m coherent
  have scalar : produced m = ⟨(event m).2.2.kind, (event m).2.2.value⟩ := by
    unfold produced event output
    cases stage : phaseAt m.position <;> rfl
  exact scalar.trans (congrArg (fun e : Event => (⟨e.2.2.kind, e.2.2.value⟩ : (k : Kind) × Value k)) same)

def alignHistory {first second target : HeterogeneousFeedback.State} (same : first = second)
    (following : History HeterogeneousFeedback.Step second target) :
    History HeterogeneousFeedback.Step first target := same.symm ▸ following

theorem aligned_length {first second target : HeterogeneousFeedback.State} (same : first = second)
    (following : History HeterogeneousFeedback.Step second target) :
    (alignHistory same following).length = following.length := by cases same; rfl

theorem aligned_admission {first second target : HeterogeneousFeedback.State} (same : first = second)
    (following : History HeterogeneousFeedback.Step second target) (allowed : HeterogeneousFeedback.Admissible following) :
    HeterogeneousFeedback.Admissible (alignHistory same following) := by cases same; exact allowed

/-- The execution entry point receives a history starting at the active view;
its executable body consults only the finite horizon and the reduced memory. -/
def continueFrom (m : Memory) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view m) target) : Memory := run m following.length

theorem active_continuation (m : Memory) (coherent : Coherent m) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view m) target) (allowed : HeterogeneousFeedback.Admissible following) :
    reconstruct (continueFrom m following) = HeterogeneousFeedback.specified
      (History.append (reconstruct m).2.history (alignHistory (reconstruct_state m coherent) following)) := by
  change reconstruct (run m following.length) = _
  rw [← aligned_length (reconstruct_state m coherent) following]
  exact all_finite_continuations m _ (aligned_admission _ following allowed)

theorem active_terminal (m : Memory) (coherent : Coherent m) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view m) target) (allowed : HeterogeneousFeedback.Admissible following) :
    view (continueFrom m following) = target :=
  (congrArg (fun count => view (run m count)) (aligned_length (reconstruct_state m coherent) following).symm).trans
    (continuation_terminal m coherent _ (aligned_admission _ following allowed))

/-- The acquired common constructor is covered as a whole-frame input too. -/
theorem common_constructor_round_trip {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target)
    (allowed : HeterogeneousFeedback.Admissible history) :
    reconstruct (reduce (FiniteRuleInstances.heterogeneousComplete history allowed).realization.frame) =
      (FiniteRuleInstances.heterogeneousComplete history allowed).realization.frame :=
  reconstruct_reduce (FiniteRuleInstances.heterogeneousExecution
    (FiniteRuleInstances.heterogeneousComplete history allowed).realization.execution)

end RelationalFoundations.ReducedHeterogeneous
