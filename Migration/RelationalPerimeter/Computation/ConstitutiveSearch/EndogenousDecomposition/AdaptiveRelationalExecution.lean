import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableRelationalExecution

/-!
# Continuation-dependent successors of actual local production

The successor is obtained by splitting the stored full continuation produced
by the local action. Its assignment and decision are therefore read from that
output, not from the opening's reference child. Both child formations use the
same generated source and fresh selected variable. The free constitutive step
and the operational child remain separate fields of the resulting state.

Adaptive paths carry constituted occurrences; their tails are indexed by the
corresponding produced successor. This is a separate construction from a
product over a fixed history. No product width formula is asserted for it.
SAT acceptance is separate from the formation and interpretation of a path.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive
open SAT StrongPerimetralTurning RelationalExtensive Extensive

def restoreChild {source : CausalConstitutiveState} (opening : Opening source) :
    (value : Bool) → GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected value opening.fresh) →
      GeneratedStructuralBranchContinuation source.operationalState
  | false, payload =>
      (generatedStructuralSplit source.operationalState opening.selected opening.fresh).merge (.inl payload)
  | true, payload =>
      (generatedStructuralSplit source.operationalState opening.selected opening.fresh).merge (.inr payload)

theorem restoreChild_assignment {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) (payload : GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected value opening.fresh)) :
    (restoreChild opening value payload).val = payload.val := by cases value <;> rfl

theorem restoreChild_preserves {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) (payload : GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected value opening.fresh))
    (accepted : GeneratedStructuralBranchAccept
      (source.operationalState.child opening.selected value opening.fresh) payload) :
    GeneratedStructuralBranchAccept source.operationalState (restoreChild opening value payload) := by
  cases value with
  | false => exact (generatedStructuralSplit _ _ _).mergePreservesAccept (.inl payload) accepted
  | true => exact (generatedStructuralSplit _ _ _).mergePreservesAccept (.inr payload) accepted

theorem restoreChild_reflects {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) (payload : GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected value opening.fresh))
    (accepted : GeneratedStructuralBranchAccept source.operationalState (restoreChild opening value payload)) :
    GeneratedStructuralBranchAccept
      (source.operationalState.child opening.selected value opening.fresh) payload := by
  let split := generatedStructuralSplit source.operationalState opening.selected opening.fresh
  have recovered := split.splitPreservesAccept _ accepted
  cases value with
  | false =>
      change BinaryAccept _ (split.split (split.merge (.inl payload))) at recovered
      rw [split.splitMerge] at recovered
      exact recovered
  | true =>
      change BinaryAccept _ (split.split (split.merge (.inr payload))) at recovered
      rw [split.splitMerge] at recovered
      exact recovered

def advanceState {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) (payload : GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected value opening.fresh)) : CausalConstitutiveState :=
  { constitutedHistory := appendGenerated source.constitutedHistory
      (generate source.constitutedHistory.endpoint)
    rootFormula := source.rootFormula
    operationalState := source.operationalState.child opening.selected value opening.fresh
    assignment := payload.val
    searchSeed := opening.selected
    decisions := {var := opening.selected, value := value} :: source.decisions
    provenance := opening.selected :: source.provenance
    provenanceExact := congrArg (List.cons opening.selected) source.provenanceExact }

structure ProducedSuccessor {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening) where
  private mk ::
  value : Bool
  continuation : GeneratedStructuralBranchContinuation
    (source.operationalState.child opening.selected value opening.fresh)
  restoredExact : restoreChild opening value continuation = head.output formed

def ProducedSuccessor.state {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) : CausalConstitutiveState :=
  advanceState opening successor.value successor.continuation

def ProducedSuccessor.arrival {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) :
    GeneratedStructuralBranchContinuation successor.state.operationalState := successor.continuation

def ProducedSuccessor.restore {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed)
    (payload : GeneratedStructuralBranchContinuation successor.state.operationalState) :
    GeneratedStructuralBranchContinuation source.operationalState :=
  restoreChild opening successor.value payload

theorem ProducedSuccessor.assignment_exact {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) :
    successor.state.assignment = (head.output formed).val :=
  (restoreChild_assignment opening successor.value successor.continuation).symm.trans
    (congrArg Subtype.val successor.restoredExact)

def ProducedSuccessor.generation {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) :
    GeneratedStep source.constitutedHistory.endpoint successor.state.constitutedHistory.endpoint :=
  (generate source.constitutedHistory.endpoint).2

def ProducedSuccessor.formation {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) :
    GeneratedChildFormation source.operationalState opening.selected successor.value opening.fresh
      successor.state.operationalState := .formed

theorem ProducedSuccessor.restore_preserves {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed)
    (payload : GeneratedStructuralBranchContinuation successor.state.operationalState)
    (accepted : GeneratedStructuralBranchAccept successor.state.operationalState payload) :
    GeneratedStructuralBranchAccept source.operationalState (successor.restore payload) :=
  restoreChild_preserves opening successor.value payload accepted

def produceSuccessor {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening) : ProducedSuccessor head formed :=
  let split := generatedStructuralSplit source.operationalState opening.selected opening.fresh
  match equation : split.split (head.output formed) with
  | .inl payload => ⟨false, payload, by
      have exactOutput := split.mergeSplit (head.output formed)
      rw [equation] at exactOutput
      exact exactOutput⟩
  | .inr payload => ⟨true, payload, by
      have exactOutput := split.mergeSplit (head.output formed)
      rw [equation] at exactOutput
      exact exactOutput⟩

theorem produced_successor_action {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening) :
    (produceSuccessor head formed).restore (produceSuccessor head formed).arrival = produced formed :=
  (produceSuccessor head formed).restoredExact.trans (head.output_exact formed)

theorem ProducedSuccessor.arrival_accepted_from_action
    {source : CausalConstitutiveState} {opening : Opening source}
    {head : LocalProduction opening} {formed : Identity opening}
    (successor : ProducedSuccessor head formed) (accepted : Accept formed (canonical formed)) :
    GeneratedStructuralBranchAccept successor.state.operationalState successor.arrival := by
  have outputAccepted := action_preserves formed (canonical formed) accepted
  change GeneratedStructuralBranchAccept source.operationalState (produced formed) at outputAccepted
  rw [← head.output_exact formed, ← successor.restoredExact] at outputAccepted
  exact restoreChild_reflects opening successor.value successor.continuation outputAccepted

theorem flip_fresh_decisions (selected : Var) (decisions : List StructuralBranchDecision)
    (assignment : Assignment) (fresh : StructuralDecisionsAvoid selected decisions)
    (holds : StructuralDecisionsHold assignment decisions) :
    StructuralDecisionsHold (Assignment.flipAt selected assignment) decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons head rest ih =>
      exact ⟨(Assignment.flipAt_other selected head.var assignment fresh.1).trans holds.1,
        ih fresh.2 holds.2⟩

def childInput {source : CausalConstitutiveState}
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (selected : Var) (fresh : StructuralDecisionsAvoid selected source.operationalState.context.decisions)
    (value : Bool) : GeneratedStructuralBranchContinuation
      (source.operationalState.child selected value fresh) :=
  if same : arrival.val selected = value then ⟨arrival.val, same, arrival.property⟩
  else ⟨Assignment.flipAt selected arrival.val, by
    have flipped : (!(arrival.val selected)) = value := by
      cases equation : arrival.val selected <;> cases value
      · exact False.elim (same equation)
      · rfl
      · rfl
      · exact False.elim (same equation)
    exact ⟨(Assignment.flipAt_selected selected arrival.val).trans flipped,
      flip_fresh_decisions selected _ arrival.val fresh arrival.property⟩⟩

/-- Candidates are extracted from this received residual syntax. Successful
freshness checking constructs the witness required to form both children. -/
def chooseFromCandidates (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (candidates : List Var) : Option (Opening source) :=
  List.foldr
    (fun selected next (_ : Unit) =>
      if check : structuralDecisionsAvoidCheck selected source.operationalState.context.decisions = true then
        let fresh := structuralDecisionsAvoid_of_check_true selected _ check
        some ⟨selected, fresh, childInput arrival selected fresh⟩
      else next ()) (fun _ => none) candidates ()

def chooseOpening (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState) : Option (Opening source) :=
  chooseFromCandidates source arrival (runCandidateExtraction source.operationalState).candidates

/-- A node owns its local production before any dependent continuation.
There is no supplied obligation policy or final partition. -/
inductive Execution : CausalConstitutiveState → Type 1 where
  | finish {source : CausalConstitutiveState}
      (arrival : GeneratedStructuralBranchContinuation source.operationalState)
      (assignmentExact : source.assignment = arrival.val) : Execution source
  | step {source : CausalConstitutiveState} (opening : Opening source)
      (head : LocalProduction opening)
      (tail : (formed : Identity opening) → Execution (produceSuccessor head formed).state) :
      Execution source

/-- One fuel recursion owns opening selection, local output production and
successor formation. The child executor receives the actual produced arrival.
Fuel is a stopping bound, not a supplied list of partitions or role statuses. -/
def execute : (fuel : Nat) → (source : CausalConstitutiveState) →
    (arrival : GeneratedStructuralBranchContinuation source.operationalState) →
    source.assignment = arrival.val → Execution source
  | 0, _, arrival, same => .finish arrival same
  | fuel + 1, source, arrival, same =>
      match chooseOpening source arrival with
      | none => .finish arrival same
      | some opening =>
          let head := executeOpening opening
          .step opening head (fun formed =>
            let successor := produceSuccessor head formed
            execute fuel successor.state successor.arrival rfl)

def Profile : {source : CausalConstitutiveState} → Execution source → Type
  | _, .finish _ _ => Unit
  | _, .step _ _ tail => (formed : _) × Profile (tail formed)

def profileEquality : {source : CausalConstitutiveState} → (execution : Execution source) →
    DecidableEq (Profile execution)
  | _, .finish _ _ => by change DecidableEq Unit; infer_instance
  | _, .step opening _ tail => by
      change DecidableEq ((formed : Identity opening) × Profile (tail formed))
      letI : DecidableEq (Identity opening) := (sourceCarrier opening).decEq
      letI : (formed : Identity opening) → DecidableEq (Profile (tail formed)) :=
        fun formed => profileEquality (tail formed)
      infer_instance

/-- Enumerate tails at their actual produced sources. The two heads are the
canonical witnessed occurrences of this opening, not unstructured bit labels. -/
def frontier : {source : CausalConstitutiveState} → (execution : Execution source) → List (Profile execution)
  | _, .finish _ _ => [()]
  | _, .step opening _ tail =>
      (frontier (tail (identity opening false))).map (Sigma.mk (identity opening false)) ++
      (frontier (tail (identity opening true))).map (Sigma.mk (identity opening true))

theorem fixed_head_injective {Head : Type} {Tail : Head → Type} (head : Head) :
    Function.Injective (Sigma.mk head : Tail head → Sigma Tail) := by
  intro left right same
  cases same
  rfl

theorem frontier_complete : {source : CausalConstitutiveState} → (execution : Execution source) →
    (profile : Profile execution) → profile ∈ frontier execution
  | _, .finish _ _, profile => by cases profile; exact .head _
  | _, .step opening _ tail, profile => by
      rcases profile with ⟨formed, rest⟩
      cases value : formed.position with
      | false =>
          have same : identity opening false = formed := by
            rw [← value]
            exact relationallyConstitutedOccurrence_roundTrip formed
          cases same
          apply List.mem_append_left
          exact mem_map _ (frontier_complete _ rest)
      | true =>
          have same : identity opening true = formed := by
            rw [← value]
            exact relationallyConstitutedOccurrence_roundTrip formed
          cases same
          apply List.mem_append_right
          exact mem_map _ (frontier_complete _ rest)

theorem frontier_nodup : {source : CausalConstitutiveState} → (execution : Execution source) →
    (frontier execution).Nodup
  | _, .finish _ _ => .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, .step opening _ tail => by
      apply relational_nodup_append
        (nodup_map _ (fixed_head_injective _) (frontier_nodup (tail (identity opening false))))
        (nodup_map _ (fixed_head_injective _) (frontier_nodup (tail (identity opening true))))
      intro left leftMember right rightMember same
      rcases mem_map_preimage _ leftMember with ⟨_, _, exactLeft⟩
      rcases mem_map_preimage _ rightMember with ⟨_, _, exactRight⟩
      exact source_distinct opening (congrArg Sigma.fst (exactLeft.trans (same.trans exactRight.symm)))

def profileCarrier {source : CausalConstitutiveState} (execution : Execution source) : FiniteCarrier :=
  { Identity := Profile execution
    decEq := profileEquality execution
    frontier := frontier execution
    complete := frontier_complete execution
    nodup := frontier_nodup execution }

def firstProfile : {source : CausalConstitutiveState} → (execution : Execution source) → Profile execution
  | _, .finish _ _ => ()
  | _, .step opening _ tail =>
      ⟨identity opening false, firstProfile (tail (identity opening false))⟩

/-- This sum is read from the actual dependent tails, not from a fixed depth. -/
theorem frontier_length_step {source : CausalConstitutiveState} (opening : Opening source)
    (head : LocalProduction opening)
    (tail : (formed : Identity opening) → Execution (produceSuccessor head formed).state) :
    (frontier (.step opening head tail)).length =
      (frontier (tail (identity opening false))).length +
        (frontier (tail (identity opening true))).length := by
  change (List.append
    ((frontier (tail (identity opening false))).map
      (fun rest => (⟨identity opening false, rest⟩ : Profile (.step opening head tail))))
    ((frontier (tail (identity opening true))).map
      (fun rest => (⟨identity opening true, rest⟩ : Profile (.step opening head tail))))).length = _
  exact (relational_length_append _ _).trans
    ((congrArg (fun count => count + _) (relational_length_map _ _)).trans
      (congrArg (Nat.add _) (relational_length_map _ _)))

def interpret : {source : CausalConstitutiveState} → (execution : Execution source) →
    Profile execution → GeneratedStructuralBranchContinuation source.operationalState
  | _, .finish arrival _, _ => arrival
  | _, .step _ head tail, profile =>
      (produceSuccessor head profile.1).restore (interpret (tail profile.1) profile.2)

/-- Generic image interface: equality is required only on the actual output
image. The concrete examples below construct it, without assuming equality
of arbitrary functional continuations. This interface enumerates the image;
it does not assert a bound on the cost of producing it. -/
def outputRegime {source : CausalConstitutiveState} (execution : Execution source)
    (equality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution))) :
    ObligationRegime (profileCarrier execution) :=
  ProducedOutputImage.imageRegime (profileCarrier execution) (interpret execution) equality

theorem output_fibres {source : CausalConstitutiveState} (execution : Execution source)
    (equality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution)))
    (p q : Profile execution) :
    (outputRegime execution equality).carry p = (outputRegime execution equality).carry q ↔
      interpret execution p = interpret execution q :=
  ProducedOutputImage.image_carry_fibres (profileCarrier execution) (interpret execution) equality p q

theorem output_width_one_iff {source : CausalConstitutiveState} (execution : Execution source)
    (equality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution))) :
    (outputRegime execution equality).frontier.length = 1 ↔
      ∀ p q, interpret execution p = interpret execution q :=
  ProducedOutputImage.image_width_one_iff_converges (profileCarrier execution) (interpret execution)
    equality (firstProfile execution)

def pathLength : {source : CausalConstitutiveState} → (execution : Execution source) →
    Profile execution → Nat
  | _, .finish _ _, _ => 0
  | _, .step _ _ tail, profile => pathLength (tail profile.1) profile.2 + 1

def endpoint : {source : CausalConstitutiveState} → (execution : Execution source) →
    Profile execution → CausalConstitutiveState
  | source, .finish _ _, _ => source
  | _, .step _ _ tail, profile => endpoint (tail profile.1) profile.2

def headProduction {source : CausalConstitutiveState} (execution : Execution source) :
    Option ((opening : Opening source) × LocalProduction opening) :=
  match execution with
  | .finish _ _ => none
  | .step opening head _ => some ⟨opening, head⟩

theorem execute_head_exact (fuel : Nat) (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (same : source.assignment = arrival.val) :
    headProduction (execute (fuel + 1) source arrival same) =
      (chooseOpening source arrival).map (fun opening => ⟨opening, executeOpening opening⟩) := by
  unfold execute
  cases chooseOpening source arrival <;> rfl

theorem execute_head_horizon_independent (leftFuel rightFuel : Nat) (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (same : source.assignment = arrival.val) :
    headProduction (execute (leftFuel + 1) source arrival same) =
      headProduction (execute (rightFuel + 1) source arrival same) :=
  (execute_head_exact leftFuel source arrival same).trans (execute_head_exact rightFuel source arrival same).symm

theorem execute_path_bounded : (fuel : Nat) → (source : CausalConstitutiveState) →
    (arrival : GeneratedStructuralBranchContinuation source.operationalState) →
    (same : source.assignment = arrival.val) →
    (profile : Profile (execute fuel source arrival same)) →
    pathLength (execute fuel source arrival same) profile ≤ fuel
  | 0, _, _, _, _ => Nat.le_refl 0
  | fuel + 1, source, arrival, same, profile => by
      revert profile
      dsimp only [execute]
      cases chooseOpening source arrival with
      | none => exact fun _ => Nat.zero_le _
      | some opening =>
          intro profile
          exact Nat.succ_le_succ (execute_path_bounded fuel _ _ rfl profile.2)

inductive AcceptedPath : {source : CausalConstitutiveState} →
    (execution : Execution source) → Profile execution → Prop where
  | finish {source : CausalConstitutiveState}
      {arrival : GeneratedStructuralBranchContinuation source.operationalState}
      {exactAssignment : source.assignment = arrival.val} (profile : Unit)
      (accepted : GeneratedStructuralBranchAccept source.operationalState arrival) :
      AcceptedPath (.finish arrival exactAssignment) profile
  | step {source : CausalConstitutiveState} {opening : Opening source} {head : LocalProduction opening}
      {tail : (formed : Identity opening) → Execution (produceSuccessor head formed).state}
      (formed : Identity opening) {rest : Profile (tail formed)}
      (accepted : AcceptedPath (tail formed) rest) : AcceptedPath (.step opening head tail) ⟨formed, rest⟩

theorem interpret_preserves {source : CausalConstitutiveState} {execution : Execution source}
    {profile : Profile execution} (accepted : AcceptedPath execution profile) :
    GeneratedStructuralBranchAccept source.operationalState (interpret execution profile) := by
  induction accepted with
  | finish _ accepted => exact accepted
  | step formed _ ih => exact (produceSuccessor _ formed).restore_preserves _ ih

namespace SeparatingExample
open MixedExample

def head : LocalProduction second := executeOpening second
def left := produceSuccessor head (identity second false)
def right := produceSuccessor head (identity second true)

theorem successor_states_distinct : left.state ≠ right.state := by
  intro same
  have observed := congrArg (fun state => state.assignment 1) same
  cases observed

def left_formation : GeneratedChildFormation first.next.operationalState 1 false second.fresh
    left.state.operationalState := left.formation

def right_formation : GeneratedChildFormation first.next.operationalState 1 true second.fresh
    right.state.operationalState := right.formation

def terminalExecution : Execution first.next :=
  .step second head (fun formed => .finish (produceSuccessor head formed).arrival rfl)

def terminalProfile (value : Bool) : Profile terminalExecution := ⟨identity second value, ()⟩

theorem terminal_interpretation (value : Bool) :
    interpret terminalExecution (terminalProfile value) = produced (identity second value) :=
  produced_successor_action head (identity second value)

theorem terminal_targets_distinct :
    interpret terminalExecution (terminalProfile false) ≠
      interpret terminalExecution (terminalProfile true) := by
  rw [terminal_interpretation, terminal_interpretation]
  exact second_outputs_distinct

end SeparatingExample

namespace DependentTailExample
open MixedExample

def arrival : GeneratedStructuralBranchContinuation first.next.operationalState := first.input true
def selectedOpening : Opening first.next :=
  (chooseOpening first.next arrival).get (by rfl)
def head := executeOpening selectedOpening
def left := produceSuccessor head (identity selectedOpening false)
def right := produceSuccessor head (identity selectedOpening true)
def followingOpening : Opening left.state := (chooseOpening left.state left.arrival).get (by rfl)
def execution := execute 2 first.next arrival rfl

theorem selection_from_produced_state : selectedOpening.selected = 1 ∧ followingOpening.selected = 2 :=
  ⟨rfl, rfl⟩

theorem separating_discovery_fails :
    (runEndogenousFlipDiscovery first.next.operationalState).outcome.discovered? = none := rfl

theorem right_has_no_next_opening : chooseOpening right.state right.arrival = none := rfl

theorem left_has_next_opening : (chooseOpening left.state left.arrival).isSome = true := rfl

def leftProfile (value : Bool) : Profile execution :=
  ⟨identity selectedOpening false, ⟨identity followingOpening value, ()⟩⟩

def rightProfile : Profile execution := ⟨identity selectedOpening true, ()⟩

theorem different_tail_lengths : pathLength execution (leftProfile true) = 2 ∧
    pathLength execution rightProfile = 1 := ⟨rfl, rfl⟩

theorem produced_endpoints_differ : endpoint execution (leftProfile true) ≠ endpoint execution rightProfile := by
  intro same
  have observed := congrArg (fun state => state.assignment 1) same
  cases observed

theorem outputs_preserve_separation :
    interpret execution (leftProfile true) ≠ interpret execution rightProfile := by
  intro same
  have observed := congrArg (fun output => output.val 1) same
  cases observed

theorem extended_outputs_distinct :
    interpret execution (leftProfile false) ≠ interpret execution (leftProfile true) := by
  intro same
  have observed := congrArg (fun output => output.val 2) same
  cases observed

theorem leftAccepted : AcceptedPath execution (leftProfile true) :=
  .step (identity selectedOpening false) (.step (identity followingOpening true) (.finish () .nil))

theorem rightAccepted : AcceptedPath execution rightProfile :=
  .step (identity selectedOpening true) (.finish () .nil)

theorem accepted_outputs :
    GeneratedStructuralBranchAccept first.next.operationalState (interpret execution (leftProfile true)) ∧
      GeneratedStructuralBranchAccept first.next.operationalState (interpret execution rightProfile) :=
  ⟨interpret_preserves leftAccepted, interpret_preserves rightAccepted⟩

theorem rejected_output :
    ¬ GeneratedStructuralBranchAccept first.next.operationalState (interpret execution (leftProfile false)) := by
  intro accepted
  cases accepted with
  | cons headSatisfied _ => cases headSatisfied

theorem frontier_exact : frontier execution = [leftProfile false, leftProfile true, rightProfile] := rfl

theorem profiles_exhaustive (profile : Profile execution) :
    profile = leftProfile false ∨ profile = leftProfile true ∨ profile = rightProfile := by
  have member := frontier_complete execution profile
  rw [frontier_exact] at member
  cases member with
  | head => exact .inl rfl
  | tail _ rest => cases rest with
    | head => exact .inr (.inl rfl)
    | tail _ last => cases last with
      | head => exact .inr (.inr rfl)
      | tail _ impossible => cases impossible

def observe (output : GeneratedStructuralBranchContinuation first.next.operationalState) :=
  (output.val 1, output.val 2)

theorem observation_injective (p q : Profile execution)
    (same : observe (interpret execution p) = observe (interpret execution q)) : p = q := by
  rcases profiles_exhaustive p with pe | pe | pe <;>
    rcases profiles_exhaustive q with qe | qe | qe
  all_goals subst p; subst q
  all_goals first | rfl | cases same

def imageEquality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution)) :=
  fun left right => match decEq (observe left.val) (observe right.val) with
  | isTrue same => isTrue (Subtype.ext (by
      rcases left.property with ⟨p, pe⟩
      rcases right.property with ⟨q, qe⟩
      have sameProfile := observation_injective p q (by rw [pe, qe]; exact same)
      exact pe.symm.trans ((congrArg (interpret execution) sameProfile).trans qe)))
  | isFalse different => isFalse (fun same => different (congrArg (fun value => observe value.val) same))

def regime := ProducedOutputImage.imageRegime (profileCarrier execution) (interpret execution) imageEquality

theorem source_width : (profileCarrier execution).frontier.length = 3 := rfl
theorem image_width : regime.frontier.length = 3 := rfl

theorem exact_fibres (p q : Profile execution) : regime.carry p = regime.carry q ↔
    interpret execution p = interpret execution q :=
  ProducedOutputImage.image_carry_fibres (profileCarrier execution) (interpret execution) imageEquality p q

end DependentTailExample

namespace MixedAdaptiveExample
open MixedExample

def arrival : GeneratedStructuralBranchContinuation initialState.operationalState := ⟨initialAssignment, True.intro⟩
def selectedOpening : Opening initialState := (chooseOpening initialState arrival).get (by rfl)
def head := executeOpening selectedOpening
def execution := execute 3 initialState arrival rfl

theorem convergent_successors :
    (produceSuccessor head (identity selectedOpening false)).state = first.next ∧
      (produceSuccessor head (identity selectedOpening true)).state = first.next := ⟨rfl, rfl⟩

theorem canonical_inputs_accepted (formed : Identity selectedOpening) : Accept formed (canonical formed) := by
  have exactFormed := relationallyConstitutedOccurrence_roundTrip formed
  rw [← exactFormed]
  cases formed.position <;> exact .cons rfl .nil

theorem produced_arrivals_accepted (formed : Identity selectedOpening) :
    GeneratedStructuralBranchAccept (produceSuccessor head formed).state.operationalState
      (produceSuccessor head formed).arrival :=
  (produceSuccessor head formed).arrival_accepted_from_action (canonical_inputs_accepted formed)

def embed (value : Bool) (rest : Profile DependentTailExample.execution) : Profile execution :=
  match value with
  | false => ⟨identity selectedOpening false, rest⟩
  | true => ⟨identity selectedOpening true, rest⟩

theorem sources_distinct (rest : Profile DependentTailExample.execution) : embed false rest ≠ embed true rest := by
  intro same
  exact source_distinct selectedOpening (congrArg Sigma.fst same)

theorem interpretation_exact (value : Bool) (rest : Profile DependentTailExample.execution) :
    interpret execution (embed value rest) =
      restoreChild selectedOpening true (interpret DependentTailExample.execution rest) := by
  cases value <;> rfl

theorem computed_grouping (rest : Profile DependentTailExample.execution) :
    interpret execution (embed false rest) = interpret execution (embed true rest) :=
  (interpretation_exact false rest).trans (interpretation_exact true rest).symm

theorem source_width : (profileCarrier execution).frontier.length = 6 := rfl

theorem profiles_exhaustive (profile : Profile execution) :
    (∃ rest, profile = embed false rest) ∨ (∃ rest, profile = embed true rest) := by
  have member := frontier_complete execution profile
  change profile ∈ [embed false (DependentTailExample.leftProfile false),
    embed false (DependentTailExample.leftProfile true), embed false DependentTailExample.rightProfile,
    embed true (DependentTailExample.leftProfile false),
    embed true (DependentTailExample.leftProfile true), embed true DependentTailExample.rightProfile] at member
  cases member with
  | head => exact .inl ⟨_, rfl⟩
  | tail _ second => cases second with
    | head => exact .inl ⟨_, rfl⟩
    | tail _ third => cases third with
      | head => exact .inl ⟨_, rfl⟩
      | tail _ fourth => cases fourth with
        | head => exact .inr ⟨_, rfl⟩
        | tail _ fifth => cases fifth with
          | head => exact .inr ⟨_, rfl⟩
          | tail _ sixth => cases sixth with
            | head => exact .inr ⟨_, rfl⟩
            | tail _ impossible => cases impossible

def observe (output : GeneratedStructuralBranchContinuation initialState.operationalState) :=
  (output.val 1, output.val 2)

theorem observation_faithful (p q : Profile execution)
    (same : observe (interpret execution p) = observe (interpret execution q)) :
    interpret execution p = interpret execution q := by
  rcases profiles_exhaustive p with ⟨pRest, pe⟩ | ⟨pRest, pe⟩ <;>
    rcases profiles_exhaustive q with ⟨qRest, qe⟩ | ⟨qRest, qe⟩
  all_goals
    rw [pe, qe, interpretation_exact, interpretation_exact] at same ⊢
    have restSame := DependentTailExample.observation_injective pRest qRest same
    exact congrArg (fun rest => restoreChild selectedOpening true (interpret DependentTailExample.execution rest)) restSame

def imageEquality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution)) :=
  fun left right => match decEq (observe left.val) (observe right.val) with
  | isTrue same => isTrue (Subtype.ext (by
      rcases left.property with ⟨p, pe⟩
      rcases right.property with ⟨q, qe⟩
      exact pe.symm.trans ((observation_faithful p q (by rw [pe, qe]; exact same)).trans qe)))
  | isFalse different => isFalse (fun same => different (congrArg (fun value => observe value.val) same))

def regime := ProducedOutputImage.imageRegime (profileCarrier execution) (interpret execution) imageEquality

theorem image_width : regime.frontier.length = 3 := rfl

theorem exact_fibres (p q : Profile execution) : regime.carry p = regime.carry q ↔
    interpret execution p = interpret execution q :=
  ProducedOutputImage.image_carry_fibres (profileCarrier execution) (interpret execution) imageEquality p q

theorem carries_together_without_identification (rest : Profile DependentTailExample.execution) :
    embed false rest ≠ embed true rest ∧ regime.carry (embed false rest) = regime.carry (embed true rest) :=
  ⟨sources_distinct rest, (exact_fibres _ _).mpr (computed_grouping rest)⟩

theorem separates_dependent_futures (firstValue : Bool) :
    regime.carry (embed firstValue (DependentTailExample.leftProfile true)) ≠
      regime.carry (embed firstValue DependentTailExample.rightProfile) := by
  intro same
  have observed := congrArg (fun output => output.val 1) ((exact_fibres _ _).mp same)
  rw [interpretation_exact, interpretation_exact] at observed
  cases observed

end MixedAdaptiveExample
end ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.restoreChild
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.restoreChild_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.restoreChild_reflects
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.advanceState
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.ProducedSuccessor.assignment_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.ProducedSuccessor.generation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.ProducedSuccessor.formation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.ProducedSuccessor.restore_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.produceSuccessor
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.produced_successor_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.ProducedSuccessor.arrival_accepted_from_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.flip_fresh_decisions
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.childInput
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.chooseOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.execute
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.Profile
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.profileEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.frontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.frontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.frontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.profileCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.firstProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.frontier_length_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.interpret
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.outputRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.output_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.output_width_one_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.pathLength
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.endpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.execute_head_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.execute_head_horizon_independent
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.execute_path_bounded
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.interpret_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.SeparatingExample.successor_states_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.SeparatingExample.left_formation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.SeparatingExample.right_formation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.SeparatingExample.terminal_interpretation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.SeparatingExample.terminal_targets_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.selection_from_produced_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.right_has_no_next_opening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.left_has_next_opening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.different_tail_lengths
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.produced_endpoints_differ
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.outputs_preserve_separation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.extended_outputs_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.accepted_outputs
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.rejected_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.profiles_exhaustive
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.observation_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.source_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.image_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.DependentTailExample.exact_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.convergent_successors
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.canonical_inputs_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.produced_arrivals_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.sources_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.interpretation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.computed_grouping
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.source_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.observation_faithful
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.image_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.exact_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.carries_together_without_identification
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Adaptive.MixedAdaptiveExample.separates_dependent_futures
/- AXIOM_AUDIT_END -/
