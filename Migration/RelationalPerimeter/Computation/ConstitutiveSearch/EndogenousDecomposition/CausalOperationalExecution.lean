import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseOperationalStatus
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOutputObligations

/-!
# Execution that produces its operational decomposition stage by stage

This is the causal object used by the final certificate.  It does not receive a
completed execution history.  Its executor performs the authoritative stage
construction and, at that same recursive step, forms the local relational
decomposition before recursing from the state just produced.

The instrumented and causal histories are downstream erasures of this single
object. They are not inputs from which the operational decomposition is
reconstructed afterwards.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

/-- The root context is indexed by the actually initialized public state. -/
abbrev InitialOperationalPrefix (input : Nat) : Type 2 :=
  ConstitutedOperationalPrefix (causalStateOfThreadedState
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input)))

def initialOperationalPrefix (input : Nat) : InitialOperationalPrefix input :=
  .root _

set_option genSizeOf false in
/--
The tail receives both the exact state and the closed context produced by the
head. The context is a past history, not an arbitrary type parameter.
-/
inductive CausalOperationalExecutionHistory :
    {depth _count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      ConstitutedOperationalPrefix (causalStateOfThreadedState state) → Type 3 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
      (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) :
      CausalOperationalExecutionHistory (_count := 0) state context
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
      (head : SequentialStageRun depth assignment)
      (headRun : ThreadedConstitutiveStageRun state head)
      (headProduction : ExecutedStageOperationalProduction
        context (causalStageOfThreadedStage headRun))
      (tail : CausalOperationalExecutionHistory (_count := count)
        headRun.nextRun.next headProduction.nextContext) :
      CausalOperationalExecutionHistory (_count := count + 1) state context

/-- The next stage and its production, without a remaining-length input. -/
structure CausalOperationalHead
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) : Type 3 where
  stage : SequentialStageRun depth assignment
  run : ThreadedConstitutiveStageRun state stage
  production : ExecutedStageOperationalProduction context (causalStageOfThreadedStage run)

/-- Observable boundaries of the existing primitive operations.
`applied` includes the existing stage builder and next-state formation.
These events do not claim instruction-level or wall-clock timing. -/
inductive OperationalProductionEvent where
  | discovered (depth : Nat)
  | applied (depth : Nat)
  | decomposed (depth : Nat)
  deriving DecidableEq

/-- Build from the discovery already performed, without searching a second time. -/
def buildFromExecutedDiscovery {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryExact : discoveryRun = runThreadedNextDiscovery state) :
    ConstructedThreadedStageRun state :=
  match found : discoveryRun.outcome.discovered? with
  | none => False.elim ((runThreadedNextDiscovery_found state fresh)
      (discoveryExact ▸ found))
  | some discovery =>
      buildThreadedConstitutiveStage state discoveryRun discoveryExact
        discovery found
        (by rw [discoveryExact, runThreadedNextDiscovery_discovered_exact state fresh] at found
            exact found)
        (discoveryExact.symm ▸ runThreadedNextDiscovery_work_le_canonical state fresh)
        (state.decisionsAvoidNext fresh)

universe u
/-- A program over fixed production primitives. No constructor accepts a log.
The interpreter calls each primitive and emits its own corresponding event. -/
inductive OperationalProductionProgram : Type u → Type (max (u + 1) 3) where
  | done {Result : Type u} (value : Result) : OperationalProductionProgram Result
  | discover {Result : Type u} {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
      (next : (discovery : ThreadedNextDiscoveryRun depth state) →
        discovery = runThreadedNextDiscovery state → OperationalProductionProgram Result) :
      OperationalProductionProgram Result
  | applyStage {Result : Type u} {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment)
      (fresh : ThreadedStateFreshForNext state)
      (discovery : ThreadedNextDiscoveryRun depth state)
      (exactDiscovery : discovery = runThreadedNextDiscovery state)
      (next : ConstructedThreadedStageRun state → OperationalProductionProgram Result) :
      OperationalProductionProgram Result
  | decompose {Result : Type u} {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {stage : SequentialStageRun depth assignment}
      (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
      (run : ThreadedConstitutiveStageRun state stage)
      (next : ExecutedStageOperationalProduction context (causalStageOfThreadedStage run) →
        OperationalProductionProgram Result) : OperationalProductionProgram Result
  | mapResult {Input Result : Type u} (program : OperationalProductionProgram Input)
      (map : Input → Result) : OperationalProductionProgram Result

/-- Value and trace are produced together, not reconstructed from a completed history. -/
def OperationalProductionProgram.evaluate {Result : Type u} :
    OperationalProductionProgram Result → Result × List OperationalProductionEvent
  | .done value => (value, [])
  | .discover (depth := depth) state next =>
      let discovery := runThreadedNextDiscovery state
      let result := (next discovery rfl).evaluate
      (result.1, .discovered depth :: result.2)
  | .applyStage (depth := depth) state fresh discovery exactDiscovery next =>
      let built := buildFromExecutedDiscovery state fresh discovery exactDiscovery
      let result := (next built).evaluate
      (result.1, .applied depth :: result.2)
  | .decompose (depth := depth) context run next =>
      let production := prefixLocalOperationalProducer context (causalStageOfThreadedStage run)
      let result := (next production).evaluate
      (result.1, .decomposed depth :: result.2)
  | .mapResult program map =>
      let result := program.evaluate
      (map result.1, result.2)

/-- Shared head program used by the head API and by the recursive executor. -/
def withCausalOperationalHead {Result : Type u}
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state)
    (next : CausalOperationalHead state context → OperationalProductionProgram Result) :
    OperationalProductionProgram Result :=
  .discover state fun discovery exactDiscovery =>
    .applyStage state fresh discovery exactDiscovery fun built =>
      .decompose context built.run fun production =>
        next ⟨built.stage, built.run, production⟩

def causalOperationalHeadProgram {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    OperationalProductionProgram (CausalOperationalHead state context) :=
  withCausalOperationalHead state context fresh .done

/-- Specialised evaluator for the fixed three-primitive head program.
The equation below checks it against the generic interpreter, avoiding repeated
normalisation of its polymorphic recursor in downstream dependent types. -/
def executeCausalOperationalHeadWithTrace {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    CausalOperationalHead state context × List OperationalProductionEvent :=
  let discovery := runThreadedNextDiscovery state
  let built := buildFromExecutedDiscovery state fresh discovery rfl
  let production := prefixLocalOperationalProducer context (causalStageOfThreadedStage built.run)
  (⟨built.stage, built.run, production⟩,
    [.discovered depth, .applied depth, .decomposed depth])

theorem executeCausalOperationalHeadWithTrace_exact
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    executeCausalOperationalHeadWithTrace state context fresh =
      (causalOperationalHeadProgram state context fresh).evaluate := rfl

/-- The public head is the value of the verified primitive-program evaluator. -/
def executeCausalOperationalHead {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) : CausalOperationalHead state context :=
  (executeCausalOperationalHeadWithTrace state context fresh).1

/-- Program construction continues only from the state and context it has produced. -/
def causalOperationalExecutionProgram (count : Nat) :
    {depth : Nat} → {assignment : SequentialAssignment depth} →
    (state : ThreadedConstitutiveState depth assignment) →
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) →
    ThreadedStateFreshForNext state →
    OperationalProductionProgram (CausalOperationalExecutionHistory (_count := count) state context)
  | _, _, state, context, fresh => match count with
    | 0 => .done (.nil state context)
    | count + 1 => withCausalOperationalHead state context fresh fun produced =>
      .mapResult
        (causalOperationalExecutionProgram count produced.run.nextRun.next
          produced.production.nextContext (produced.run.nextRun.fresh fresh))
        (fun tail => .step produced.stage produced.run produced.production tail)

/-- Evaluation yields both the historical value and the chronological primitive trace. -/
def executeCausalOperationalExecutionWithTrace (count : Nat) :
    {depth : Nat} → {assignment : SequentialAssignment depth} →
    (state : ThreadedConstitutiveState depth assignment) →
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)) →
    ThreadedStateFreshForNext state →
    CausalOperationalExecutionHistory (_count := count) state context × List OperationalProductionEvent
  | _, _, state, context, fresh => match count with
    | 0 => (.nil state context, [])
    | count + 1 =>
      let produced := executeCausalOperationalHeadWithTrace state context fresh
      let rest := executeCausalOperationalExecutionWithTrace count produced.1.run.nextRun.next
        produced.1.production.nextContext (produced.1.run.nextRun.fresh fresh)
      (.step produced.1.stage produced.1.run produced.1.production rest.1, produced.2 ++ rest.2)

/-- The specialised recursive evaluator implements the primitive program exactly. -/
theorem executeWithTrace_program_exact (count : Nat)
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    executeCausalOperationalExecutionWithTrace count state context fresh =
      (causalOperationalExecutionProgram count state context fresh).evaluate := by
  induction count generalizing depth assignment with
  | zero => rfl
  | succ count ih =>
    let produced := executeCausalOperationalHead state context fresh
    change (CausalOperationalExecutionHistory.step produced.stage produced.run produced.production
      (executeCausalOperationalExecutionWithTrace count produced.run.nextRun.next
        produced.production.nextContext (produced.run.nextRun.fresh fresh)).1,
      OperationalProductionEvent.discovered depth :: .applied depth :: .decomposed depth ::
      (executeCausalOperationalExecutionWithTrace count produced.run.nextRun.next
        produced.production.nextContext (produced.run.nextRun.fresh fresh)).2) = _
    rw [ih produced.run.nextRun.next produced.production.nextContext (produced.run.nextRun.fresh fresh)]
    rfl

def executeCausalOperationalExecutionHistory (count : Nat)
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    CausalOperationalExecutionHistory (_count := count) state context :=
  (executeCausalOperationalExecutionWithTrace count state context fresh).1

/-- Required order is specified independently of the program's returned history. -/
def operationalProductionTimeline : Nat → Nat → List OperationalProductionEvent
  | 0, _ => []
  | count + 1, depth => .discovered depth :: .applied depth :: .decomposed depth ::
      operationalProductionTimeline count (depth + 1)

theorem operationalProductionTimeline_exact (count : Nat)
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionWithTrace count state context fresh).2 =
      operationalProductionTimeline count depth := by
  induction count generalizing depth assignment with
  | zero => rfl
  | succ count ih =>
    let produced := executeCausalOperationalHead state context fresh
    change .discovered depth :: .applied depth :: .decomposed depth ::
      (executeCausalOperationalExecutionWithTrace count produced.run.nextRun.next
        produced.production.nextContext (produced.run.nextRun.fresh fresh)).2 = _
    exact congrArg (fun tail => OperationalProductionEvent.discovered depth ::
      .applied depth :: .decomposed depth :: tail)
      (ih produced.run.nextRun.next produced.production.nextContext (produced.run.nextRun.fresh fresh))

/-- Observe the head without evaluating any tail or adding a positivity cast. -/
def CausalOperationalExecutionHistory.head?
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} :
    CausalOperationalExecutionHistory (_count := count) state context →
      Option (CausalOperationalHead state context)
  | .nil _ _ => none
  | .step stage run production _ => some ⟨stage, run, production⟩

/-- Head production of the public recursion is the prefix-only producer itself. -/
theorem executeCausalOperationalExecutionHistory_head
    (remaining : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory (remaining + 1) state context fresh).head? =
      some (executeCausalOperationalHead state context fresh) := rfl

/-- Varying the future horizon leaves the constructed head unchanged. -/
theorem executeCausalOperationalExecutionHistory_head_independent
    (leftRemaining rightRemaining : Nat)
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory (leftRemaining + 1) state context fresh).head? =
      (executeCausalOperationalExecutionHistory (rightRemaining + 1) state context fresh).head? :=
  rfl

/-- The recursive transition exposes the exact produced state and context. -/
theorem executeCausalOperationalExecutionHistory_step
    (remaining : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    executeCausalOperationalExecutionHistory (remaining + 1) state context fresh =
      let produced := executeCausalOperationalHead state context fresh
      CausalOperationalExecutionHistory.step produced.stage produced.run produced.production
        (executeCausalOperationalExecutionHistory remaining produced.run.nextRun.next
          produced.production.nextContext (produced.run.nextRun.fresh fresh)) := rfl

/-- Different valid tails do not determine the already constructed head. -/
theorem causalOperational_same_head_different_tails
    {depth leftCount rightCount : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (stage : SequentialStageRun depth assignment)
    (run : ThreadedConstitutiveStageRun state stage)
    (production : ExecutedStageOperationalProduction context (causalStageOfThreadedStage run))
    (leftTail : CausalOperationalExecutionHistory (_count := leftCount)
      run.nextRun.next production.nextContext)
    (rightTail : CausalOperationalExecutionHistory (_count := rightCount)
      run.nextRun.next production.nextContext) :
    (CausalOperationalExecutionHistory.step stage run production leftTail).head? =
      (CausalOperationalExecutionHistory.step stage run production rightTail).head? :=
  rfl

/-- Erase only the operational material; the executed states are unchanged. -/
def CausalOperationalExecutionHistory.instrumented :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
      CausalOperationalExecutionHistory (_count := count) state context →
      ConstitutiveExecutionHistory (count := count) state
  | _, _, _, _, _, .nil state _ => .nil state
  | _, _, _, _, _, .step head headRun _ tail =>
      .step head headRun tail.instrumented

/-- The causal run is an erasure of the same fused execution. -/
def CausalOperationalExecutionHistory.causalRun :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
      (history : CausalOperationalExecutionHistory (_count := count) state context) →
      CausalConstitutiveExecutionHistory count (causalStateOfThreadedState state)
  | _, _, _, _, _, .nil state _ =>
      CausalConstitutiveExecutionHistory.nil (causalStateOfThreadedState state)
  | _, _, _, _, _, .step _ headRun _ tail =>
      CausalConstitutiveExecutionHistory.step
        (causalStageOfThreadedStage headRun) tail.causalRun

theorem CausalOperationalExecutionHistory.causalRun_exact :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
      (history : CausalOperationalExecutionHistory (_count := count) state context) →
      history.causalRun = causalHistoryOfInstrumentedHistory history.instrumented
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .step _ _ _ tail => by
      simp only [CausalOperationalExecutionHistory.causalRun,
        CausalOperationalExecutionHistory.instrumented,
        causalHistoryOfInstrumentedHistory]
      rw [tail.causalRun_exact]

/-- Read only the local decompositions actually stored by the fused execution. -/
def CausalOperationalExecutionHistory.stagewiseDecomposition :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
      (history : CausalOperationalExecutionHistory (_count := count) state context) →
      StagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, _, .nil _ _ => .nil
  | _, _, _, _, _, .step _ _ headProduction tail =>
      .step headProduction.decomposition tail.stagewiseDecomposition

theorem CausalOperationalExecutionHistory.headsArePrefixLocal :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)} →
      (history : CausalOperationalExecutionHistory (_count := count) state context) →
      history.stagewiseDecomposition =
        buildStagewiseExecutedDecompositionHistory history.causalRun
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .step _ _ headProduction tail => by
      change StagewiseExecutedDecompositionHistory.step
          headProduction.decomposition tail.stagewiseDecomposition =
        StagewiseExecutedDecompositionHistory.step (executedStageDecomposition _) _
      rw [headProduction.decompositionExact, tail.headsArePrefixLocal]
      rfl

/-- Removing operational context gives the original authoritative execution. -/
theorem executeCausalOperationalExecutionHistory_instrumented_exact
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionHistory count state context fresh).instrumented =
      executeConstitutiveExecutionHistory count state fresh := by
  induction count generalizing depth assignment state with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [executeCausalOperationalExecutionHistory_step, executeConstitutiveExecutionHistory]
      split
      case h_1 =>
        rename_i notFound
        exact False.elim ((runThreadedNextDiscovery_found state fresh) notFound)
      case h_2 =>
        rename_i discovery found
        let built := buildThreadedConstitutiveStage state (runThreadedNextDiscovery state)
          rfl discovery found
          (by rw [← runThreadedNextDiscovery_discovered_exact state fresh]; exact found)
          (runThreadedNextDiscovery_work_le_canonical state fresh)
          (state.decisionsAvoidNext fresh)
        have headExact : executeCausalOperationalHead state context fresh =
            { stage := built.stage, run := built.run,
              production := prefixLocalOperationalProducer context
                (causalStageOfThreadedStage built.run) } := by
          unfold executeCausalOperationalHead executeCausalOperationalHeadWithTrace
            buildFromExecutedDiscovery
          dsimp only
          split
          case h_1 =>
            rename_i absent
            exact False.elim ((runThreadedNextDiscovery_found state fresh) absent)
          case h_2 =>
            rename_i other otherFound
            have same : other = discovery := Option.some.inj (Eq.trans otherFound.symm found)
            cases same
            rfl
        have stepExact := congrArg
          (fun produced : CausalOperationalHead state context =>
            (CausalOperationalExecutionHistory.step produced.stage produced.run produced.production
              (executeCausalOperationalExecutionHistory count produced.run.nextRun.next
                produced.production.nextContext (produced.run.nextRun.fresh fresh))).instrumented)
          headExact
        exact Eq.trans stepExact
          (congrArg (fun tail => ConstitutiveExecutionHistory.step built.stage built.run tail)
            (inductionHypothesis _ _ _))

/-- The public execution starts at the state actually produced by initialization. -/
def publicCausalOperationalExecution (input : Nat) :
    CausalOperationalExecutionHistory (_count := resolutionLength input)
      (initialThreadedConstitutiveStateFromInitialization
        (initializeConstitutiveHistory input))
      (initialOperationalPrefix input) :=
  executeCausalOperationalExecutionHistory (resolutionLength input)
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialOperationalPrefix input)
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

/-- The public execution and its operation trace share one evaluation. -/
def publicCausalOperationalExecutionWithTrace (input : Nat) :=
  executeCausalOperationalExecutionWithTrace (resolutionLength input)
    (initialThreadedConstitutiveStateFromInitialization (initializeConstitutiveHistory input))
    (initialOperationalPrefix input)
    (initialThreadedConstitutiveStateFromInitialization_fresh (initializeConstitutiveHistory input))

theorem publicCausalOperationalExecutionWithTrace_value (input : Nat) :
    (publicCausalOperationalExecutionWithTrace input).1 = publicCausalOperationalExecution input := rfl

theorem publicCausalOperationalExecutionWithTrace_order (input : Nat) :
    (publicCausalOperationalExecutionWithTrace input).2 =
      operationalProductionTimeline (resolutionLength input) input :=
  operationalProductionTimeline_exact _ _ _ _

/--
The authoritative public roles are constituted directly from the sole fused
execution.  No projected history defines a parallel scientific carrier.
-/
def publicRelationalConstitutiveRoles (input : Nat) :=
  (publicCausalOperationalExecution input).stagewiseDecomposition.roles

/-- Output images are projected from the head productions stored by this execution. -/
def CausalOperationalExecutionHistory.outputPolicy
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (history : CausalOperationalExecutionHistory (_count := count) state context) :
    RolewiseObligationPolicy history.stagewiseDecomposition.roles :=
  ExecutedOutput.ofStagewise history.stagewiseDecomposition

theorem CausalOperationalExecutionHistory.outputPolicy_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (history : CausalOperationalExecutionHistory (_count := count) state context) :
    history.outputPolicy = ExecutedOutput.policy history.stagewiseDecomposition.reduction :=
  ExecutedOutput.ofStagewise_exact history.stagewiseDecomposition

def publicExecutedOutputPolicy (input : Nat) :
    RolewiseObligationPolicy (publicRelationalConstitutiveRoles input) :=
  (publicCausalOperationalExecution input).outputPolicy

theorem publicExecutedOutputPolicy_exact (input : Nat) :
    publicExecutedOutputPolicy input =
      ExecutedOutput.policy (publicCausalOperationalExecution input).stagewiseDecomposition.reduction :=
  (publicCausalOperationalExecution input).outputPolicy_exact

/-- Statuses are projected from the productions stored by this execution. -/
def CausalOperationalExecutionHistory.operationalStatuses
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (history : CausalOperationalExecutionHistory (_count := count) state context) :
    RoleStatus.History history.stagewiseDecomposition.roles :=
  RoleStatus.ofStagewise history.stagewiseDecomposition

/-- The extracted reduction and the stored productions supply exactly one status history. -/
theorem CausalOperationalExecutionHistory.operationalStatuses_exact
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {context : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
    (history : CausalOperationalExecutionHistory (_count := count) state context) :
    history.operationalStatuses = RoleStatus.executed history.stagewiseDecomposition.reduction :=
  RoleStatus.ofStagewise_eq_executed history.stagewiseDecomposition

/-- These are projections of the actual local productions, not new discovery runs. -/
def publicOperationalStatuses (input : Nat) :
    RoleStatus.History (publicRelationalConstitutiveRoles input) :=
  (publicCausalOperationalExecution input).operationalStatuses

theorem publicOperationalStatuses_exact (input : Nat) :
    publicOperationalStatuses input =
      RoleStatus.executed (publicCausalOperationalExecution input).stagewiseDecomposition.reduction :=
  (publicCausalOperationalExecution input).operationalStatuses_exact

/-- The unique public source carrier, read from the fused constitutive roles. -/
def publicRoleProfileFiniteCarrier (input : Nat) : Extensive.FiniteCarrier :=
  roleProfileFiniteCarrier (publicRelationalConstitutiveRoles input)

theorem publicRoleProfileFiniteCarrier_width (input : Nat) :
    (publicRoleProfileFiniteCarrier input).frontier.length =
      2 ^ (input + 1) :=
  roleProfileFiniteCarrier_width (publicRelationalConstitutiveRoles input)

/-- Public role-carrier form of the exact exponential-width equivalence. -/
theorem public_exponentialWidth_iff_distinctSeparateConservation
    (input : Nat)
    (regime : Extensive.ObligationRegime
      (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  roleConstituted_exponentialWidth_iff_distinctSeparateConservation
    (publicRelationalConstitutiveRoles input) regime

/-- Public factorized-addressing form of the same exact equivalence. -/
theorem public_exponentialWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : Extensive.ObligationRegime
      (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Nonempty
        (Extensive.ExactRegimeSeparateCapacity regime
          (publicRoleProfileFiniteCarrier input).frontier.length) :=
  roleConstituted_exponentialWidth_iff_exactRegimeCapacity
    (publicRelationalConstitutiveRoles input) regime

/-- Its instrumented erasure is exactly the history exposed by the public run. -/
theorem publicCausalOperationalExecution_instrumented_exact (input : Nat) :
    (publicCausalOperationalExecution input).instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory := by
  exact executeCausalOperationalExecutionHistory_instrumented_exact
    (resolutionLength input)
    (initialThreadedConstitutiveStateFromInitialization
      (initializeConstitutiveHistory input))
    (initialOperationalPrefix input)
    (initialThreadedConstitutiveStateFromInitialization_fresh
      (initializeConstitutiveHistory input))

/-- The fused public causal run is the causal run of the authoritative public realization. -/
theorem publicCausalOperationalExecution_causalRun_exact (input : Nat) :
    (publicCausalOperationalExecution input).causalRun =
      (publicInstrumentedExecutionRealization input).causalRun := by
  exact Eq.trans
    (publicCausalOperationalExecution input).causalRun_exact
    (congrArg causalHistoryOfInstrumentedHistory
      (publicCausalOperationalExecution_instrumented_exact input))

/-- The roles constituted from the fused run are definitionally the public roles. -/
theorem publicCausalOperationalExecution_roles_exact (input : Nat) :
    (publicCausalOperationalExecution input).stagewiseDecomposition.roles =
      publicRelationalConstitutiveRoles input :=
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.outputPolicy
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.outputPolicy_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicExecutedOutputPolicy
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicExecutedOutputPolicy_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.operationalStatuses
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.operationalStatuses_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicOperationalStatuses
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicOperationalStatuses_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalHeadWithTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalHeadWithTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeWithTrace_program_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecutionWithTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecutionWithTrace_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecutionWithTrace_order

#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalProductionEvent
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildFromExecutedDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalProductionProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalProductionProgram.evaluate
#print axioms ConstitutiveSearch.EndogenousDecomposition.withCausalOperationalHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOperationalHeadProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOperationalExecutionProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionWithTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalProductionTimeline
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalProductionTimeline_exact

#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_head
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_head_independent
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_step

#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.head?
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOperational_same_head_different_tails
#print axioms ConstitutiveSearch.EndogenousDecomposition.InitialOperationalPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.initialOperationalPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.instrumented
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.causalRun
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.causalRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.stagewiseDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecutionHistory.headsArePrefixLocal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeCausalOperationalExecutionHistory_instrumented_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRelationalConstitutiveRoles
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleProfileFiniteCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleProfileFiniteCarrier_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_exponentialWidth_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_instrumented_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_causalRun_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalOperationalExecution_roles_exact
/- AXIOM_AUDIT_END -/
