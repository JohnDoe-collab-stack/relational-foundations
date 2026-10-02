import RelationalPerimeter.Computation.ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerCore
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory

/-!
# Extensional observation and operational non-factorization

An extensional stability view records the source and retained states, the one
continuation actually observed at each state, acceptance, and the measured
width trace.  It deliberately does not contain the total action of the
transport on arbitrary continuations.

Both the executed-system separator and the finite explanatory separator prove
that this omission is substantive: two acceptance-preserving transports agree
on the recorded observation and width trace, yet differ on another admissible
continuation.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- What state-and-width observation retains from one operational reduction. -/
structure ExtensionalOperationalStabilityView (system : SearchSystem) where
  sourceState : system.State
  retainedState : system.State
  observedSource : system.Continuation sourceState
  observedRetained : system.Continuation retainedState
  sourceAccepted : system.Accept sourceState observedSource
  retainedAccepted : system.Accept retainedState observedRetained
  widthTrace : List Nat
  widthBound : WidthTraceAtMost 2 widthTrace

/-- Canonical bound for the numerical one-stage width readout. -/
theorem singleStageWidthReadoutBound : WidthTraceAtMost 2 [1, 2, 1] :=
  .cons (Nat.succ_le_succ (Nat.zero_le 1))
    (.cons (Nat.le_refl 2)
      (.cons (Nat.succ_le_succ (Nat.zero_le 1)) .nil))

/-- The executed width readout carries the same numerical bound. -/
theorem executedStageWidthReadoutBound {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    WidthTraceAtMost 2 (executedStageWidthTrace run) := by
  rw [executedStageWidthTrace_exact]
  exact singleStageWidthReadoutBound

/-- Extensional view of the reduction actually executed at one stage. The width
trace is a derived numerical observation, not a premise used to constitute the
reduction. -/
def executedStepToExtensionalView {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExtensionalOperationalStabilityView
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)) :=
  { sourceState := stage.schedule.entry.source
    retainedState := stage.schedule.entry.target
    observedSource := stage.sourceContinuation
    observedRetained := stage.application.output
    sourceAccepted := stage.sourceAccepted
    retainedAccepted := stage.outputAccepted
    widthTrace := executedStageWidthTrace run
    widthBound := executedStageWidthReadoutBound run }

/-- The observed output in the view is exactly the discovered map application. -/
theorem extensionalView_observedOutput_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).observedRetained =
      stage.schedule.entry.relation.mapContinuation
        (executedStepToExtensionalView run).observedSource :=
  stageApplication_eq_returnedRelationMap run

/-- The projected trace is computed from the actual entry/opened/retained lists. -/
theorem extensionalView_widthTrace_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedStepToExtensionalView run).widthTrace =
      executedStageWidthTrace run :=
  rfl

/-- Forget a total transport after recording one accepted source observation,
its transported output, and an explicitly supplied numerical width readout.
The projector does not manufacture the trace: callers must provide both the
readout and its bound. -/
def transportToExtensionalStabilityView
    {system : SearchSystem}
    {source retained : system.State}
    (transport : AcceptingContinuationTransport system source retained)
    (observed : system.Continuation source)
    (accepted : system.Accept source observed)
    (widthTrace : List Nat)
    (widthBound : WidthTraceAtMost 2 widthTrace) :
    ExtensionalOperationalStabilityView system :=
  { sourceState := source
    retainedState := retained
    observedSource := observed
    observedRetained := transport.map observed
    sourceAccepted := accepted
    retainedAccepted := transport.preservesAccept observed accepted
    widthTrace := widthTrace
    widthBound := widthBound }

namespace ExecutedExtensionalSeparator

/-- The acceptance-preserving transport reconstructed by the executed run. -/
def discoveredTransport {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      stage.schedule.entry.source stage.schedule.entry.target :=
  stage.discovery.relation.toAcceptingTransport

/-- A comparison transport on the same executed source and target.  It agrees
with the discovered transport at the continuation actually executed, while
forgetting the discovered action everywhere else. -/
def observedConstantTransport {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      stage.schedule.entry.source stage.schedule.entry.target :=
  { map := fun _ =>
      stage.discovery.relation.mapContinuation stage.sourceContinuation
    preservesAccept := fun _ _ =>
      stage.discovery.relation.mapContinuation_accept
        stage.sourceContinuation stage.sourceAccepted }

/-- Project any total transport on the executed source/target pair to the exact
state-and-quantity view retained by this stage. -/
def executedTransportProjection {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        stage.schedule.entry.source stage.schedule.entry.target →
      ExtensionalOperationalStabilityView
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)) :=
  fun transport =>
    transportToExtensionalStabilityView
      transport
      stage.sourceContinuation stage.sourceAccepted
      (executedStageWidthTrace run) (executedStageWidthReadoutBound run)

/-- The total operational action carried by a transport on the executed pair. -/
def executedTransportAction {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptingContinuationTransport
        (generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        stage.schedule.entry.source stage.schedule.entry.target →
      GeneratedStructuralBranchContinuation stage.schedule.entry.source →
      GeneratedStructuralBranchContinuation stage.schedule.entry.target :=
  fun transport continuation => transport.map continuation

/-- A second source continuation obtained by changing the anchor coordinate.
The anchor is distinct from the selected branch variable, so the constituted
source decision remains realized. -/
def alternateContinuation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    GeneratedStructuralBranchContinuation stage.schedule.entry.source := by
  let anchor := stageAnchorVar (depth + 1)
  refine ⟨Assignment.flipAt anchor stage.sourceContinuation.1, ?_⟩
  change
    Assignment.flipAt anchor stage.sourceContinuation.1 stage.discovery.var = false ∧
      True
  constructor
  · rw [Assignment.flipAt_other]
    · exact stage.sourceContinuation.2.1
    · have selected := sequentialStage_selected_exact stage
      change stage.discovery.var = stageSelectedVar (depth + 1) at selected
      dsimp only [anchor]
      rw [selected, stageAnchorVar_eq_selected_succ]
      exact Nat.ne_of_lt (Nat.lt_succ_self _)
  · exact True.intro

/-- The discovered and comparison transports produce the same observed output. -/
theorem same_observed_output {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (discoveredTransport run).map stage.sourceContinuation =
      (observedConstantTransport run).map stage.sourceContinuation :=
  rfl

/-- The comparison does not collapse into equality of total actions: on the
alternate continuation, the discovered map retains the changed anchor bit and
the constant map does not. -/
theorem different_total_action {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (discoveredTransport run).map (alternateContinuation run) ≠
      (observedConstantTransport run).map (alternateContinuation run) := by
  intro same
  have sameAt := congrArg
    (fun continuation => continuation.1 (stageAnchorVar (depth + 1))) same
  change
    Assignment.flipAt stage.discovery.var
        (Assignment.flipAt (stageAnchorVar (depth + 1))
          stage.sourceContinuation.1)
        (stageAnchorVar (depth + 1)) =
      Assignment.flipAt stage.discovery.var stage.sourceContinuation.1
        (stageAnchorVar (depth + 1)) at sameAt
  have anchorDifferent : stageAnchorVar (depth + 1) ≠ stage.discovery.var := by
    have selected := sequentialStage_selected_exact stage
    change stage.discovery.var = stageSelectedVar (depth + 1) at selected
    rw [selected, stageAnchorVar_eq_selected_succ]
    exact Nat.ne_of_gt (Nat.lt_succ_self _)
  rw [Assignment.flipAt_other _ _ _ anchorDifferent,
    Assignment.flipAt_selected,
    Assignment.flipAt_other _ _ _ anchorDifferent] at sameAt
  cases value : stage.sourceContinuation.1 (stageAnchorVar (depth + 1)) <;>
    rw [value] at sameAt <;> cases sameAt

/-- Both transports induce the same complete extensional view on the executed
system and its actually observed source continuation. The equality is a genuine
projection collision: the total transports remain distinct on another
continuation. -/
theorem same_extensional_view {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedTransportProjection run (discoveredTransport run) =
      executedTransportProjection run (observedConstantTransport run) :=
  rfl

/-- The extensional view produced by the authoritative execution is exactly the
projection of the discovered total transport at the executed observation and
with the executed numerical readout. -/
theorem executed_view_is_projection_of_discovered {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      executedTransportProjection run (discoveredTransport run) := by
  unfold executedStepToExtensionalView executedTransportProjection
    transportToExtensionalStabilityView
  congr 1
  exact stageApplication_eq_returnedRelationMap run

/-- The same extensional readout is obtained by projecting the authoritative
typed instruction.  Thus the readout is downstream of the instruction's total
action; it is not an alternative source for that action. -/
theorem executed_view_is_projection_of_authoritative_instruction {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      executedTransportProjection run
        ((authoritativeNormalizerInstruction run).toAcceptingTransport run) := by
  unfold executedStepToExtensionalView executedTransportProjection
    transportToExtensionalStabilityView
  congr 1
  exact Eq.trans
    (stageApplication_eq_returnedRelationMap run)
    (authoritativeNormalizerInstruction_transport_map_exact
      run stage.sourceContinuation).symm

/-- The authoritative instruction itself, rather than a separately named
transport, has the same projected view as the comparison transport. -/
theorem authoritative_instruction_same_extensional_view {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedTransportProjection run
        ((authoritativeNormalizerInstruction run).toAcceptingTransport run) =
      executedTransportProjection run (observedConstantTransport run) :=
  Eq.trans
    (executed_view_is_projection_of_authoritative_instruction run).symm
    (Eq.trans
      (executed_view_is_projection_of_discovered run)
      (same_extensional_view run))

/-- The total action denoted by the authoritative instruction remains distinct
from the comparison action on an admissible continuation hidden by the common
projection. -/
theorem authoritative_instruction_different_total_action {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ((authoritativeNormalizerInstruction run).toAcceptingTransport run).map
        (alternateContinuation run) ≠
      (observedConstantTransport run).map (alternateContinuation run) := by
  intro same
  exact different_total_action run
    (Eq.trans
      (authoritativeNormalizerInstruction_transport_map_exact
        run (alternateContinuation run)).symm
      same)

/-- The comparison transport agrees with the output recorded by the actual
executed projection at its observed source continuation. -/
theorem comparison_matches_executed_observation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (observedConstantTransport run).map
        (executedStepToExtensionalView run).observedSource =
      (executedStepToExtensionalView run).observedRetained :=
  (stageApplication_eq_returnedRelationMap run).symm

/-- The executed pair is a concrete collision for the generic
information-loss theorem: equal projected views carry different total actions. -/
def actionProjectionCollision {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ActionProjectionCollision
      (executedTransportProjection run)
      (executedTransportAction run) :=
  { first := discoveredTransport run
    second := observedConstantTransport run
    sameProjection := same_extensional_view run
    argument := alternateContinuation run
    differentAction := different_total_action run }

/-- Concrete projection collision whose first term is the total action stored
by the authoritative program instruction. -/
def authoritativeInstructionActionProjectionCollision {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    AnchoredActionProjectionCollision
      (executedTransportProjection run)
      (executedTransportAction run)
      ((authoritativeNormalizerInstruction run).toAcceptingTransport run) :=
  { second := observedConstantTransport run
    sameProjection := authoritative_instruction_same_extensional_view run
    argument := alternateContinuation run
    differentAction := authoritative_instruction_different_total_action run }

/-- Statement-level collision anchored at the authoritative program
instruction.  Unlike the unanchored non-factorization proposition, this public
statement records which total action the projection fails to determine. -/
theorem authoritative_instruction_projection_collision {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ∃ comparison argument,
      executedTransportProjection run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run) =
        executedTransportProjection run comparison ∧
      executedTransportAction run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run)
          argument ≠
        executedTransportAction run comparison argument :=
  let collision := authoritativeInstructionActionProjectionCollision run
  ⟨collision.second, collision.argument,
    collision.sameProjection, collision.differentAction⟩

/-- The determined state-and-width projection cannot reconstruct the total
action stored by the authoritative instruction. -/
theorem authoritative_instruction_action_not_factors_on_executed_system
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ActionFactorsThrough
      (executedTransportProjection run)
      (executedTransportAction run) :=
  action_not_factors_of_anchored_projection_collision
    (authoritativeInstructionActionProjectionCollision run)

/-- On the executed family itself, the total transport action does not factor
through the extensional state-and-quantity projection. The proof is an
instantiation of the generic projection-collision theorem, so the equality of
the two projected views is a formal premise of the non-factorization result. -/
theorem operational_action_not_factors_on_executed_system {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ActionFactorsThrough
      (executedTransportProjection run)
      (executedTransportAction run) :=
  action_not_factors_of_projection_collision
    (actionProjectionCollision run)

end ExecutedExtensionalSeparator

namespace ExtensionalSeparator

/-- Minimal system in which every Boolean continuation is admissible. -/
def system : SearchSystem :=
  { State := Bool
    Continuation := fun _ => Bool
    Accept := fun _ _ => True }

/-- Transport that preserves both Boolean continuations. -/
def preservingTransport :
    AcceptingContinuationTransport system false true :=
  { map := fun continuation => continuation
    preservesAccept := fun _ _ => True.intro }

/-- Transport with the same observed output at `false`, but a different total map. -/
def collapsingTransport :
    AcceptingContinuationTransport system false true :=
  { map := fun _ => false
    preservesAccept := fun _ _ => True.intro }

/-- Extensional projection used by the finite explanatory separator. -/
def projection :
    AcceptingContinuationTransport system false true →
      ExtensionalOperationalStabilityView system :=
  fun transport =>
    transportToExtensionalStabilityView transport false True.intro
      [1, 2, 1] singleStageWidthReadoutBound

/-- Total action carried by a finite-separator transport. -/
def action :
    AcceptingContinuationTransport system false true → Bool → Bool :=
  fun transport continuation => transport.map continuation

/-- Extensional projection of the identity-like total transport. -/
def preservingView : ExtensionalOperationalStabilityView system :=
  projection preservingTransport

/-- Extensional projection of the collapsing total transport. -/
def collapsingView : ExtensionalOperationalStabilityView system :=
  projection collapsingTransport

/-- Backward-compatible name for the shared observed view. -/
def commonView : ExtensionalOperationalStabilityView system :=
  preservingView

/-- Both transports produce the same output on the executed continuation. -/
theorem same_executed_output :
    preservingTransport.map preservingView.observedSource =
      collapsingTransport.map collapsingView.observedSource :=
  rfl

/-- Projecting the two distinct total transports yields the same complete
extensional stability view. -/
theorem same_extensional_stability_view : preservingView = collapsingView :=
  rfl

/-- Their actions differ on another admissible continuation. -/
theorem different_arbitrary_continuation_action :
    preservingTransport.map true ≠ collapsingTransport.map true := by
  intro impossible
  exact Bool.noConfusion impossible

/-- The finite separator packages the same information-loss pattern as the
executed family. -/
def actionProjectionCollision :
    ActionProjectionCollision projection action :=
  { first := preservingTransport
    second := collapsingTransport
    sameProjection := same_extensional_stability_view
    argument := true
    differentAction := different_arbitrary_continuation_action }

/--
No reconstruction from the extensional view can recover the total operational
action on all transports. The finite separator is an instance of the generic
projection-collision theorem.
-/
theorem operational_action_not_factors_through_extensional_view :
    ¬ ActionFactorsThrough projection action :=
  action_not_factors_of_projection_collision actionProjectionCollision

end ExtensionalSeparator

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalOperationalStabilityView
#print axioms ConstitutiveSearch.EndogenousDecomposition.singleStageWidthReadoutBound
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthReadoutBound
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStepToExtensionalView
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalView_observedOutput_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.extensionalView_widthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.transportToExtensionalStabilityView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.discoveredTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.observedConstantTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.executedTransportProjection
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.executedTransportAction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.alternateContinuation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.same_observed_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.different_total_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.authoritative_instruction_same_extensional_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.authoritative_instruction_different_total_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.same_extensional_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.executed_view_is_projection_of_discovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.executed_view_is_projection_of_authoritative_instruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.comparison_matches_executed_observation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.actionProjectionCollision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.authoritativeInstructionActionProjectionCollision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.authoritative_instruction_projection_collision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.authoritative_instruction_action_not_factors_on_executed_system
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedExtensionalSeparator.operational_action_not_factors_on_executed_system
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.system
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.preservingTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.collapsingTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.projection
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.preservingView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.collapsingView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.commonView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.same_executed_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.same_extensional_stability_view
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.different_arbitrary_continuation_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.actionProjectionCollision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExtensionalSeparator.operational_action_not_factors_through_extensional_view
/- AXIOM_AUDIT_END -/
