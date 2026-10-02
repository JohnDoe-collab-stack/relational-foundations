import RelationalPerimeter.Computation.ConstitutiveSearch.OperationalFrontierStatus
import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierNormalization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFullStep

/-!
# Executed operational reduction

This file connects the generic frontier absorption to the unique relation
returned by one threaded discovery.  The opening view contains no relation.
The reduction reads the relation from the executed stage and its complete
parent-to-child action is the existing full constitutive step.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- A constituted binary opening with no operational transport field. -/
structure ConstitutedOpeningView {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) where
  var : Var
  fresh : StructuralDecisionsAvoid var parent.context.decisions
  split : AcceptingExactBinarySplit
    (generatedStructuralBranchSystem root)
    parent
    (parent.child var false fresh)
    (parent.child var true fresh)

namespace ConstitutedOpeningView

/-- Left state of the opened frontier. -/
def left {root : Cnf} {parent : GeneratedStructuralBranchContext root}
    (opening : ConstitutedOpeningView parent) :
    GeneratedStructuralBranchContext root :=
  parent.child opening.var false opening.fresh

/-- Right state of the opened frontier. -/
def right {root : Cnf} {parent : GeneratedStructuralBranchContext root}
    (opening : ConstitutedOpeningView parent) :
    GeneratedStructuralBranchContext root :=
  parent.child opening.var true opening.fresh

end ConstitutedOpeningView

/-- Forget the discovered relation while retaining its constituted opening. -/
def EndogenousFlipDiscovery.openingView {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    ConstitutedOpeningView state :=
  { var := discovery.var
    fresh := discovery.fresh
    split := generatedStructuralSplit state discovery.var discovery.fresh }

/-- The relation-free opening actually consumed by the executed reduction. -/
def executedOpening {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    ConstitutedOpeningView (constructStage (depth + 1)).operationalRoot :=
  EndogenousFlipDiscovery.openingView stage.discovery

/-- Singleton frontier before the executed opening. -/
def executedEntryFrontier {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    List (GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)) :=
  [(constructStage (depth + 1)).operationalRoot]

/-- The two-position frontier produced by the relation-free opening. -/
def executedOpenedFrontier {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    List (GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)) :=
  [(executedOpening run).left, (executedOpening run).right]

/-- Operational status computed from the transport returned by the executed
discovery.  Replacing this `some` by `none` changes the position type from a
singleton retained frontier back to the unreduced two-position frontier. -/
def executedOperationalStatus {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    Option (AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      (executedOpening run).left (executedOpening run).right) :=
  some stage.discovery.relation.toAcceptingTransport

@[simp] theorem executedOperationalStatus_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedOperationalStatus run =
      some stage.discovery.relation.toAcceptingTransport :=
  rfl

/-- Before the executed discovery is incorporated, the same opening carries
both of its structurally distinct alternatives as operational positions. -/
@[simp] theorem executedPendingStatus_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stageOperationalWidth
        (system := generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        (left := (executedOpening run).left)
        (right := (executedOpening run).right)
        none = 2 :=
  rfl

/-- Incorporating the transport returned by the executed discovery changes the
position type for the same opening to the single retained alternative. -/
@[simp] theorem executedDiscoveredStatus_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stageOperationalWidth (executedOperationalStatus run) = 1 :=
  rfl

/-- The local operational-width reduction is induced by changing only the
status of the executed opening from no transport to its discovered transport. -/
theorem executedDiscovery_reduces_sameOpening_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stageOperationalWidth
        (system := generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        (left := (executedOpening run).left)
        (right := (executedOpening run).right)
        none = 2 ∧
      stageOperationalWidth (executedOperationalStatus run) = 1 :=
  ⟨executedPendingStatus_width run, executedDiscoveredStatus_width run⟩

/-- The exact sibling reduction licensed by the executed discovery. -/
def executedSiblingReduction {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    AcceptedIrreducibleFrontierReduction
      (system := generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      (generatedStructuralFlipAtSearch
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)
        stage.discovery.var)
      (executedOpenedFrontier _run) :=
  { retained := retainedFrontier (executedOperationalStatus _run)
    preservation := outcomePreservation (executedOperationalStatus _run)
    irreducible :=
      SearchIrreducible.singleton
        (generatedStructuralFlipAtSearch
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)
          stage.discovery.var)
        ((constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var true stage.discovery.fresh) }

/-- Parent-to-retained-child operation: exact opening followed by absorption. -/
def executedFullPreservation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      [(constructStage (depth + 1)).operationalRoot]
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh] :=
  (generatedStructuralExpansion
    (constructStage (depth + 1)).operationalRoot
    stage.discovery.var stage.discovery.fresh).trans
      (executedSiblingReduction run).preservation

/-- The opening view is definitionally relation-free. -/
theorem executedOpening_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    EndogenousFlipDiscovery.openingView stage.discovery =
      { var := stage.discovery.var
        fresh := stage.discovery.fresh
        split := generatedStructuralSplit
          (constructStage (depth + 1)).operationalRoot
          stage.discovery.var stage.discovery.fresh } :=
  rfl

/-- The chosen discovery is the one returned by the measured threaded run. -/
theorem executedTransformation_from_discoveryOutcome {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.discoveryRun.outcome.discovered? = some stage.discovery :=
  run.relationFromTransmittedState

@[simp] theorem executedSiblingReduction_retained {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedSiblingReduction run).retained =
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh] :=
  rfl

@[simp] theorem executedSiblingReduction_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (executedSiblingReduction run).width = 1 :=
  rfl

@[simp] theorem executedSiblingReduction_left_eq_discoveredMap {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.head continuation) =
      .head (stage.discovery.relation.mapContinuation continuation) :=
  rfl

@[simp] theorem executedSiblingReduction_right_eq_identity {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)) :
    (executedSiblingReduction run).preservation.forward.map
        (.tail (.head continuation)) =
      .head continuation :=
  rfl

theorem executedSiblingReduction_preservesAccept {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh))
    (accepted : GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh) continuation) :
    GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)
      (stage.discovery.relation.mapContinuation continuation) :=
  (executedSiblingReduction run).preservation.forward.preservesAccept
    (.head continuation) accepted

theorem executedFullPreservation_eq_discoveryFullStep {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedFullPreservation run =
      EndogenousFlipDiscovery.fullStepPreservation stage.discovery :=
  rfl

/--
The concrete application is the discovered schedule relation acting on the
actual source continuation.  This is the data-level link between the generic
left-case theorem above and the executed stage.
-/
theorem stageApplication_eq_returnedRelationMap {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    stage.application.output =
      stage.schedule.entry.relation.mapContinuation stage.sourceContinuation := by
  rw [stage.application.outputExact, executedDiscoverySchedule_code]
  rfl

/-- The absorbed source sibling remains positively viable. -/
theorem executedSourceSibling_viable {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
      stage.schedule.entry.source :=
  ⟨stage.sourceContinuation, stage.sourceAccepted⟩

/-- The retained target sibling is viable by the separately proved criterion. -/
theorem executedTargetSibling_viable {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)).Viable
      stage.schedule.entry.target :=
  ⟨stage.application.output, stage.outputAccepted⟩

/-- The complete executed output is the assignment stored in the next state. -/
theorem executedOutput_eq_nextOperationalAssignment {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.application.output.1 =
      run.nextRun.next.threadedAssignment.assignment :=
  (roleStage_output_constitutes_nextOperationalState run).1.symm

/-- Both sibling states remain structurally distinct. -/
theorem executedSiblingStates_distinct {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) :
    (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh ≠
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh := by
  intro same
  have decisionsSame := congrArg
    (fun context : GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex) => context.context.decisions)
    same
  have head :
      (⟨stage.discovery.var, false⟩ : StructuralBranchDecision) =
        ⟨stage.discovery.var, true⟩ :=
    List.head_eq_of_cons_eq decisionsSame
  exact Bool.noConfusion (congrArg StructuralBranchDecision.value head)

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOpeningView
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOpeningView.left
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOpeningView.right
#print axioms ConstitutiveSearch.EndogenousDecomposition.EndogenousFlipDiscovery.openingView
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedEntryFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOpenedFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalStatus
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalStatus_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedPendingStatus_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedDiscoveredStatus_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedDiscovery_reduces_sameOpening_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedFullPreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOpening_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTransformation_from_discoveryOutcome
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction_retained
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction_left_eq_discoveredMap
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction_right_eq_identity
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingReduction_preservesAccept
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedFullPreservation_eq_discoveryFullStep
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageApplication_eq_returnedRelationMap
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSourceSibling_viable
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTargetSibling_viable
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOutput_eq_nextOperationalAssignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedSiblingStates_distinct
/- AXIOM_AUDIT_END -/
