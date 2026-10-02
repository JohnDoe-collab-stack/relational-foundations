import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProduction

/-!
# Executed reduction indexed by role, action, and preservation

The reduction certificate cannot be built from a width or a singleton alone.
At every role it is indexed by the authoritative atom and records that the
atom's transformed interpretation reaches the completed output, that the
separate preservation theorem accepts that result, that the retained output is
accepted, and that the two source occurrences remain distinct.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive

/--
Stagewise decomposition of a causal execution.  The tail is indexed by the
exact state produced by the head, while the head decomposition is already
typed using the head stage alone.
-/
inductive StagewiseExecutedDecompositionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      StagewiseExecutedDecompositionHistory
        (CausalConstitutiveExecutionHistory.nil state)
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      (headDecomposition : ExecutedStageDecomposition head)
      (tailDecomposition : StagewiseExecutedDecompositionHistory tail) :
      StagewiseExecutedDecompositionHistory
        (CausalConstitutiveExecutionHistory.step head tail)

/-- Build each local decomposition at the corresponding causal prefix. -/
def buildStagewiseExecutedDecompositionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) →
      StagewiseExecutedDecompositionHistory run
  | _, _, .nil _ => .nil
  | _, _, .step head tail =>
      .step (executedStageDecomposition head)
        (buildStagewiseExecutedDecompositionHistory tail)

/-- The role history is read directly from the stagewise decomposition. -/
def StagewiseExecutedDecompositionHistory.roles :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      StagewiseExecutedDecompositionHistory run →
      RelationalConstitutiveRoleHistory run
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step headDecomposition.role tailDecomposition.roles

/-- The canonical stagewise roles are definitionally the canonical role readout. -/
theorem buildStagewiseExecutedDecompositionHistory_roles_exact
    {count : Nat} {state : CausalConstitutiveState}
    (run : CausalConstitutiveExecutionHistory count state) :
    (buildStagewiseExecutedDecompositionHistory run).roles =
      buildRelationalConstitutiveRoleHistory run := by
  induction run with
  | nil => rfl
  | step head tail inductionHypothesis =>
      change
        RelationalConstitutiveRoleHistory.step
            (relationalConstitutiveRoleStage head)
            (buildStagewiseExecutedDecompositionHistory tail).roles =
          RelationalConstitutiveRoleHistory.step
            (relationalConstitutiveRoleStage head)
            (buildRelationalConstitutiveRoleHistory tail)
      exact congrArg
        (RelationalConstitutiveRoleHistory.step
          (relationalConstitutiveRoleStage head))
        inductionHypothesis

/-- Every stagewise role is exactly the role constituted by its executed stage. -/
theorem StagewiseExecutedDecompositionHistory.rolesConstitutionExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (history : StagewiseExecutedDecompositionHistory run) →
      RelationalRoleHistoryConstitutionExact history.roles
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step
        (by
          rw [headDecomposition.roleExact]
          exact relationalConstitutiveRoleStage_exact _)
        tailDecomposition.rolesConstitutionExact

/-- A positive profile selecting the transformed occurrence at the first role. -/
def RelationalConstitutiveRoleHistory.headTransformedProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles
  | _, _, _, .nil => ()
  | _, _, _, .step headRole tailRoles =>
      (roleConstitutedOccurrenceAt headRole .left,
        defaultRoleOccurrenceProfile tailRoles)

/-- A positive profile selecting the retained occurrence at the first role. -/
def RelationalConstitutiveRoleHistory.headRetainedProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles
  | _, _, _, .nil => ()
  | _, _, _, .step headRole tailRoles =>
      (roleConstitutedOccurrenceAt headRole .right,
        defaultRoleOccurrenceProfile tailRoles)

/-- The two profiles remain distinct before any operational grouping. -/
theorem RelationalConstitutiveRoleHistory.headProfilesDistinct
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (positive : 0 < count) :
    roles.headTransformedProfile ≠ roles.headRetainedProfile := by
  cases roles with
  | nil => exact False.elim (Nat.not_lt_zero 0 positive)
  | step headRole tailRoles =>
      intro same
      exact openingRolePosition_left_ne_right headRole
        (congrArg
          (fun occurrence : RoleConstitutedOccurrence headRole =>
            occurrence.position)
          (congrArg Prod.fst same))

/-- Dependent reduction history for exactly the atoms of one role program. -/
inductive ExecutedRoleReductionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (program : RoleIndexedProgram roles) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedRoleReductionHistory
        (RoleIndexedProgram.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      (license : ExecutedRoleReductionLicense headRole atom)
      (tailReduction : ExecutedRoleReductionHistory tailProgram) :
      ExecutedRoleReductionHistory
        (RoleIndexedProgram.step atom tailProgram)

/-- Canonical reduction history, structurally tied to the compiled program. -/
def buildExecutedRoleReductionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      ExecutedRoleReductionHistory (compileRoleHistory roles)
  | _, _, _, .nil => .nil
  | _, _, _, .step headRole tailRoles =>
      .step (executedRoleReductionLicense headRole)
        (buildExecutedRoleReductionHistory tailRoles)

/-- The reduction history is read from the same stagewise decomposition. -/
def StagewiseExecutedDecompositionHistory.reduction :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (history : StagewiseExecutedDecompositionHistory run) →
      ExecutedRoleReductionHistory (compileRoleHistory history.roles)
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step headDecomposition.license tailDecomposition.reduction

/-- The canonical stagewise reduction agrees with the role-indexed builder. -/
theorem buildStagewiseExecutedDecompositionHistory_reduction_exact
    {count : Nat} {state : CausalConstitutiveState}
    (run : CausalConstitutiveExecutionHistory count state) :
    (buildStagewiseExecutedDecompositionHistory run).reduction =
      buildExecutedRoleReductionHistory
        (buildStagewiseExecutedDecompositionHistory run).roles := by
  induction run with
  | nil => rfl
  | step head tail inductionHypothesis =>
      change
        ExecutedRoleReductionHistory.step
            (executedRoleReductionLicense
              (relationalConstitutiveRoleStage head))
            (buildStagewiseExecutedDecompositionHistory tail).reduction =
          ExecutedRoleReductionHistory.step
            (executedRoleReductionLicense
              (relationalConstitutiveRoleStage head))
            (buildExecutedRoleReductionHistory
              (buildStagewiseExecutedDecompositionHistory tail).roles)
      exact congrArg
        (ExecutedRoleReductionHistory.step
          (executedRoleReductionLicense
            (relationalConstitutiveRoleStage head)))
        inductionHypothesis

/--
Positive witness that the transformed occurrence is absorbed into the retained
operational target.  Its constructor is private: the target is licensed only by
the executed action together with its universal preservation map, positive
acceptance, non-identity and occurrence distinction.
-/
structure CriterionPreservingAbsorption
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) : Type where
  private mk ::
  outputExact :
    interpretRoleStageAtom atom
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput) =
      role.completedOutput
  accepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (interpretRoleStageAtom atom
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput))
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation)
  changesSource :
    (atom.action role.executedInput).1 ≠ role.executedInput.1
  sourceTargetDistinct :
    license.transformedOccurrence ≠ license.retainedOccurrence

/-- The canonical absorption is constituted from the complete executed license. -/
def criterionPreservingAbsorption
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    CriterionPreservingAbsorption license :=
  { outputExact := license.transformedOutputExact
    accepted := license.transformedAccepted
    preservesCriterion := license.preservesCriterion
    changesSource := license.actionChangesSource
    sourceTargetDistinct := license.occurrencesRemainDistinct }

/--
A produced action target is an execution constructor, not a stored value
accompanied by an equality. Its value is obtained only by interpretation below.
-/
inductive ActionProducedOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) : Type where
  | execute : ActionProducedOperationalTarget absorption

/-- Eliminate the execution constructor by applying the actual role action. -/
def ActionProducedOperationalTarget.value
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    {absorption : CriterionPreservingAbsorption license} :
    ActionProducedOperationalTarget absorption →
      GeneratedStructuralBranchContinuation
        (causalOpeningRight source run.selected run.fresh)
  | .execute => interpretRoleStageAtom atom
      license.transformedOccurrence license.transformedConstitution
      (license.transformedOccurrenceExact ▸ role.executedInput)

/-- The action equation follows from execution, rather than being a field. -/
theorem ActionProducedOperationalTarget.valueExact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    {absorption : CriterionPreservingAbsorption license}
    (produced : ActionProducedOperationalTarget absorption) :
    produced.value = interpretRoleStageAtom atom
      license.transformedOccurrence license.transformedConstitution
      (license.transformedOccurrenceExact ▸ role.executedInput) := by
  cases produced
  rfl

/-- The canonical action step does not accept a caller-supplied target. -/
def actionProducedOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    ActionProducedOperationalTarget absorption :=
  .execute

/--
The operational target carrier at one role is the full continuation space in
the codomain of the executed relation.  It is deliberately not restricted to
the completed output: convergence must be proved from execution rather than
built into the target type.
-/
abbrev ExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (_license : ExecutedRoleReductionLicense role atom) : Type :=
  GeneratedStructuralBranchContinuation
    (causalOpeningRight source run.selected run.fresh)

/-- The target positively produced by applying the executed relation. -/
def transformedExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    ExecutedRoleOperationalTarget license :=
  (actionProducedOperationalTarget absorption).value

/-- The transformed target exposes the executed action result definitionally. -/
theorem transformedExecutedRoleOperationalTarget_is_executed_action
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    transformedExecutedRoleOperationalTarget absorption =
      interpretRoleStageAtom atom
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput) :=
  (actionProducedOperationalTarget absorption).valueExact

/-- The already completed right-hand continuation as an operational target. -/
def retainedExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    ExecutedRoleOperationalTarget license :=
  role.completedOutput

/-- The executed action, rather than the target carrier, proves convergence. -/
theorem transformedExecutedRoleOperationalTarget_eq_retained
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    transformedExecutedRoleOperationalTarget absorption =
      retainedExecutedRoleOperationalTarget license :=
  absorption.outputExact

/--
One local operational decision, indexed by its constituted source and by the
target it actually produces.  The transformed constructor consumes the complete
preserving absorption witness.  The retained constructor consumes positive
viability.  Neither constructor identifies the source occurrences.
-/
inductive ExecutedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    RoleConstitutedOccurrence role →
      ExecutedRoleOperationalTarget license → Type 2 where
  | transformed
      (absorption : CriterionPreservingAbsorption license)
      (produced : ActionProducedOperationalTarget absorption) :
      ExecutedRoleOccurrenceDecision license
        license.transformedOccurrence
        produced.value
  | retained
      (accepted :
        GeneratedStructuralBranchAccept
          (causalOpeningRight source run.selected run.fresh)
          role.completedOutput) :
      ExecutedRoleOccurrenceDecision license
        license.retainedOccurrence
        (retainedExecutedRoleOperationalTarget license)

/-- The target index carried by the decision. -/
def ExecutedRoleOccurrenceDecision.target
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    {occurrence : RoleConstitutedOccurrence role}
    {target : ExecutedRoleOperationalTarget license}
    (_decision : ExecutedRoleOccurrenceDecision license occurrence target) :
    ExecutedRoleOperationalTarget license :=
  target

/--
The canonical transformed decision. Its target is obtained only by projecting
the action-produced object that consumes the preserving absorption.
-/
def executedTransformedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    ExecutedRoleOccurrenceDecision license license.transformedOccurrence
      (transformedExecutedRoleOperationalTarget
        (criterionPreservingAbsorption license)) :=
  let absorption := criterionPreservingAbsorption license
  .transformed absorption (actionProducedOperationalTarget absorption)

/-- The canonical transformed decision definitionally exposes the action result. -/
theorem executedTransformedRoleOccurrenceDecision_target_is_action
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    (executedTransformedRoleOccurrenceDecision license).target =
      interpretRoleStageAtom atom
        license.transformedOccurrence
        license.transformedConstitution
        (license.transformedOccurrenceExact ▸ role.executedInput) :=
  rfl

/--
Complete local witness consumed by the next stratum. It ties the canonical
decision simultaneously to the executed action, arbitrary-continuation
preservation, positive viability and source-occurrence distinction.
-/
structure ExecutedTransformedDecisionWitness
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) : Type 2 where
  private mk ::
  absorption : CriterionPreservingAbsorption license
  produced : ActionProducedOperationalTarget absorption
  decision :
    ExecutedRoleOccurrenceDecision license license.transformedOccurrence
      produced.value
  decisionExact : decision =
    ExecutedRoleOccurrenceDecision.transformed absorption produced
  transformedConstitution :
    RoleConstitutionEvidence role license.transformedOccurrence
  retainedConstitution :
    RoleConstitutionEvidence role license.retainedOccurrence
  targetFromAction :
    produced.value = interpretRoleStageAtom atom
      license.transformedOccurrence
      license.transformedConstitution
      (license.transformedOccurrenceExact ▸ role.executedInput)
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation)
  transformedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh) produced.value
  retainedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      role.completedOutput
  occurrencesDistinct :
    license.transformedOccurrence ≠ license.retainedOccurrence

/-- Build the complete local witness from the one authoritative license. -/
def executedTransformedDecisionWitness
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    ExecutedTransformedDecisionWitness license :=
  let absorption := criterionPreservingAbsorption license
  let produced := actionProducedOperationalTarget absorption
  { absorption := absorption
    produced := produced
    decision := ExecutedRoleOccurrenceDecision.transformed absorption produced
    decisionExact := rfl
    transformedConstitution := license.transformedConstitution
    retainedConstitution := license.retainedConstitution
    targetFromAction := rfl
    preservesCriterion := license.preservesCriterion
    transformedAccepted := license.transformedAccepted
    retainedAccepted := license.retainedAccepted
    occurrencesDistinct := license.occurrencesRemainDistinct }

/-- Decide the operational case by inspecting the constituted occurrence. -/
def executedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (occurrence : RoleConstitutedOccurrence role) :
    Sigma fun target : ExecutedRoleOperationalTarget license =>
      ExecutedRoleOccurrenceDecision license occurrence target := by
  cases positionExact : occurrence.position with
  | left =>
      have occurrenceExact : license.transformedOccurrence = occurrence :=
        Eq.trans license.transformedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip occurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← occurrenceExact]
      let witness := executedTransformedDecisionWitness license
      exact ⟨witness.produced.value, witness.decision⟩
  | right =>
      have occurrenceExact : license.retainedOccurrence = occurrence :=
        Eq.trans license.retainedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip occurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← occurrenceExact]
      exact ⟨retainedExecutedRoleOperationalTarget license,
        ExecutedRoleOccurrenceDecision.retained
          (executedTransformedDecisionWitness license).retainedAccepted⟩

/--
Decide one occurrence by consuming the complete causal witness of this role.
The transformed case reuses the exact action-produced decision stored in that
witness; it is not reconstructed from the retained target.
-/
def executedRoleOccurrenceDecisionFromWitness
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (witness : ExecutedTransformedDecisionWitness license)
    (occurrence : RoleConstitutedOccurrence role) :
    Sigma fun target : ExecutedRoleOperationalTarget license =>
      ExecutedRoleOccurrenceDecision license occurrence target := by
  cases positionExact : occurrence.position with
  | left =>
      have occurrenceExact : license.transformedOccurrence = occurrence :=
        Eq.trans license.transformedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip occurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← occurrenceExact]
      exact ⟨witness.produced.value, witness.decision⟩
  | right =>
      have occurrenceExact : license.retainedOccurrence = occurrence :=
        Eq.trans license.retainedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip occurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← occurrenceExact]
      exact ⟨retainedExecutedRoleOperationalTarget license,
        ExecutedRoleOccurrenceDecision.retained witness.retainedAccepted⟩

/-- Every local target is obtained by eliminating the produced decision. -/
theorem ExecutedRoleOccurrenceDecision.target_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    {sourceOccurrence : RoleConstitutedOccurrence role}
    {target : ExecutedRoleOperationalTarget license}
    (decision : ExecutedRoleOccurrenceDecision
      license sourceOccurrence target) :
    target = retainedExecutedRoleOperationalTarget license := by
  cases decision with
  | transformed absorption produced =>
      exact Eq.trans produced.valueExact absorption.outputExact
  | retained => rfl

/-- The preserving absorption used to form a transformed decision retains the
separate preservation map. -/
theorem criterionPreservingAbsorption_preservesCriterion
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation) :=
  absorption.preservesCriterion

/--
End-to-end causal witness for a whole executed reduction. Every head consumes
the exact role license through its action-producing transformed decision before
the dependent tail is considered.
-/
inductive ExecutedReductionConstitutiveChain :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedReductionConstitutiveChain
        (ExecutedRoleReductionHistory.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      (headWitness : ExecutedTransformedDecisionWitness license)
      (tailWitness : ExecutedReductionConstitutiveChain tailReduction) :
      ExecutedReductionConstitutiveChain
        (ExecutedRoleReductionHistory.step license tailReduction)

/-- The constitutive chain is built only by consuming each executed license. -/
def executedReductionConstitutiveChain :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      ExecutedReductionConstitutiveChain reduction
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .step license tailReduction =>
      .step (executedTransformedDecisionWitness license)
        (executedReductionConstitutiveChain tailReduction)

/--
The public causal content of a complete reduction chain.  At every role the
target is the output of the executed action, the independent preservation map
is still present, the produced target is accepted, and the source occurrences
remain distinct.  The predicate follows the dependent tail constituted by the
state produced at the preceding role.
-/
inductive ExecutedReductionCausalExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      ExecutedReductionConstitutiveChain reduction → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedReductionCausalExact
        (ExecutedReductionConstitutiveChain.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headWitness : ExecutedTransformedDecisionWitness license}
      {tailWitness : ExecutedReductionConstitutiveChain tailReduction}
      (targetFromAction :
        headWitness.decision.target = interpretRoleStageAtom atom
          license.transformedOccurrence
          license.transformedConstitution
          (license.transformedOccurrenceExact ▸ headRole.executedInput))
      (transformedConstitution :
        RoleConstitutionEvidence headRole license.transformedOccurrence)
      (retainedConstitution :
        RoleConstitutionEvidence headRole license.retainedOccurrence)
      (preservesCriterion :
        (continuation : GeneratedStructuralBranchContinuation
          (causalOpeningLeft state head.selected head.fresh)) →
        GeneratedStructuralBranchAccept
            (causalOpeningLeft state head.selected head.fresh) continuation →
          GeneratedStructuralBranchAccept
            (causalOpeningRight state head.selected head.fresh)
            (atom.action continuation))
      (producedTargetAccepted :
        GeneratedStructuralBranchAccept
          (causalOpeningRight state head.selected head.fresh)
          headWitness.decision.target)
      (occurrencesDistinct :
        license.transformedOccurrence ≠ license.retainedOccurrence)
      (tailExact : ExecutedReductionCausalExact tailWitness) :
      ExecutedReductionCausalExact
        (ExecutedReductionConstitutiveChain.step headWitness tailWitness)

/-- Every constitutive chain exposes its action and preservation data in order. -/
def ExecutedReductionConstitutiveChain.causalExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      (chain : ExecutedReductionConstitutiveChain reduction) →
      ExecutedReductionCausalExact chain
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .step headWitness tailWitness =>
      .step headWitness.targetFromAction
        headWitness.transformedConstitution headWitness.retainedConstitution
        headWitness.preservesCriterion
        headWitness.transformedAccepted headWitness.occurrencesDistinct
        tailWitness.causalExact

/--
The relational constitution consumed by an executed reduction.  Each step
retains the formation and provenance witnesses of both constituted sources in
the same dependent order as the executed roles.
-/
inductive ExecutedReductionRelationalConstitutionExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      ExecutedReductionConstitutiveChain reduction → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedReductionRelationalConstitutionExact
        (ExecutedReductionConstitutiveChain.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headWitness : ExecutedTransformedDecisionWitness license}
      {tailWitness : ExecutedReductionConstitutiveChain tailReduction}
      (transformedConstitution :
        RoleConstitutionEvidence headRole license.transformedOccurrence)
      (retainedConstitution :
        RoleConstitutionEvidence headRole license.retainedOccurrence)
      (tailConstitution :
        ExecutedReductionRelationalConstitutionExact tailWitness) :
      ExecutedReductionRelationalConstitutionExact
        (ExecutedReductionConstitutiveChain.step headWitness tailWitness)

/--
The preservation content of an executed reduction, exposed independently of
the other causal fields.  Each constructor carries the universal map on
continuations at the corresponding constituted role.
-/
inductive ExecutedReductionPreservationExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      ExecutedReductionConstitutiveChain reduction → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedReductionPreservationExact
        (ExecutedReductionConstitutiveChain.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headWitness : ExecutedTransformedDecisionWitness license}
      {tailWitness : ExecutedReductionConstitutiveChain tailReduction}
      (headPreservation :
        (continuation : GeneratedStructuralBranchContinuation
          (causalOpeningLeft state head.selected head.fresh)) →
        GeneratedStructuralBranchAccept
            (causalOpeningLeft state head.selected head.fresh) continuation →
          GeneratedStructuralBranchAccept
            (causalOpeningRight state head.selected head.fresh)
            (atom.action continuation))
      (tailPreservation : ExecutedReductionPreservationExact tailWitness) :
      ExecutedReductionPreservationExact
        (ExecutedReductionConstitutiveChain.step headWitness tailWitness)

/--
The occurrence-separation content of an executed reduction.  It records at
every role that operational grouping does not identify the two constituted
source occurrences.
-/
inductive ExecutedReductionOccurrenceSeparationExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      ExecutedReductionConstitutiveChain reduction → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedReductionOccurrenceSeparationExact
        (ExecutedReductionConstitutiveChain.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headWitness : ExecutedTransformedDecisionWitness license}
      {tailWitness : ExecutedReductionConstitutiveChain tailReduction}
      (headSeparation :
        license.transformedOccurrence ≠ license.retainedOccurrence)
      (tailSeparation :
        ExecutedReductionOccurrenceSeparationExact tailWitness) :
      ExecutedReductionOccurrenceSeparationExact
        (ExecutedReductionConstitutiveChain.step headWitness tailWitness)

/-- Project the universal-preservation chain from the complete causal chain. -/
def ExecutedReductionCausalExact.preservationExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {chain : ExecutedReductionConstitutiveChain reduction} →
      ExecutedReductionCausalExact chain →
        ExecutedReductionPreservationExact chain
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .step _ _ _ preservation _ _ tailExact =>
      .step preservation tailExact.preservationExact

/-- Project occurrence separation from the complete causal chain. -/
def ExecutedReductionCausalExact.occurrenceSeparationExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {chain : ExecutedReductionConstitutiveChain reduction} →
      ExecutedReductionCausalExact chain →
        ExecutedReductionOccurrenceSeparationExact chain
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .step _ _ _ _ _ separation tailExact =>
      .step separation tailExact.occurrenceSeparationExact

/-- Project the primitive relational constitution from the exact causal chain. -/
def ExecutedReductionCausalExact.relationalConstitutionExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {chain : ExecutedReductionConstitutiveChain reduction} →
      ExecutedReductionCausalExact chain →
        ExecutedReductionRelationalConstitutionExact chain
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .step _ transformed retained _ _ _ tailExact =>
      .step transformed retained tailExact.relationalConstitutionExact

/-- The profile retained by every license of one reduction history. -/
def retainedRoleProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      ExecutedRoleReductionHistory program → RoleOccurrenceProfile roles
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, .step license tailReduction =>
      (license.retainedOccurrence, retainedRoleProfile tailReduction)

/--
Dependent carrier of outputs produced by the executed reduction.  Unlike the
source occurrence profile, every head component contains the continuation
actually produced in the codomain of that stage relation.
-/
def ExecutedOperationalTargetProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      ExecutedRoleReductionHistory program → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, .step license tailReduction =>
      ExecutedRoleOperationalTarget license ×
        ExecutedOperationalTargetProfile tailReduction

/-- The completed output profile against which produced outputs are compared. -/
def retainedExecutedOperationalTargetProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      ExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, .step license tailReduction =>
      (retainedExecutedRoleOperationalTarget license,
        retainedExecutedOperationalTargetProfile tailReduction)

/--
Proof-relevant global reduction from one constituted source profile to one
target profile.  Its head decision consumes the corresponding local license and
its tail follows the exact dependent reduction history.
-/
inductive ExecutedRoleProfileReduction :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      RoleOccurrenceProfile roles →
        ExecutedOperationalTargetProfile reduction → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedRoleProfileReduction
        (ExecutedRoleReductionHistory.nil (state := state)) () ()
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headSource : RoleConstitutedOccurrence headRole}
      {headTarget : ExecutedRoleOperationalTarget license}
      {tailSource : RoleOccurrenceProfile tailRoles}
      {tailTarget : ExecutedOperationalTargetProfile tailReduction}
      (headDecision :
        ExecutedRoleOccurrenceDecision license headSource headTarget)
      (headPreservation :
        (continuation : GeneratedStructuralBranchContinuation
          (causalOpeningLeft state head.selected head.fresh)) →
        GeneratedStructuralBranchAccept
            (causalOpeningLeft state head.selected head.fresh) continuation →
          GeneratedStructuralBranchAccept
            (causalOpeningRight state head.selected head.fresh)
            (atom.action continuation))
      (headSeparation :
        license.transformedOccurrence ≠ license.retainedOccurrence)
      (tailTrace :
        ExecutedRoleProfileReduction tailReduction tailSource tailTarget) :
      ExecutedRoleProfileReduction
        (ExecutedRoleReductionHistory.step license tailReduction)
        (headSource, tailSource)
        (headTarget, tailTarget)

/--
Proof-relevant normalization of one constituted occurrence.  Its constructors
are the two executed decisions themselves: no target value or equality proof
can be supplied independently.
-/
inductive ExecutedHeadNormalization
    {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {headRole : RelationalConstitutiveRoleStage head}
    {atom : RoleStageAtom headRole}
    {license : ExecutedRoleReductionLicense headRole atom}
    (headWitness : ExecutedTransformedDecisionWitness license) :
    RoleConstitutedOccurrence headRole → Type where
  | transformed :
      ExecutedHeadNormalization headWitness license.transformedOccurrence
  | retained :
      ExecutedHeadNormalization headWitness license.retainedOccurrence

/-- The local target is computed by eliminating the executed decision. -/
def ExecutedHeadNormalization.target
    {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {headRole : RelationalConstitutiveRoleStage head}
    {atom : RoleStageAtom headRole}
    {license : ExecutedRoleReductionLicense headRole atom}
    {headWitness : ExecutedTransformedDecisionWitness license}
    {sourceOccurrence : RoleConstitutedOccurrence headRole}
    (result : ExecutedHeadNormalization headWitness sourceOccurrence) :
    ExecutedRoleOperationalTarget license :=
  match result with
  | .transformed => headWitness.produced.value
  | .retained => retainedExecutedRoleOperationalTarget license

/-- Recover the exact decision whose elimination produced the local target. -/
def ExecutedHeadNormalization.decision
    {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {headRole : RelationalConstitutiveRoleStage head}
    {atom : RoleStageAtom headRole}
    {license : ExecutedRoleReductionLicense headRole atom}
    {headWitness : ExecutedTransformedDecisionWitness license}
    {sourceOccurrence : RoleConstitutedOccurrence headRole}
    (result : ExecutedHeadNormalization headWitness sourceOccurrence) :
    ExecutedRoleOccurrenceDecision license sourceOccurrence result.target :=
  match result with
  | .transformed => headWitness.decision
  | .retained => .retained headWitness.retainedAccepted

/-- Select the corresponding decision constructor from a constituted source. -/
def normalizeExecutedHead
    {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {headRole : RelationalConstitutiveRoleStage head}
    {atom : RoleStageAtom headRole}
    {license : ExecutedRoleReductionLicense headRole atom}
    (headWitness : ExecutedTransformedDecisionWitness license)
    (sourceOccurrence : RoleConstitutedOccurrence headRole) :
    ExecutedHeadNormalization headWitness sourceOccurrence := by
  cases positionExact : sourceOccurrence.position with
  | left =>
      have sourceExact : license.transformedOccurrence = sourceOccurrence :=
        Eq.trans license.transformedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip sourceOccurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← sourceExact]
      exact .transformed
  | right =>
      have sourceExact : license.retainedOccurrence = sourceOccurrence :=
        Eq.trans license.retainedOccurrenceExact (by
          have canonical := roleConstitutedOccurrence_roundTrip sourceOccurrence
          rw [positionExact] at canonical
          exact canonical)
      rw [← sourceExact]
      exact .retained

def ExecutedChainNormalization :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      (chain : ExecutedReductionConstitutiveChain reduction) →
      RoleOccurrenceProfile roles → Type 2
  | _, _, _, _, _, _, .nil, _ => ULift.{2, 0} Unit
  | _, _, _, _, _, _, .step headWitness tailWitness, profile =>
      ExecutedHeadNormalization headWitness profile.1 ×
        ExecutedChainNormalization tailWitness profile.2

/-- The target is determined structurally by the executed decisions. -/
def ExecutedChainNormalization.target
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {chain : ExecutedReductionConstitutiveChain reduction}
    {profile : RoleOccurrenceProfile roles}
    (result : ExecutedChainNormalization chain profile) :
    ExecutedOperationalTargetProfile reduction := by
  cases chain with
  | nil => exact ()
  | step headWitness tailWitness =>
      exact (result.1.target,
        ExecutedChainNormalization.target result.2)

/-- The trace is reconstructed from the same decisions, preservation and separation. -/
def ExecutedChainNormalization.trace
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {chain : ExecutedReductionConstitutiveChain reduction}
    {profile : RoleOccurrenceProfile roles}
    (result : ExecutedChainNormalization chain profile) :
    ExecutedRoleProfileReduction reduction profile result.target := by
  cases chain with
  | nil => exact .nil
  | step headWitness tailWitness =>
      exact .step result.1.decision headWitness.preservesCriterion
        headWitness.occurrencesDistinct
        (ExecutedChainNormalization.trace result.2)

/--
Normalize only by structural recursion on the constitutive chain itself. Each
head decision is produced before the recursively normalized tail.
-/
def normalizeExecutedRoleProfileFromChain :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      (chain : ExecutedReductionConstitutiveChain reduction) →
      (profile : RoleOccurrenceProfile roles) →
      ExecutedChainNormalization chain profile
  | _, state, _, _, _, _, .nil, profile => by
      cases profile
      exact ULift.up ()
  | _, _, _, _, _, _, .step headWitness tailWitness, profile =>
      (normalizeExecutedHead headWitness profile.1,
        normalizeExecutedRoleProfileFromChain tailWitness profile.2)

/-- Every trace target equals the completed profile through executed outputs. -/
theorem executedRoleProfileReduction_target_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {sourceProfile : RoleOccurrenceProfile roles} →
      {targetProfile : ExecutedOperationalTargetProfile reduction} →
      (trace :
        ExecutedRoleProfileReduction reduction sourceProfile targetProfile) →
      targetProfile = retainedExecutedOperationalTargetProfile reduction := by
  intro count state run roles program reduction sourceProfile targetProfile trace
  induction trace with
  | nil => rfl
  | step headDecision _ _ tailTrace tailExact =>
      cases headDecision with
      | transformed absorption produced =>
          exact Prod.ext
            (Eq.trans produced.valueExact absorption.outputExact)
            tailExact
      | retained =>
          exact congrArg (fun tail => (_, tail)) tailExact

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory_roles_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.rolesConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headTransformedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headRetainedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headProfilesDistinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.reduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory_reduction_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CriterionPreservingAbsorption
#print axioms ConstitutiveSearch.EndogenousDecomposition.criterionPreservingAbsorption
#print axioms ConstitutiveSearch.EndogenousDecomposition.ActionProducedOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.ActionProducedOperationalTarget.value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ActionProducedOperationalTarget.valueExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.actionProducedOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget_is_executed_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget_eq_retained
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTransformedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTransformedRoleOccurrenceDecision_target_is_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedTransformedDecisionWitness
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTransformedDecisionWitness
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleOccurrenceDecisionFromWitness
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.criterionPreservingAbsorption_preservesCriterion
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionConstitutiveChain
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionConstitutiveChain
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCausalExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionConstitutiveChain.causalExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionRelationalConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionPreservationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionOccurrenceSeparationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCausalExact.relationalConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCausalExact.preservationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCausalExact.occurrenceSeparationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalTargetProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedExecutedOperationalTargetProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleProfileReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedHeadNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedHeadNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedHeadNormalization.decision
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedChainNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedChainNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedChainNormalization.trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedRoleProfileFromChain
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleProfileReduction_target_exact
/- AXIOM_AUDIT_END -/
