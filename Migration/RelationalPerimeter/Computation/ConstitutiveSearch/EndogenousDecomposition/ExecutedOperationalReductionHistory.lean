import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReduction
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerCore

/-!
# Causally threaded operational reductions

The tail of this history is indexed by the exact next state produced by its
head.  Structural profiles keep both positions of every opening.  Operational
profiles use the positions of the frontier actually retained by the executed
reduction.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Minimal proof-only certificate for the reduction computed from one executed
run. Viability and sibling distinction remain separate positive theorems; they
are not prerequisites of the reduction certificate itself. -/
structure ExecutedOperationalReductionEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Type where
  private mk ::
  outcomeExact :
    run.discoveryRun.outcome.discovered? = some stage.discovery
  retainedExact :
    (executedSiblingReduction run).retained =
      [(constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh]
  leftActionExact :
    ∀ continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh),
      (executedSiblingReduction run).preservation.forward.map
          (.head continuation) =
        .head (stage.discovery.relation.mapContinuation continuation)
  rightActionExact :
    ∀ continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh),
      (executedSiblingReduction run).preservation.forward.map
          (.tail (.head continuation)) = .head continuation
  criterionPreserved :
    ∀ (continuation : GeneratedStructuralBranchContinuation
        ((constructStage (depth + 1)).operationalRoot.child
          stage.discovery.var false stage.discovery.fresh)),
      GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh) continuation →
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh)
          (stage.discovery.relation.mapContinuation continuation)
  applicationUsesReturnedRelation :
    stage.application.output =
      stage.schedule.entry.relation.mapContinuation stage.sourceContinuation
  outputConstitutesNext :
    stage.application.output.1 =
      run.nextRun.next.threadedAssignment.assignment

/-- Construct the certificate solely from the executed run. -/
def executedOperationalReductionEvidence {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ExecutedOperationalReductionEvidence run :=
  { outcomeExact := executedTransformation_from_discoveryOutcome run
    retainedExact := executedSiblingReduction_retained run
    leftActionExact := executedSiblingReduction_left_eq_discoveredMap run
    rightActionExact := executedSiblingReduction_right_eq_identity run
    criterionPreserved := executedSiblingReduction_preservesAccept run
    applicationUsesReturnedRelation := stageApplication_eq_returnedRelationMap run
    outputConstitutesNext := executedOutput_eq_nextOperationalAssignment run }

/--
Dependent certificate history.  Its recursive tail has the type carried by the
authoritative role history, hence is rooted in `headRun.nextRun.next`.
-/
def ExecutedOperationalReductionHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ExecutedOperationalReductionEvidence headRun ×
        ExecutedOperationalReductionHistory tailRoles

/-- Build the unique reduction certificate history from the role history. -/
def buildExecutedOperationalReductionHistory :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      ExecutedOperationalReductionHistory roles
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      ⟨executedOperationalReductionEvidence headRun,
        buildExecutedOperationalReductionHistory tailRoles⟩

/-- The head of a reduction history is indexed by the exact executed head run.
This eliminator makes the causal dependency of the history computationally
observable; a homogeneous list cannot implement its result type. -/
def executedOperationalReductionHistoryHead
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExecutedOperationalReductionHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExecutedOperationalReductionEvidence headRun :=
  history.1

/-- The tail remains indexed by the state produced by the exact head run. -/
def executedOperationalReductionHistoryTail
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun)
    (history : ExecutedOperationalReductionHistory
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :
    ExecutedOperationalReductionHistory tailRoles :=
  history.2

/-- Positions of one executed opening before any transport is incorporated. -/
abbrev PendingStagePosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :=
  StageOperationalPosition
    (system := generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex))
    (left := (executedOpening run).left)
    (right := (executedOpening run).right)
    none

/-- The first position of an executed opening with pending status. -/
def pendingLeftPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    PendingStagePosition run :=
  ⟨0, Nat.zero_lt_succ 1⟩

/-- The second position of an executed opening with pending status. -/
def pendingRightPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    PendingStagePosition run :=
  ⟨1, Nat.lt_succ_self 1⟩

/-- Pending profiles retain both status-indexed positions at every opening. -/
def PendingOperationalObligation :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      PendingStagePosition headRun × PendingOperationalObligation tailRoles

/-- The unique position of a singleton retained frontier. -/
def executedRetainedPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    StageOperationalPosition (executedOperationalStatus run) :=
  ⟨0, Nat.zero_lt_succ 0⟩

/-- Operational profiles use the positions of the actually retained lists. -/
def OperationalObligation :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      StageOperationalPosition (executedOperationalStatus headRun) ×
        OperationalObligation tailRoles

/-- Enumerate both pending positions of every executed opening. -/
def pendingFrontier :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      List (PendingOperationalObligation roles)
  | _, _, _, _, _, .nil => [()]
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      (pendingFrontier tailRoles).map
          (fun rest => (pendingLeftPosition headRun, rest)) ++
        (pendingFrontier tailRoles).map
          (fun rest => (pendingRightPosition headRun, rest))

/-- Enumerate profiles of retained positions from the executed reductions. -/
def operationalFrontier :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
      List (OperationalObligation roles)
  | _, _, _, _, _, .nil => [()]
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      (operationalFrontier tailRoles).map
        (fun rest => (executedRetainedPosition headRun, rest))

def pendingWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (pendingFrontier roles).length

def executedWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (operationalFrontier roles).length

theorem pendingWidth_eq_two_pow_stageCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      pendingWidth roles = 2 ^ operationalStageCount roles
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      change
        ((pendingFrontier tailRoles).map
            (fun rest => (pendingLeftPosition headRun, rest)) ++
          (pendingFrontier tailRoles).map
            (fun rest => (pendingRightPosition headRun, rest))).length =
          2 ^ (operationalStageCount tailRoles + 1)
      have tailWidth : (pendingFrontier tailRoles).length =
          2 ^ operationalStageCount tailRoles :=
        pendingWidth_eq_two_pow_stageCount tailRoles
      calc
        ((pendingFrontier tailRoles).map
            (fun rest => (pendingLeftPosition headRun, rest)) ++
          (pendingFrontier tailRoles).map
            (fun rest => (pendingRightPosition headRun, rest))).length =
            ((pendingFrontier tailRoles).map
              (fun rest => (pendingLeftPosition headRun, rest))).length +
            ((pendingFrontier tailRoles).map
              (fun rest => (pendingRightPosition headRun, rest))).length :=
                length_append_constructive _ _
        _ = (pendingFrontier tailRoles).length +
            (pendingFrontier tailRoles).length :=
              nat_add_congr
                (length_map_constructive
                  (fun rest => (pendingLeftPosition headRun, rest)) _)
                (length_map_constructive
                  (fun rest => (pendingRightPosition headRun, rest)) _)
        _ = 2 ^ operationalStageCount tailRoles +
            2 ^ operationalStageCount tailRoles :=
              nat_add_congr tailWidth tailWidth
        _ = 2 ^ operationalStageCount tailRoles * 2 :=
              (Nat.mul_two _).symm
        _ = 2 ^ (operationalStageCount tailRoles + 1) :=
              (Nat.pow_succ 2 (operationalStageCount tailRoles)).symm

theorem pendingWidth_eq_structuralWidth {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    pendingWidth roles = structuralWidth roles :=
  (pendingWidth_eq_two_pow_stageCount roles).trans
    (structuralWidth_eq_two_pow_stageCount roles).symm

theorem executedWidth_eq_one :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      executedWidth roles = 1
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      change
        ((operationalFrontier tailRoles).map
          (fun rest => (executedRetainedPosition headRun, rest))).length = 1
      have tailWidth : (operationalFrontier tailRoles).length = 1 :=
        executedWidth_eq_one tailRoles
      exact Eq.trans
        (length_map_constructive
          (fun rest => (executedRetainedPosition headRun, rest)) _)
        tailWidth

/-- Every pending position is one of the two positions of its opening. -/
theorem pendingPosition_eq_left_or_right {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (position : PendingStagePosition run) :
    position = pendingLeftPosition run ∨
      position = pendingRightPosition run := by
  cases value : position.val with
  | zero =>
      apply Or.inl
      apply Fin.ext
      exact value
  | succ remaining =>
      apply Or.inr
      apply Fin.ext
      have positionBelowTwo : position.val < 2 := position.isLt
      rw [value] at positionBelowTwo
      have belowOne : remaining < 1 :=
        Nat.lt_of_succ_lt_succ positionBelowTwo
      have isZero : remaining = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ belowOne)
      rw [value, isZero]
      rfl

/-- The two pending positions of an opening remain distinct. -/
theorem pendingPositions_distinct {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    pendingLeftPosition run ≠ pendingRightPosition run := by
  intro same
  exact Nat.noConfusion (congrArg Fin.val same)

/-- Every pending status profile occurs in the pending frontier. -/
theorem pendingFrontier_complete :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run)
      (profile : PendingOperationalObligation roles),
      List.Mem profile (pendingFrontier roles)
  | _, _, _, _, _, .nil, profile => by
      change Unit at profile
      cases profile
      exact .head _
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile => by
      change PendingStagePosition headRun ×
        PendingOperationalObligation tailRoles at profile
      cases profile with
      | mk position rest =>
          cases pendingPosition_eq_left_or_right headRun position with
          | inl leftExact =>
              cases leftExact
              exact mem_append_left_constructive _
                (mem_map_constructive
                  (fun value => (pendingLeftPosition headRun, value))
                  (pendingFrontier_complete tailRoles rest))
          | inr rightExact =>
              cases rightExact
              exact mem_append_right_constructive _
                (mem_map_constructive
                  (fun value => (pendingRightPosition headRun, value))
                  (pendingFrontier_complete tailRoles rest))

/-- The pending frontier enumerates every pending status profile once. -/
theorem pendingFrontier_nodup :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (pendingFrontier roles).Nodup
  | _, _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      change
        ((pendingFrontier tailRoles).map
            (fun value => (pendingLeftPosition headRun, value)) ++
          (pendingFrontier tailRoles).map
            (fun value => (pendingRightPosition headRun, value))).Nodup
      have tailNodup := pendingFrontier_nodup tailRoles
      have leftNodup := nodup_map_constructive
        (fun value => (pendingLeftPosition headRun, value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      have rightNodup := nodup_map_constructive
        (fun value => (pendingRightPosition headRun, value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      exact nodup_append_constructive leftNodup rightNodup
        (fun leftValue leftMem rightValue rightMem same => by
          let ⟨leftSource, _, leftExact⟩ :=
            mem_map_preimage_constructive
              (fun value => (pendingLeftPosition headRun, value)) leftMem
          let ⟨rightSource, _, rightExact⟩ :=
            mem_map_preimage_constructive
              (fun value => (pendingRightPosition headRun, value)) rightMem
          have pairSame :
              (pendingLeftPosition headRun, leftSource) =
                (pendingRightPosition headRun, rightSource) :=
            Eq.trans leftExact (Eq.trans same rightExact.symm)
          exact pendingPositions_distinct headRun (congrArg Prod.fst pairSame))

/-- The unique index of a retained singleton is its constructed index zero. -/
theorem retainedPosition_eq_executedPosition {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (position : Fin (executedSiblingReduction run).retained.length) :
    position = executedRetainedPosition run := by
  apply Fin.ext
  have widthOne : (executedSiblingReduction run).retained.length = 1 :=
    executedSiblingReduction_width run
  have positionBelowOne : position.val < 1 :=
    Eq.mp (congrArg (fun width => position.val < width) widthOne) position.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ positionBelowOne)

/-- Every operational profile occurs in the frontier built from retained positions. -/
theorem operationalFrontier_complete :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run)
      (profile : OperationalObligation roles),
      List.Mem profile (operationalFrontier roles)
  | _, _, _, _, _, .nil, profile => by
      change Unit at profile
      cases profile
      exact .head _
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile => by
      change Fin (executedSiblingReduction headRun).retained.length ×
        OperationalObligation tailRoles at profile
      cases profile with
      | mk position rest =>
          have positionExact := retainedPosition_eq_executedPosition headRun position
          cases positionExact
          exact mem_map_constructive
            (fun value => (executedRetainedPosition headRun, value))
            (operationalFrontier_complete tailRoles rest)

/-- The operational enumeration contains each retained-position profile once. -/
theorem operationalFrontier_nodup :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (operationalFrontier roles).Nodup
  | _, _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      nodup_map_constructive
        (fun value => (executedRetainedPosition headRun, value))
        (fun same => congrArg Prod.snd same)
        (operationalFrontier_nodup tailRoles)

/-- Accepted local payload selected by one structural left/right role. -/
def LocalAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) : Bool → Type
  | false =>
      { continuation : GeneratedStructuralBranchContinuation
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh) //
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var false stage.discovery.fresh)
          continuation }
  | true =>
      { continuation : GeneratedStructuralBranchContinuation
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh) //
        GeneratedStructuralBranchAccept
          ((constructStage (depth + 1)).operationalRoot.child
            stage.discovery.var true stage.discovery.fresh)
          continuation }

/-- Accepted payload carried by the sibling retained by the executed reduction. -/
def RetainedAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) : Type :=
  { continuation : GeneratedStructuralBranchContinuation
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh) //
    GeneratedStructuralBranchAccept
      ((constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh)
      continuation }

/--
Normalize either structural role by the transport of the executed reduction.
The left case consumes the discovered map and its separate preservation proof;
the already retained right case is unchanged.
-/
def normalizeLocalAcceptedPayload {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (choice : Bool) → LocalAcceptedPayload run choice →
      RetainedAcceptedPayload run
  | false, payload =>
      ⟨stage.discovery.relation.mapContinuation payload.1,
        executedSiblingReduction_preservesAccept run payload.1 payload.2⟩
  | true, payload => payload

@[simp] theorem normalizeLocalAcceptedPayload_left_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run false) :
    (normalizeLocalAcceptedPayload run false payload).1 =
      stage.discovery.relation.mapContinuation payload.1 :=
  rfl

@[simp] theorem normalizeLocalAcceptedPayload_right_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (payload : LocalAcceptedPayload run true) :
    (normalizeLocalAcceptedPayload run true payload).1 = payload.1 :=
  rfl

/-- Every structural profile carries accepted local data at every opening. -/
def StructuralAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    StructuralObligation roles → Type
  | _, _, _, _, _, .nil, _ => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile =>
      LocalAcceptedPayload headRun profile.1.choice ×
        StructuralAcceptedPayload tailRoles profile.2

/-- Accepted payloads after every structural role has been carried to the
actually retained position of its executed opening. -/
def OperationalAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      RetainedAcceptedPayload headRun ×
        OperationalAcceptedPayload tailRoles

/--
Normalize a complete structural payload profile through the executed transports
of the causally indexed history.
-/
def normalizeStructuralAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    (profile : StructuralObligation roles) →
      StructuralAcceptedPayload roles profile →
        OperationalAcceptedPayload roles
  | _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles, profile, payload =>
      ⟨normalizeLocalAcceptedPayload headRun profile.1.choice payload.1,
        normalizeStructuralAcceptedPayload tailRoles profile.2 payload.2⟩

/-- Positive accepted payload for every structural role profile. -/
def everyStructuralObligationHasAcceptedPayload :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    (roles : ThreadedConstitutiveRoleHistory run) →
    (profile : StructuralObligation roles) →
      StructuralAcceptedPayload roles profile
  | _, _, _, _, _, .nil, profile => by
      change Unit
      exact ()
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ headStage headRun _ _ tailRoles, profile => by
      change (authoritativeNormalizerInstruction headRun).Alternative ×
        StructuralObligation tailRoles at profile
      cases profile with
      | mk choice rest =>
          cases choice with
          | transformed =>
              exact ⟨⟨_, headStage.sourceAccepted⟩,
                everyStructuralObligationHasAcceptedPayload tailRoles rest⟩
          | retained =>
              exact ⟨⟨_, headStage.outputAccepted⟩,
                everyStructuralObligationHasAcceptedPayload tailRoles rest⟩

/-- The three actual frontier objects of one executed stage. -/
def executedStageFrontiers {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    List (List (GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex))) :=
  [
    executedEntryFrontier run,
    executedOpenedFrontier run,
    (executedSiblingReduction run).retained
  ]

/-- Numerical width readout of one stage. It is intentionally treated as a
derived observation: the causal reduction is carried by the frontier/status
objects above, not by this list of numbers. -/
def executedStageWidthTrace {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : List Nat :=
  (executedStageFrontiers run).map List.length

/-- For the canonical implementation, the numerical readout agrees with the
length projection of the three frontier objects. This theorem records that
agreement; the readout itself is not a causal premise of the reduction. -/
theorem executedStageWidthTrace_from_frontiers {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run =
      (executedStageFrontiers run).map List.length :=
  rfl

/-- Full transient trace, recursively read from the executed role history. -/
def executedWidthTrace :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → List Nat
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles =>
      executedStageWidthTrace headRun ++ executedWidthTrace tailRoles

/-- A constructive pointwise upper bound on a width trace. -/
inductive WidthTraceAtMost (bound : Nat) : List Nat → Prop where
  | nil : WidthTraceAtMost bound []
  | cons {width tail} : width ≤ bound → WidthTraceAtMost bound tail →
      WidthTraceAtMost bound (width :: tail)

/-- The width trace is definitionally read from frontiers of sizes 1, 2, 1. -/
theorem executedStageWidthTrace_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStageWidthTrace run = [1, 2, 1] :=
  rfl

/-- Every transient width produced by the executed history is at most two. -/
theorem executedWidthTrace_le_two :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      WidthTraceAtMost 2 (executedWidthTrace roles)
  | _, _, _, _, _, .nil => .nil
  | depth, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ _ tailRoles => by
      have oneLeTwo : 1 ≤ 2 := Nat.succ_le_succ (Nat.zero_le 1)
      change WidthTraceAtMost 2
        (1 :: 2 :: 1 :: executedWidthTrace tailRoles)
      exact .cons oneLeTwo
        (.cons (Nat.le_refl 2)
          (.cons oneLeTwo (executedWidthTrace_le_two tailRoles)))

/-- Every nonempty executed history actually reaches transient width two. -/
theorem executedWidthTrace_attains_two_of_step {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    {headRole : ThreadedConstitutiveRoleStage headRun}
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun} :
    List.Mem 2 (executedWidthTrace
      (ThreadedConstitutiveRoleHistory.step headRole tailRoles)) :=
  .tail _ (.head _)

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalReductionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedOperationalReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalReductionHistoryHead
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalReductionHistoryTail
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount_eq_historyCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.StructuralObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.PendingStagePosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingLeftPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingRightPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.PendingOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRetainedPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.zero_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.succ_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nat_add_congr
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth_eq_two_pow_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth_eq_structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingWidth_eq_two_pow_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidth_eq_one
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_left_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_right_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_preimage_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_cases_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingPosition_eq_left_or_right
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingPositions_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.pendingFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedPosition_eq_executedPosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.LocalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.RetainedAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload_left_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeLocalAcceptedPayload_right_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.StructuralAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationalAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeStructuralAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.everyStructuralObligationHasAcceptedPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageFrontiers
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthTrace_from_frontiers
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.WidthTraceAtMost
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageWidthTrace_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace_le_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedWidthTrace_attains_two_of_step
/- AXIOM_AUDIT_END -/
