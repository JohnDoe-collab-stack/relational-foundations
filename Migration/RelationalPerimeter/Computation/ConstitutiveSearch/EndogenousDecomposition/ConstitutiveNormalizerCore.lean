import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveFeedback

/-!
# Constitutive normalizer core

This module is upstream of the extensive operational history.  It reifies the
transport code returned by every executed stage as a dependently typed program,
then derives the complete binary profile carrier from the structure of that
program.  No extensive frontier is imported to construct the program or its
profiles.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Number of executed openings read recursively from the dependent role
history.  This count is available before any extensive frontier is formed. -/
def operationalStageCount :
    {depth count : Nat} →
    {assignment : SequentialAssignment depth} →
    {state : ThreadedConstitutiveState depth assignment} →
    {run : ConstitutiveExecutionHistory (count := count) state} →
    ThreadedConstitutiveRoleHistory run → Nat
  | _, _, _, _, _, .nil => 0
  | _, _, _, _, _, .step _ tail => operationalStageCount tail + 1

/-- The dependent role history contains exactly the openings of its indexed
authoritative execution history. -/
theorem operationalStageCount_eq_historyCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      operationalStageCount roles = count
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step _ tail =>
      congrArg (fun value => value + 1)
        (operationalStageCount_eq_historyCount tail)

/-- One typed instruction at an executed stage.  Its endpoints are the actual
schedule endpoints, so an unrelated transport cannot inhabit this field. -/
structure ConstitutiveNormalizerInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (_run : ThreadedConstitutiveStageRun state stage) where
  code :
    TransportCode
      (GeneratedStructuralFlipAtRelation
        (rootFormula := distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex)
        stage.schedule.entry.var)
      stage.schedule.entry.source
      stage.schedule.entry.target

/-- The instruction is authoritative exactly when it is the code returned by
the execution stored at this stage. -/
def ConstitutiveNormalizerInstruction.IsAuthoritative
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (instruction : ConstitutiveNormalizerInstruction run) : Prop :=
  instruction.code = stage.execution.code

/-- The actual returned code, reified as one instruction. -/
def authoritativeNormalizerInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ConstitutiveNormalizerInstruction run :=
  ⟨stage.execution.code⟩

/-- The canonical instruction stores the returned execution code itself. -/
theorem authoritativeNormalizerInstruction_code_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (authoritativeNormalizerInstruction run).code = stage.execution.code :=
  rfl

theorem authoritativeNormalizerInstruction_isAuthoritative
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (authoritativeNormalizerInstruction run).IsAuthoritative :=
  rfl

/-- Total acceptance-preserving action denoted by one stored instruction. -/
def ConstitutiveNormalizerInstruction.toAcceptingTransport
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      stage.schedule.entry.source stage.schedule.entry.target :=
  instruction.code.eval
    (generatedStructuralFlipAtAction
      (distinctGrowingDiscoveryFormula
        (constructStage (depth + 1)).searchIndex)
      stage.schedule.entry.var)

/-- The action of the authoritative instruction is pointwise the discovered
relation on every admissible continuation, not only on the executed one. -/
theorem authoritativeNormalizerInstruction_transport_map_exact
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (continuation : GeneratedStructuralBranchContinuation
      stage.schedule.entry.source) :
    ((authoritativeNormalizerInstruction run).toAcceptingTransport run).map
        continuation =
      stage.discovery.relation.mapContinuation continuation := by
  unfold ConstitutiveNormalizerInstruction.toAcceptingTransport
  unfold authoritativeNormalizerInstruction
  rw [executedDiscoverySchedule_code stage.execution]
  rfl

/-- The two structural alternatives opened by one instruction.  The family is
indexed by the instruction that constitutes the opening: alternatives from a
different instruction are not interchangeable merely because both openings
have two branches. -/
inductive ConstitutiveNormalizerInstruction.Alternative
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (instruction : ConstitutiveNormalizerInstruction run) : Type where
  | transformed : instruction.Alternative
  | retained : instruction.Alternative

/-- Operational branch readout of an instruction-indexed alternative. -/
def ConstitutiveNormalizerInstruction.Alternative.choice
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    {instruction : ConstitutiveNormalizerInstruction run} :
    instruction.Alternative -> Bool
  | .transformed => false
  | .retained => true

/-- A raw program has exactly one instruction for each role-stage constructor.
The dependent tail is indexed by the state produced by the head execution. -/
inductive ConstitutiveNormalizerProgram :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    (roles : ThreadedConstitutiveRoleHistory run) -> Type 2 where
  | nil {depth : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      ConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.nil (state := state))
  | step {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {stage : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state stage}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (instruction : ConstitutiveNormalizerInstruction headRun)
      {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
      (tail : ConstitutiveNormalizerProgram tailRoles) :
      ConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles)

/-- Reify the returned execution code at every stage of the role history. -/
def buildConstitutiveNormalizerProgram :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    (roles : ThreadedConstitutiveRoleHistory run) ->
      ConstitutiveNormalizerProgram roles
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ headRun _ headRole tailRoles =>
      .step headRole (authoritativeNormalizerInstruction headRun)
        (buildConstitutiveNormalizerProgram tailRoles)

theorem buildConstitutiveNormalizerProgram_step
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    buildConstitutiveNormalizerProgram
        (ThreadedConstitutiveRoleHistory.step headRole tailRoles) =
      ConstitutiveNormalizerProgram.step headRole
        (authoritativeNormalizerInstruction headRun)
        (buildConstitutiveNormalizerProgram tailRoles) :=
  rfl

/-- Number of instruction constructors in a program. -/
def ConstitutiveNormalizerProgram.instructionCount :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
      ConstitutiveNormalizerProgram roles -> Nat
  | _, _, _, _, _, _, .nil => 0
  | _, _, _, _, _, _, .step _ _ tail => tail.instructionCount + 1

theorem ConstitutiveNormalizerProgram.instructionCount_step
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (instruction : ConstitutiveNormalizerInstruction headRun)
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (tail : ConstitutiveNormalizerProgram tailRoles) :
    (ConstitutiveNormalizerProgram.step headRole instruction tail).instructionCount =
      tail.instructionCount + 1 :=
  rfl

/-- The canonical program has one instruction for every constituted stage. -/
theorem buildConstitutiveNormalizerProgram_instructionCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (buildConstitutiveNormalizerProgram roles).instructionCount =
        operationalStageCount roles
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .step _ tail =>
      congrArg (fun value => value + 1)
        (buildConstitutiveNormalizerProgram_instructionCount tail)

/-- Number of transport atoms stored by a raw dependent program.  This counts
only run-specific code data. -/
def ConstitutiveNormalizerProgram.codeSize :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
      ConstitutiveNormalizerProgram roles -> Nat
  | _, _, _, _, _, _, .nil => 0
  | _, _, _, _, _, _, .step _ instruction tail =>
      instruction.code.size + tail.codeSize

/-- One instruction-indexed structural alternative for every program step. -/
def ConstitutiveNormalizerProgram.Profile :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
    (program : ConstitutiveNormalizerProgram roles) -> Type
  | _, _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, _, .step _ instruction tail =>
      instruction.Alternative × tail.Profile

/-- Complete extensive expansion of the alternatives constituted by the
program's own instructions. -/
def ConstitutiveNormalizerProgram.profileFrontier :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
    (program : ConstitutiveNormalizerProgram roles) -> List program.Profile
  | _, _, _, _, _, _, .nil => [()]
  | _, _, _, _, _, _, .step _ instruction tail =>
      (tail.profileFrontier.map (fun rest =>
        (ConstitutiveNormalizerInstruction.Alternative.transformed
          (instruction := instruction), rest))) ++
        (tail.profileFrontier.map (fun rest =>
          (ConstitutiveNormalizerInstruction.Alternative.retained
            (instruction := instruction), rest)))

/-- Each program instruction contributes the two Boolean profile extensions
of the tail frontier. This reduction equation is the typed source of the
binary width later read by extensivity. -/
theorem ConstitutiveNormalizerProgram.profileFrontier_step
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (instruction : ConstitutiveNormalizerInstruction headRun)
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (tail : ConstitutiveNormalizerProgram tailRoles) :
    (ConstitutiveNormalizerProgram.step headRole instruction tail).profileFrontier =
      (tail.profileFrontier.map (fun rest =>
        (ConstitutiveNormalizerInstruction.Alternative.transformed
          (instruction := instruction), rest))) ++
        (tail.profileFrontier.map (fun rest =>
          (ConstitutiveNormalizerInstruction.Alternative.retained
            (instruction := instruction), rest))) :=
  rfl

def ConstitutiveNormalizerProgram.profileWidth
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (program : ConstitutiveNormalizerProgram roles) : Nat :=
  program.profileFrontier.length

/-- Constructive length preservation for list maps. -/
theorem length_map_constructive {α β : Type} (f : α → β) :
    ∀ values : List α, (values.map f).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (length_map_constructive f tail)

theorem zero_add_constructive : ∀ value : Nat, 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (zero_add_constructive value)

theorem succ_add_constructive (left : Nat) :
    ∀ right : Nat,
      Nat.succ left + right = Nat.succ (left + right)
  | 0 => rfl
  | right + 1 => congrArg Nat.succ (succ_add_constructive left right)

theorem length_append_constructive {α : Type} :
    ∀ left right : List α,
      (left ++ right).length = left.length + right.length
  | [], right => (zero_add_constructive right.length).symm
  | _ :: tail, right => Eq.trans
      (congrArg Nat.succ (length_append_constructive tail right))
      (succ_add_constructive tail.length right.length).symm

theorem nat_add_congr {left left' right right' : Nat}
    (hLeft : left = left') (hRight : right = right') :
    left + right = left' + right' := by
  cases hLeft
  cases hRight
  rfl

/-- Program expansion has exactly two choices per instruction. -/
theorem ConstitutiveNormalizerProgram.profileWidth_eq_two_pow_instructionCount :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      {roles : ThreadedConstitutiveRoleHistory run}
      (program : ConstitutiveNormalizerProgram roles),
      program.profileWidth = 2 ^ program.instructionCount
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, .step _ instruction tail => by
      change
        ((tail.profileFrontier.map (fun rest =>
            (ConstitutiveNormalizerInstruction.Alternative.transformed
              (instruction := instruction), rest))) ++
          (tail.profileFrontier.map (fun rest =>
            (ConstitutiveNormalizerInstruction.Alternative.retained
              (instruction := instruction), rest)))).length =
            2 ^ (tail.instructionCount + 1)
      have tailWidth : tail.profileFrontier.length =
          2 ^ tail.instructionCount :=
        tail.profileWidth_eq_two_pow_instructionCount
      calc
        ((tail.profileFrontier.map (fun rest =>
            (ConstitutiveNormalizerInstruction.Alternative.transformed
              (instruction := instruction), rest))) ++
          (tail.profileFrontier.map (fun rest =>
            (ConstitutiveNormalizerInstruction.Alternative.retained
              (instruction := instruction), rest)))).length =
            (tail.profileFrontier.map (fun rest =>
              (ConstitutiveNormalizerInstruction.Alternative.transformed
                (instruction := instruction), rest))).length +
              (tail.profileFrontier.map (fun rest =>
                (ConstitutiveNormalizerInstruction.Alternative.retained
                  (instruction := instruction), rest))).length :=
          length_append_constructive _ _
        _ = tail.profileFrontier.length + tail.profileFrontier.length :=
          nat_add_congr
            (length_map_constructive (fun rest =>
              (ConstitutiveNormalizerInstruction.Alternative.transformed
                (instruction := instruction), rest)) _)
            (length_map_constructive (fun rest =>
              (ConstitutiveNormalizerInstruction.Alternative.retained
                (instruction := instruction), rest)) _)
        _ = 2 ^ tail.instructionCount + 2 ^ tail.instructionCount :=
          nat_add_congr tailWidth tailWidth
        _ = 2 ^ tail.instructionCount * 2 := (Nat.mul_two _).symm
        _ = 2 ^ (tail.instructionCount + 1) :=
          (Nat.pow_succ 2 tail.instructionCount).symm

/-- Constructively transport membership through a list map. -/
theorem mem_map_constructive {α β : Type} (f : α → β) {value : α} :
    ∀ {values : List α}, List.Mem value values →
      List.Mem (f value) (values.map f)
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (mem_map_constructive f prior)

theorem mem_append_left_constructive {α : Type} {value : α} :
    ∀ {left : List α} (right : List α), List.Mem value left →
      List.Mem value (left ++ right)
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ prior =>
      .tail _ (mem_append_left_constructive _ prior)

theorem mem_append_right_constructive {α : Type} {value : α} :
    ∀ (left : List α) {right : List α}, List.Mem value right →
      List.Mem value (left ++ right)
  | [], _, prior => prior
  | _ :: tail, _, prior =>
      .tail _ (mem_append_right_constructive tail prior)

theorem mem_map_preimage_constructive {α β : Type} (f : α → β)
    {target : β} :
    ∀ {values : List α}, List.Mem target (values.map f) →
      ∃ source, List.Mem source values ∧ f source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, sourceMem, exactValue⟩ :=
        mem_map_preimage_constructive f prior
      ⟨source, .tail _ sourceMem, exactValue⟩

theorem mem_append_cases_constructive {α : Type} {value : α} :
    ∀ {left right : List α}, List.Mem value (left ++ right) →
      List.Mem value left ∨ List.Mem value right
  | [], _, prior => Or.inr prior
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: tail, _, .tail _ prior =>
      match mem_append_cases_constructive (left := tail) prior with
      | Or.inl inTail => Or.inl (.tail _ inTail)
      | Or.inr inRight => Or.inr inRight

theorem nodup_map_constructive {α β : Type} (f : α → β)
    (injective : ∀ {left right : α}, f left = f right → left = right) :
    ∀ {values : List α}, values.Nodup → (values.map f).Nodup
  | [], .nil => .nil
  | _head :: _, .cons headFresh tailNodup =>
      .cons
        (fun _mapped mappedMem same =>
          let ⟨source, sourceMem, sourceExact⟩ :=
            mem_map_preimage_constructive f mappedMem
          headFresh source sourceMem
            (injective (Eq.trans same sourceExact.symm)))
        (nodup_map_constructive f injective tailNodup)

theorem nodup_append_constructive {α : Type} :
    ∀ {left right : List α},
      left.Nodup → right.Nodup →
      (∀ leftValue, List.Mem leftValue left →
        ∀ rightValue, List.Mem rightValue right →
          leftValue ≠ rightValue) →
      (left ++ right).Nodup
  | [], _, .nil, rightNodup, _ => rightNodup
  | head :: _tail, _right, .cons headFresh tailNodup, rightNodup, disjoint =>
      .cons
        (fun value valueMem same =>
          match mem_append_cases_constructive valueMem with
          | .inl inTail => headFresh value inTail same
          | .inr inRight =>
              disjoint head (.head _) value inRight same)
        (nodup_append_constructive tailNodup rightNodup
          (fun leftValue inTail rightValue inRight =>
            disjoint leftValue (.tail _ inTail) rightValue inRight))

/-- Every program profile occurs in the program-produced frontier. -/
theorem ConstitutiveNormalizerProgram.profileFrontier_complete :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      {roles : ThreadedConstitutiveRoleHistory run}
      (program : ConstitutiveNormalizerProgram roles)
      (profile : program.Profile),
      List.Mem profile program.profileFrontier
  | _, _, _, _, _, _, .nil, profile => by
      change Unit at profile
      cases profile
      exact .head _
  | _, _, _, _, _, _, .step _ instruction tail, profile => by
      change instruction.Alternative × tail.Profile at profile
      cases profile with
      | mk choice rest =>
          cases choice with
          | transformed =>
              exact mem_append_left_constructive _
                (mem_map_constructive (fun value =>
                  (ConstitutiveNormalizerInstruction.Alternative.transformed
                    (instruction := instruction), value))
                  (tail.profileFrontier_complete rest))
          | retained =>
              exact mem_append_right_constructive _
                (mem_map_constructive (fun value =>
                  (ConstitutiveNormalizerInstruction.Alternative.retained
                    (instruction := instruction), value))
                  (tail.profileFrontier_complete rest))

/-- The program expansion contains each binary profile exactly once. -/
theorem ConstitutiveNormalizerProgram.profileFrontier_nodup :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      {roles : ThreadedConstitutiveRoleHistory run}
      (program : ConstitutiveNormalizerProgram roles),
      program.profileFrontier.Nodup
  | _, _, _, _, _, _, .nil =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, _, _, _, .step _ instruction tail => by
      change
        ((tail.profileFrontier.map (fun value =>
            (ConstitutiveNormalizerInstruction.Alternative.transformed
              (instruction := instruction), value))) ++
          (tail.profileFrontier.map (fun value =>
            (ConstitutiveNormalizerInstruction.Alternative.retained
              (instruction := instruction), value)))).Nodup
      have tailNodup := tail.profileFrontier_nodup
      have leftNodup := nodup_map_constructive
        (fun value =>
          (ConstitutiveNormalizerInstruction.Alternative.transformed
            (instruction := instruction), value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      have rightNodup := nodup_map_constructive
        (fun value =>
          (ConstitutiveNormalizerInstruction.Alternative.retained
            (instruction := instruction), value))
        (fun same => congrArg Prod.snd same)
        tailNodup
      exact nodup_append_constructive leftNodup rightNodup
        (fun leftValue leftMem rightValue rightMem same => by
          let ⟨leftSource, _, leftExact⟩ :=
            mem_map_preimage_constructive
              (fun value =>
                (ConstitutiveNormalizerInstruction.Alternative.transformed
                  (instruction := instruction), value)) leftMem
          let ⟨rightSource, _, rightExact⟩ :=
            mem_map_preimage_constructive
              (fun value =>
                (ConstitutiveNormalizerInstruction.Alternative.retained
                  (instruction := instruction), value)) rightMem
          have pairSame :
              (ConstitutiveNormalizerInstruction.Alternative.transformed
                  (instruction := instruction), leftSource) =
                (ConstitutiveNormalizerInstruction.Alternative.retained
                  (instruction := instruction), rightSource) :=
            Eq.trans leftExact (Eq.trans same rightExact.symm)
          have choiceSame : false = true :=
            congrArg
              (fun pair : instruction.Alternative × tail.Profile =>
                ConstitutiveNormalizerInstruction.Alternative.choice pair.1)
              pairSame
          exact Bool.noConfusion choiceSame)

/-- Recursive authority predicate for the whole program. -/
def ConstitutiveNormalizerProgram.IsAuthoritative :
    {depth count : Nat} ->
    {assignment : SequentialAssignment depth} ->
    {state : ThreadedConstitutiveState depth assignment} ->
    {run : ConstitutiveExecutionHistory (count := count) state} ->
    {roles : ThreadedConstitutiveRoleHistory run} ->
      ConstitutiveNormalizerProgram roles -> Prop
  | _, _, _, _, _, _, .nil => True
  | _, _, _, _, _, _, .step _ instruction tail =>
      instruction.IsAuthoritative ∧ tail.IsAuthoritative

theorem buildConstitutiveNormalizerProgram_isAuthoritative :
    ∀ {depth count : Nat}
      {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {run : ConstitutiveExecutionHistory (count := count) state}
      (roles : ThreadedConstitutiveRoleHistory run),
      (buildConstitutiveNormalizerProgram roles).IsAuthoritative
  | _, _, _, _, _, .nil => True.intro
  | _, _, _, _, _, @ThreadedConstitutiveRoleHistory.step
      _ _ _ _ _ _ _ _ tailRoles =>
      ⟨rfl, buildConstitutiveNormalizerProgram_isAuthoritative tailRoles⟩

/-- A program bundled with the recursive proof that every instruction came
from the indexed execution. -/
structure AuthoritativeConstitutiveNormalizerProgram
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) where
  program : ConstitutiveNormalizerProgram roles
  authoritative : program.IsAuthoritative

def buildAuthoritativeConstitutiveNormalizerProgram
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    AuthoritativeConstitutiveNormalizerProgram roles :=
  ⟨buildConstitutiveNormalizerProgram roles,
    buildConstitutiveNormalizerProgram_isAuthoritative roles⟩

/-- The structural carrier is definitionally the profile type of the canonical
program produced by the executed role history. -/
abbrev StructuralObligation
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Type :=
  (buildConstitutiveNormalizerProgram roles).Profile

/-- The exhaustive structural frontier is the canonical program expansion. -/
def structuralFrontier
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    List (StructuralObligation roles) :=
  (buildConstitutiveNormalizerProgram roles).profileFrontier

def structuralWidth
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) : Nat :=
  (buildConstitutiveNormalizerProgram roles).profileWidth

theorem structuralFrontier_eq_programProfileFrontier
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    structuralFrontier roles =
      (buildConstitutiveNormalizerProgram roles).profileFrontier :=
  rfl

theorem structuralWidth_eq_programProfileWidth
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    structuralWidth roles =
      (buildConstitutiveNormalizerProgram roles).profileWidth :=
  rfl

theorem structuralWidth_eq_two_pow_stageCount
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    structuralWidth roles = 2 ^ operationalStageCount roles :=
  Eq.trans
    (structuralWidth_eq_programProfileWidth roles)
    (Eq.trans
      (buildConstitutiveNormalizerProgram roles).profileWidth_eq_two_pow_instructionCount
      (congrArg (fun count => 2 ^ count)
        (buildConstitutiveNormalizerProgram_instructionCount roles)))

theorem structuralFrontier_complete
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run)
    (profile : StructuralObligation roles) :
    List.Mem profile (structuralFrontier roles) :=
  (buildConstitutiveNormalizerProgram roles).profileFrontier_complete profile

theorem structuralFrontier_nodup
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) :
    (structuralFrontier roles).Nodup :=
  (buildConstitutiveNormalizerProgram roles).profileFrontier_nodup

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.operationalStageCount_eq_historyCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction.IsAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction_code_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction_isAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction.toAcceptingTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.authoritativeNormalizerInstruction_transport_map_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction.Alternative
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerInstruction.Alternative.choice
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.instructionCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.instructionCount_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_instructionCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.codeSize
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.Profile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileFrontier_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.zero_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.succ_add_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.length_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nat_add_congr
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileWidth_eq_two_pow_instructionCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_left_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_right_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_map_preimage_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.mem_append_cases_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_map_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.nodup_append_constructive
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.IsAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildConstitutiveNormalizerProgram_isAuthoritative
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthoritativeConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildAuthoritativeConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.StructuralObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_eq_programProfileFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth_eq_programProfileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralWidth_eq_two_pow_stageCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.structuralFrontier_nodup
/- AXIOM_AUDIT_END -/
