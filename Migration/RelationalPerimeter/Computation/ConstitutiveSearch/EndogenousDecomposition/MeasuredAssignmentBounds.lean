import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredComparisonBounds
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.SequentialHistory

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

theorem readAlternatingAssignment_bound (query : Var) :
    (readAlternatingAssignment query).work.total ≤ query + 1 := by
  induction query with
  | zero => exact Nat.le_refl 1
  | succ query ih =>
    cases query with
    | zero => exact Nat.le_succ 1
    | succ query =>
      change (readAlternatingAssignment (query + 1)).work.visit.total ≤ _
      rw [ComparisonWork.total_visit]
      exact Nat.add_le_add_right ih 1

theorem readFlippedAssignment_bound (selected : Var) {assignment : Assignment}
    (reader : MeasuredAssignment assignment) (query : Var) :
    (readFlippedAssignment selected reader query).work.total ≤
      (reader query).work.total + (query + 2) := by
  unfold readFlippedAssignment
  dsimp only
  split <;>
    change ((compareUnary query selected).work.add (reader query).work).visit.total ≤ _ <;>
    rw [ComparisonWork.total_visit, ComparisonWork.total_add] <;>
    exact Nat.le_trans
      (Nat.add_le_add_right (Nat.add_le_add_right (compareUnary_total_le query selected) _) 1)
      (Nat.le_of_eq (by rw [Nat.add_comm (query + 1), Nat.add_assoc]))

/-- Syntax-directed bound for interpreting a query through the returned code. -/
def transportedReadOverhead {root : Cnf} {selected : Var} :
    {source target : GeneratedStructuralBranchContext root} →
    TransportCode (GeneratedStructuralFlipAtRelation selected) source target → Var → Nat
  | _, _, .identity _, _ => 1
  | _, _, .atom _, query => query + 2
  | _, _, .compose first second, query =>
    transportedReadOverhead first query + transportedReadOverhead second query + 1

theorem readTransportedAssignment_bound {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source)
    (reader : MeasuredAssignment input.1) (query : Var) :
    (readTransportedAssignment selected code input reader query).work.total ≤
      (reader query).work.total + transportedReadOverhead code query := by
  induction code with
  | identity state =>
    change (reader query).work.visit.total ≤ (reader query).work.total + 1
    rw [ComparisonWork.total_visit]
    exact Nat.le_refl _
  | atom relation => exact readFlippedAssignment_bound selected reader query
  | compose first second firstBound secondBound =>
    let middle := (first.eval (generatedStructuralFlipAtAction root selected)).map input
    let readMiddle := readTransportedAssignment selected first input reader
    change (readTransportedAssignment selected second middle readMiddle query).work.visit.total ≤ _
    rw [ComparisonWork.total_visit]
    calc
      _ ≤ ((readMiddle query).work.total + transportedReadOverhead second query) + 1 :=
        Nat.add_le_add_right (secondBound middle readMiddle) 1
      _ ≤ ((reader query).work.total + transportedReadOverhead first query +
          transportedReadOverhead second query) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (firstBound input reader) _) 1
      _ = _ := by
        change _ = (reader query).work.total +
          (transportedReadOverhead first query + transportedReadOverhead second query + 1)
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

theorem executeSequentialStage_reader_bound (depth : Nat)
    (input : SequentialAssignment depth) (query : Var) :
    ((executeSequentialStage depth input).next.reader query).work.total ≤
      (input.reader query).work.total + (query + 2) := by
  let run := executeSequentialStage depth input
  have bound := readTransportedAssignment_bound run.schedule.entry.var
    run.execution.code run.sourceContinuation input.reader query
  have overhead : transportedReadOverhead run.execution.code query = query + 2 := by
    rw [executedDiscoverySchedule_code]
    rfl
  rw [overhead] at bound
  exact bound

theorem transportedMeasuredAssignment_work
    {before after : Assignment} (same : before = after)
    (reader : MeasuredAssignment before) (query : Var) :
    ((Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
      reader same) query).work = (reader query).work := by
  cases same
  rfl

theorem SequentialStageRun.reader_bound {depth : Nat}
    {input : SequentialAssignment depth} (run : SequentialStageRun depth input)
    (query : Var) :
    (run.next.reader query).work.total ≤
      (input.reader query).work.total + (query + 2) := by
  rw [run.nextReaderWorkExact]
  have bound := readTransportedAssignment_bound run.schedule.entry.var
    run.execution.code run.sourceContinuation
      (Eq.rec (motive := fun assignment _ => MeasuredAssignment assignment)
        input.reader run.sourceAssignmentExact.symm) query
  have overhead : transportedReadOverhead run.execution.code query = query + 2 := by
    rw [executedDiscoverySchedule_code]
    rfl
  rw [overhead] at bound
  rw [transportedMeasuredAssignment_work] at bound
  exact bound

theorem executeSequentialHistory_reader_bound (depth count : Nat)
    (input : SequentialAssignment depth) (query : Var) :
    ((executeSequentialHistory depth count input).final.reader query).work.total ≤
      (input.reader query).work.total + count * (query + 2) := by
  induction count generalizing depth with
  | zero => rw [Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _
  | succ count ih =>
    let head := executeSequentialStage depth input
    change ((executeSequentialHistory (depth + 1) count head.next).final.reader query).work.total ≤ _
    calc
      _ ≤ (head.next.reader query).work.total + count * (query + 2) := ih (depth + 1) head.next
      _ ≤ ((input.reader query).work.total + (query + 2)) + count * (query + 2) :=
        Nat.add_le_add_right (executeSequentialStage_reader_bound depth input query) _
      _ = _ := by rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (query + 2)]

theorem readAssignmentQueries_bound {assignment : Assignment}
    (reader : MeasuredAssignment assignment) (queries : List Var) (bound : Nat)
    (bounded : ∀ query, query ∈ queries → (reader query).work.total ≤ bound) :
    (readAssignmentQueries reader queries).work.total ≤ (bound + 1) * queries.length + 1 := by
  induction queries with
  | nil => rw [List.length_nil, Nat.mul_zero]; exact Nat.le_refl 1
  | cons query rest ih =>
    have headBound := bounded query (List.mem_cons_self)
    have tailBound := ih (fun value member => bounded value (List.mem_cons_of_mem query member))
    change ((reader query).work.add (readAssignmentQueries reader rest).work).visit.total ≤ _
    rw [ComparisonWork.total_visit, ComparisonWork.total_add]
    calc
      _ ≤ (bound + ((bound + 1) * rest.length + 1)) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add headBound tailBound) 1
      _ = _ := by
        rw [List.length_cons, Nat.mul_succ,
          ← Nat.add_assoc bound ((bound + 1) * rest.length) 1,
          Nat.add_comm bound ((bound + 1) * rest.length),
          Nat.add_assoc ((bound + 1) * rest.length) bound 1]

theorem stageSelectedVar_mono {first second : Nat} (before : first ≤ second) :
    stageSelectedVar first ≤ stageSelectedVar second := by
  cases Nat.lt_or_eq_of_le before with
  | inl strict => exact Nat.le_of_lt (stageSelectedVar_strict strict)
  | inr same => cases same; exact Nat.le_refl _

theorem executedHistory_variables_bounded (depth count : Nat)
    (input : SequentialAssignment depth) :
    ∀ query, query ∈ (executeSequentialHistory depth count input).executedVariables →
      query ≤ stageSelectedVar (depth + count) := by
  induction count generalizing depth with
  | zero => intro query member; cases member
  | succ count ih =>
    intro query member
    change query ∈ (executeSequentialStage depth input).schedule.entry.var ::
      (executeSequentialHistory (depth + 1) count (executeSequentialStage depth input).next).executedVariables at member
    cases member with
    | head =>
      rw [sequentialStage_selected_exact]
      exact stageSelectedVar_mono (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le count)) depth)
    | tail _ member =>
      have bounded := ih (depth + 1) (executeSequentialStage depth input).next query member
      have indices : depth + 1 + count = depth + (count + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 count]
      rw [indices] at bounded
      exact bounded

/-- Closed bound for the actual terminal-reader recursion of the concrete family. -/
theorem concreteTerminalQueries_bound (depth count : Nat) :
    let history := executeSequentialHistory depth count (initialSequentialAssignment depth)
    let largest := stageSelectedVar (depth + count)
    (readAssignmentQueries history.final.reader history.executedVariables).work.total ≤
      ((largest + 1 + count * (largest + 2)) + 1) * count + 1 := by
  dsimp only
  have perQuery : ∀ query,
      query ∈ (executeSequentialHistory depth count (initialSequentialAssignment depth)).executedVariables →
      (((executeSequentialHistory depth count (initialSequentialAssignment depth)).final.reader query).work.total ≤
        stageSelectedVar (depth + count) + 1 + count * (stageSelectedVar (depth + count) + 2)) := by
    intro query member
    have queryBound := executedHistory_variables_bounded depth count _ query member
    have reading := executeSequentialHistory_reader_bound depth count (initialSequentialAssignment depth) query
    exact Nat.le_trans reading (Nat.add_le_add
      (Nat.le_trans (readAlternatingAssignment_bound query) (Nat.add_le_add_right queryBound 1))
      (Nat.mul_le_mul_left count (Nat.add_le_add_right queryBound 2)))
  have bound := readAssignmentQueries_bound
    (executeSequentialHistory depth count (initialSequentialAssignment depth)).final.reader
    (executeSequentialHistory depth count (initialSequentialAssignment depth)).executedVariables
    _ perQuery
  rw [executedHistory_variables_length] at bound
  exact bound

theorem concreteTerminalBit_bound (depth count : Nat) :
    let history := executeSequentialHistory depth (count + 1) (initialSequentialAssignment depth)
    let largest := stageSelectedVar (depth + (count + 1))
    (terminalFromSequentialHistory history).bitRead.work.total ≤
      largest + 1 + (count + 1) * (largest + 2) := by
  dsimp only
  let history := executeSequentialHistory depth (count + 1) (initialSequentialAssignment depth)
  let terminal := terminalFromSequentialHistory history
  change (history.final.reader terminal.observedVar).work.total ≤ _
  rw [terminal.observedVarExact]
  have indexExact : lastStageDepth depth count + 1 = depth + (count + 1) := by
    unfold lastStageDepth
    rw [advancedDepth_eq_add, Nat.add_assoc]
  rw [indexExact]
  exact Nat.le_trans (executeSequentialHistory_reader_bound depth (count + 1) _ _)
    (Nat.add_le_add_right (readAlternatingAssignment_bound _) _)

/-- Costs of the two actual reads plus the variable traversal and Boolean fold.
No history-size profile is added to these reader costs. -/
def SequentialTerminalArtifact.measuredReadWork {depth count : Nat} {input : SequentialAssignment depth}
    {history : SequentialHistory depth input (count + 1)} (terminal : SequentialTerminalArtifact history) : Nat :=
  ((terminal.variableReadout.visits + terminal.assignmentReadout.work.total) +
    terminal.bitRead.work.total) + terminal.readoutRun.bitVisits

theorem concreteTerminalReadWork_bound (depth count : Nat) :
    let history := executeSequentialHistory depth (count + 1) (initialSequentialAssignment depth)
    let largest := stageSelectedVar (depth + (count + 1))
    let readBound := largest + 1 + (count + 1) * (largest + 2)
    (terminalFromSequentialHistory history).measuredReadWork ≤
      (((count + 1) + 1) + ((readBound + 1) * (count + 1) + 1)) + readBound + (count + 1) := by
  dsimp only
  let history := executeSequentialHistory depth (count + 1) (initialSequentialAssignment depth)
  let terminal := terminalFromSequentialHistory history
  have folded : terminal.readoutRun.bitVisits = count + 1 := by
    rw [terminal.readoutRunExact, terminal.observedBitsExact, runTerminalReadout_visits]
    exact executedHistory_bits_length _ _ _
  unfold SequentialTerminalArtifact.measuredReadWork
  rw [folded]
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.le_of_eq (SequentialHistory.lastVariableRun_visits history)
    · exact concreteTerminalQueries_bound depth (count + 1)
  · exact concreteTerminalBit_bound depth count

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.readAlternatingAssignment_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.readFlippedAssignment_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.transportedReadOverhead
#print axioms ConstitutiveSearch.EndogenousDecomposition.readTransportedAssignment_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialStage_reader_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeSequentialHistory_reader_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.readAssignmentQueries_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.stageSelectedVar_mono
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_variables_bounded
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteTerminalQueries_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteTerminalBit_bound
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialTerminalArtifact.measuredReadWork
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteTerminalReadWork_bound
/- AXIOM_AUDIT_END -/
