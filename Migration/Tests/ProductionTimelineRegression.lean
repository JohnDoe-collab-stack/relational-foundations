import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution

namespace ProductionTimelineRegression
set_option maxHeartbeats 3200000
open ConstitutiveSearch.EndogenousDecomposition

/-- Deliberately evaluate a genuine following stage before the first decomposition.
Unlike the historical one-stage replay, this uses a nonempty later continuation. -/
def delayedTwo {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    OperationalProductionProgram (CausalOperationalExecutionHistory (_count := 2) state context) :=
  .discover state fun d1 exact1 =>
    .applyStage state fresh d1 exact1 fun first =>
      .discover first.run.nextRun.next fun d2 exact2 =>
        .applyStage first.run.nextRun.next (first.run.nextRun.fresh fresh) d2 exact2 fun second =>
          .decompose context first.run fun production1 =>
            .decompose production1.nextContext second.run fun production2 =>
              .done (.step first.stage first.run production1
                (.step second.stage second.run production2
                  (.nil second.run.nextRun.next production2.nextContext)))

/-- Equal terminal values alone cannot distinguish the reordered process. -/
theorem delayed_value_same {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (delayedTwo state context fresh).evaluate.1 =
      executeCausalOperationalExecutionHistory 2 state context fresh := by
  have valueExact : (delayedTwo state context fresh).evaluate.1 =
      (causalOperationalExecutionProgram 2 state context fresh).evaluate.1 := by
    dsimp only [delayedTwo, causalOperationalExecutionProgram, withCausalOperationalHead,
      OperationalProductionProgram.evaluate]
  exact Eq.trans valueExact
    (congrArg Prod.fst (executeWithTrace_program_exact 2 state context fresh)).symm

/-- Events are emitted by the same interpreter that computes the value. -/
theorem delayed_trace {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (delayedTwo state context fresh).evaluate.2 =
      [.discovered depth, .applied depth, .discovered (depth + 1),
       .applied (depth + 1), .decomposed depth, .decomposed (depth + 1)] := rfl

/-- The same-value reordering violates the fixed chronological contract. -/
theorem delayed_fails_order {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (delayedTwo state context fresh).evaluate.2 ≠ operationalProductionTimeline 2 depth := by
  intro same
  change [OperationalProductionEvent.discovered depth, .applied depth, .discovered (depth + 1),
       .applied (depth + 1), .decomposed depth, .decomposed (depth + 1)] =
     [.discovered depth, .applied depth, .decomposed depth,
      .discovered (depth + 1), .applied (depth + 1), .decomposed (depth + 1)] at same
  have first := List.cons.inj same
  have second := List.cons.inj first.2
  have third := List.cons.inj second.2
  cases third.1

/-- The positive control is the evaluator actually called by the public executor. -/
theorem canonical_order (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (context : ConstitutedOperationalPrefix (causalStateOfThreadedState state))
    (fresh : ThreadedStateFreshForNext state) :
    (executeCausalOperationalExecutionWithTrace count state context fresh).2 =
      operationalProductionTimeline count depth :=
  operationalProductionTimeline_exact count state context fresh

end ProductionTimelineRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ProductionTimelineRegression.delayedTwo
#print axioms ProductionTimelineRegression.delayed_value_same
#print axioms ProductionTimelineRegression.delayed_trace
#print axioms ProductionTimelineRegression.delayed_fails_order
#print axioms ProductionTimelineRegression.canonical_order
/- AXIOM_AUDIT_END -/
