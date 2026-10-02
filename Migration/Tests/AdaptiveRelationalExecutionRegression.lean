import RelationalPerimeter

namespace AdaptiveRelationalExecutionRegression
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.RelationalExtensive ConstitutiveSearch.Extensive
open ConstitutiveSearch.SAT StrongPerimetralTurning
open VariableExecution VariableExecution.Adaptive

theorem successor_reads_executed_output {source : CausalConstitutiveState}
    {opening : Opening source} (head : LocalProduction opening) (formed : Identity opening) :
    (produceSuccessor head formed).state.assignment = (head.output formed).val :=
  (produceSuccessor head formed).assignment_exact

def successor_is_formed {source : CausalConstitutiveState}
    {opening : Opening source} (head : LocalProduction opening) (formed : Identity opening) :
    GeneratedChildFormation source.operationalState opening.selected
      (produceSuccessor head formed).value opening.fresh
      (produceSuccessor head formed).state.operationalState :=
  (produceSuccessor head formed).formation

theorem next_arrival_consumes_preservation {source : CausalConstitutiveState}
    {opening : Opening source} (head : LocalProduction opening) (formed : Identity opening)
    (accepted : Accept formed (canonical formed)) :
    GeneratedStructuralBranchAccept (produceSuccessor head formed).state.operationalState
      (produceSuccessor head formed).arrival :=
  (produceSuccessor head formed).arrival_accepted_from_action accepted

theorem head_does_not_read_future (leftFuel rightFuel : Nat) (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (same : source.assignment = arrival.val) :
    headProduction (execute (leftFuel + 1) source arrival same) =
      headProduction (execute (rightFuel + 1) source arrival same) :=
  execute_head_horizon_independent leftFuel rightFuel source arrival same

theorem path_is_bounded (fuel : Nat) (source : CausalConstitutiveState)
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (same : source.assignment = arrival.val) (profile : Profile (execute fuel source arrival same)) :
    pathLength (execute fuel source arrival same) profile ≤ fuel :=
  execute_path_bounded fuel source arrival same profile

theorem dependent_tail_is_not_a_fixed_product :
    pathLength DependentTailExample.execution (DependentTailExample.leftProfile true) = 2 ∧
      pathLength DependentTailExample.execution DependentTailExample.rightProfile = 1 :=
  DependentTailExample.different_tail_lengths

theorem produced_future_states_differ :
    endpoint DependentTailExample.execution (DependentTailExample.leftProfile true) ≠
      endpoint DependentTailExample.execution DependentTailExample.rightProfile :=
  DependentTailExample.produced_endpoints_differ

theorem real_image_not_position_labels (p q : Profile DependentTailExample.execution) :
    DependentTailExample.regime.carry p = DependentTailExample.regime.carry q ↔
      interpret DependentTailExample.execution p = interpret DependentTailExample.execution q :=
  DependentTailExample.exact_fibres p q

theorem admission_is_separate_from_output :
    GeneratedStructuralBranchAccept MixedExample.first.next.operationalState
      (interpret DependentTailExample.execution (DependentTailExample.leftProfile true)) ∧
      ¬ GeneratedStructuralBranchAccept MixedExample.first.next.operationalState
        (interpret DependentTailExample.execution (DependentTailExample.leftProfile false)) :=
  ⟨DependentTailExample.accepted_outputs.1, DependentTailExample.rejected_output⟩

theorem mixed_widths : (profileCarrier MixedAdaptiveExample.execution).frontier.length = 6 ∧
    MixedAdaptiveExample.regime.frontier.length = 3 :=
  ⟨MixedAdaptiveExample.source_width, MixedAdaptiveExample.image_width⟩

theorem computed_absorption_keeps_identities (rest : Profile DependentTailExample.execution) :
    MixedAdaptiveExample.embed false rest ≠ MixedAdaptiveExample.embed true rest ∧
      MixedAdaptiveExample.regime.carry (MixedAdaptiveExample.embed false rest) =
        MixedAdaptiveExample.regime.carry (MixedAdaptiveExample.embed true rest) :=
  MixedAdaptiveExample.carries_together_without_identification rest

theorem distinct_futures_remain_distinct (value : Bool) :
    MixedAdaptiveExample.regime.carry
        (MixedAdaptiveExample.embed value (DependentTailExample.leftProfile true)) ≠
      MixedAdaptiveExample.regime.carry
        (MixedAdaptiveExample.embed value DependentTailExample.rightProfile) :=
  MixedAdaptiveExample.separates_dependent_futures value

theorem generic_image_exactness {source : CausalConstitutiveState} (execution : Execution source)
    (equality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution)))
    (p q : Profile execution) :
    (outputRegime execution equality).carry p = (outputRegime execution equality).carry q ↔
      interpret execution p = interpret execution q := output_fibres execution equality p q

theorem width_one_requires_actual_convergence {source : CausalConstitutiveState} (execution : Execution source)
    (equality : DecidableEq (ProducedOutputImage.Value (profileCarrier execution) (interpret execution))) :
    (outputRegime execution equality).frontier.length = 1 ↔
      ∀ p q, interpret execution p = interpret execution q := output_width_one_iff execution equality

end AdaptiveRelationalExecutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms AdaptiveRelationalExecutionRegression.successor_reads_executed_output
#print axioms AdaptiveRelationalExecutionRegression.successor_is_formed
#print axioms AdaptiveRelationalExecutionRegression.next_arrival_consumes_preservation
#print axioms AdaptiveRelationalExecutionRegression.head_does_not_read_future
#print axioms AdaptiveRelationalExecutionRegression.path_is_bounded
#print axioms AdaptiveRelationalExecutionRegression.dependent_tail_is_not_a_fixed_product
#print axioms AdaptiveRelationalExecutionRegression.produced_future_states_differ
#print axioms AdaptiveRelationalExecutionRegression.real_image_not_position_labels
#print axioms AdaptiveRelationalExecutionRegression.admission_is_separate_from_output
#print axioms AdaptiveRelationalExecutionRegression.mixed_widths
#print axioms AdaptiveRelationalExecutionRegression.computed_absorption_keeps_identities
#print axioms AdaptiveRelationalExecutionRegression.distinct_futures_remain_distinct
#print axioms AdaptiveRelationalExecutionRegression.generic_image_exactness
#print axioms AdaptiveRelationalExecutionRegression.width_one_requires_actual_convergence
/- AXIOM_AUDIT_END -/
