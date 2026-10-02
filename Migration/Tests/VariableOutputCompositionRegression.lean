import RelationalPerimeter

namespace VariableOutputCompositionRegression
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.RelationalExtensive VariableExecution VariableExecution.MixedExample

theorem exact_product_fibres {source : CausalConstitutiveState} {count : Nat}
    {history : ProductionHistory source count} (comparisons : ImageComparisons history)
    (p q : RelationalOccurrenceProfile history.roles) :
    (composedRegime comparisons).carry p = (composedRegime comparisons).carry q ↔
      history.output p = history.output q := composed_fibres comparisons p q

theorem product_round_trip {source : CausalConstitutiveState} {count : Nat}
    (history : ProductionHistory source count) (value : ProductImage history) :
    (outputTransport history).backward ((outputTransport history).forward value) = value :=
  (outputTransport history).forwardBackward value

theorem image_round_trip {source : CausalConstitutiveState} {count : Nat}
    (history : ProductionHistory source count) (value : OutputImage history) :
    (outputTransport history).forward ((outputTransport history).backward value) = value :=
  (outputTransport history).backwardForward value

theorem width_from_actual_images {source : CausalConstitutiveState} {count : Nat}
    {history : ProductionHistory source count} (comparisons : ImageComparisons history) :
    (composedRegime comparisons).frontier.length = 2 ^ separatingCount comparisons :=
  composed_width_pow comparisons

theorem concrete_mixed_width : (composedRegime MixedExample.comparisons).frontier.length = 2 ∧
    separatingCount MixedExample.comparisons = 1 := ⟨composed_width, one_separating_step⟩

theorem concrete_semantic_fibres (p q : profiles.Identity) :
    (composedRegime MixedExample.comparisons).carry p =
      (composedRegime MixedExample.comparisons).carry q ↔ finalOutput p = finalOutput q :=
  composed_final_fibres p q

theorem common_tail_reads_produced_assignment (formed : Identity first) :
    (transmittedState (executeOpening first) formed).assignment =
      ((executeOpening first).output formed).val := rfl

theorem resumed_tail_return (formed : Identity first) :
    (tailStateTransport (executeOpening first) formed (first_transmits formed) 1).backward
      (resumedSecond formed) = .step second (executeOpening second) (.nil second.next) :=
  resumed_second_returns formed

theorem distinct_output_does_not_authorize_same_future :
    transmittedState (executeOpening second) (identity second false) ≠ second.next :=
  separating_output_rejects_common_future

end VariableOutputCompositionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms VariableOutputCompositionRegression.exact_product_fibres
#print axioms VariableOutputCompositionRegression.product_round_trip
#print axioms VariableOutputCompositionRegression.image_round_trip
#print axioms VariableOutputCompositionRegression.width_from_actual_images
#print axioms VariableOutputCompositionRegression.concrete_mixed_width
#print axioms VariableOutputCompositionRegression.concrete_semantic_fibres
#print axioms VariableOutputCompositionRegression.common_tail_reads_produced_assignment
#print axioms VariableOutputCompositionRegression.resumed_tail_return
#print axioms VariableOutputCompositionRegression.distinct_output_does_not_authorize_same_future
/- AXIOM_AUDIT_END -/
