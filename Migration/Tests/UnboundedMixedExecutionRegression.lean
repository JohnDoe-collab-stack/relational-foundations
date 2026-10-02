import RelationalPerimeter

namespace UnboundedMixedExecutionRegression
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.RelationalExtensive ConstitutiveSearch.Extensive
open ConstitutiveSearch.SAT VariableExecution VariableExecution.UnboundedMixed

theorem actual_prefix_selection {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    Adaptive.chooseOpening source prepared.arrival = some (prefixOpening prepared) :=
  prefix_selected_from_state prepared

theorem actual_terminal_selection {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    Adaptive.chooseOpening source prepared.arrival = some (terminalOpening prepared) :=
  terminal_selected_from_state prepared

theorem actual_search_changes_status (count : Nat) :
    tryEndogenousFlipCandidate (initialState (count + 1)).operationalState (count + 2) ≠ none ∧
      tryEndogenousFlipCandidate (initialState 0).operationalState 0 = none :=
  ⟨prefix_search_succeeds (initialPrepared (count + 1)), terminal_search_fails (initialPrepared 0)⟩

theorem common_future_reads_produced_assignment {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (formed : Identity (prefixOpening prepared)) :
    (transmittedState (prefixSelected prepared) formed).assignment = ((prefixSelected prepared).output formed).val := rfl

theorem common_future_is_justified {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (formed : Identity (prefixOpening prepared)) :
    transmittedState (prefixSelected prepared) formed = (prefixOpening prepared).next :=
  transmittedState_exact _ _ (selectedPrefixTransmits prepared formed)

theorem growing_formed_carrier (count : Nat) :
    (relationalProfileFiniteCarrier (production count).history.roles).frontier.length = 2 ^ (count + 1) :=
  constituted_width count

theorem actual_output_image_width (count : Nat) :
    (composedRegime (production count).comparisons).frontier.length = 2 := produced_width count

theorem both_behaviours_for_every_positive_prefix (count : Nat) :
    (localRegime (prefixSelected (initialPrepared (count + 1)))
      (selectedPrefixEquality (initialPrepared (count + 1)))).frontier.length = 1 ∧
    separatingCount (production (count + 1)).comparisons = 1 := family_has_both_behaviours count

theorem fibres_are_values_not_status_labels (count : Nat)
    (p q : RelationalOccurrenceProfile (production count).history.roles) :
    (composedRegime (production count).comparisons).carry p =
        (composedRegime (production count).comparisons).carry q ↔
      (production count).history.output p = (production count).history.output q :=
  composed_fibres _ p q

theorem admission_consumes_preservation (count : Nat) (value : OutputImage (production count).history) :
    AcceptedStoredTuple (production count).history value.val := image_values_accepted count value

theorem execution_transport_first_return {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) (head : LocalProduction left) :
    (openingExecutionTransport same).backward ((openingExecutionTransport same).forward head) = head :=
  openingExecutionTransport_round_trip same head

theorem execution_transport_second_return {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) (head : LocalProduction right) :
    (openingExecutionTransport same).forward ((openingExecutionTransport same).backward head) = head :=
  openingExecutionTransport_return same head

end UnboundedMixedExecutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms UnboundedMixedExecutionRegression.actual_prefix_selection
#print axioms UnboundedMixedExecutionRegression.actual_terminal_selection
#print axioms UnboundedMixedExecutionRegression.actual_search_changes_status
#print axioms UnboundedMixedExecutionRegression.common_future_reads_produced_assignment
#print axioms UnboundedMixedExecutionRegression.common_future_is_justified
#print axioms UnboundedMixedExecutionRegression.growing_formed_carrier
#print axioms UnboundedMixedExecutionRegression.actual_output_image_width
#print axioms UnboundedMixedExecutionRegression.both_behaviours_for_every_positive_prefix
#print axioms UnboundedMixedExecutionRegression.fibres_are_values_not_status_labels
#print axioms UnboundedMixedExecutionRegression.admission_consumes_preservation
#print axioms UnboundedMixedExecutionRegression.execution_transport_first_return
#print axioms UnboundedMixedExecutionRegression.execution_transport_second_return
/- AXIOM_AUDIT_END -/
