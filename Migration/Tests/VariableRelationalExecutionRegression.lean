import RelationalPerimeter

namespace VariableRelationalExecutionRegression
open ConstitutiveSearch ConstitutiveSearch.EndogenousDecomposition
open VariableExecution VariableExecution.MixedExample

theorem width_variation : firstRegime.frontier.length = 1 ∧
    secondRegime.frontier.length = 2 ∧ mixedRegime.frontier.length = 2 :=
  ⟨first_width, second_width, mixed_width⟩

theorem unchanged_sources : profiles.frontier.length = 4 ∧
    identity first false ≠ identity first true ∧
    identity second false ≠ identity second true :=
  ⟨profile_width, source_distinct first, source_distinct second⟩

theorem transmitted_source :
    first.next.assignment = (executeOpening first).leftOutput.val :=
  production_transmits_output.1

theorem separating_action : produced (identity second false) ≠ produced (identity second true) :=
  second_outputs_distinct

theorem admission_consumes_preservation (value : Bool)
    (payload : Payload (identity second value))
    (accepted : Accept (identity second value) payload) :
    SAT.GeneratedStructuralBranchAccept first.next.operationalState
      (action (identity second value) payload) :=
  ((admission second).specification (produced (identity second value))).2.1
    (identity second value) rfl |>.2 payload accepted

theorem realization_returns_value
    (value : Extensive.ProducedOutputImage.Value (sourceCarrier second) produced) :
    (admittedOutputTransport second).backward ((admittedOutputTransport second).forward value) = value :=
  (admittedOutputTransport second).forwardBackward value

theorem no_extra_merging (p q : profiles.Identity) :
    mixedRegime.carry p = mixedRegime.carry q ↔ mixedOutput p = mixedOutput q :=
  mixed_fibres p q

theorem certificate_head_exact (input remaining : Nat) :
    (executeCausalOperationalExecutionHistory (remaining + 1)
      (initialThreadedConstitutiveStateFromInitialization (initializeConstitutiveHistory input))
      (initialOperationalPrefix input)
      (initialThreadedConstitutiveStateFromInitialization_fresh
        (initializeConstitutiveHistory input))).head? =
      some (executeCausalOperationalHead
        (initialThreadedConstitutiveStateFromInitialization (initializeConstitutiveHistory input))
        (initialOperationalPrefix input)
        (initialThreadedConstitutiveStateFromInitialization_fresh
          (initializeConstitutiveHistory input))) :=
  (publicExecutionConstitutionCertificate input).wholeHeadIsPrefixLocal remaining

theorem final_normalization_preserves_sat (profile : profiles.Identity) :
    SAT.GeneratedStructuralBranchAccept initialState.operationalState (finalOutput profile) :=
  finalOutput_accept profile

theorem final_width_is_not_a_label_count : finalRegime.frontier.length = 2 := final_width

/-- Closed public statements for the recovered constructions. -/
theorem public_mixed_widths :
    firstRegime.frontier.length = 1 ∧ secondRegime.frontier.length = 2 :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.mixed_execution_local_widths

-- Executable smoke check, separate from the proofs above.
#eval (firstRegime.frontier.length, secondRegime.frontier.length, mixedRegime.frontier.length)

end VariableRelationalExecutionRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms VariableRelationalExecutionRegression.width_variation
#print axioms VariableRelationalExecutionRegression.unchanged_sources
#print axioms VariableRelationalExecutionRegression.transmitted_source
#print axioms VariableRelationalExecutionRegression.separating_action
#print axioms VariableRelationalExecutionRegression.admission_consumes_preservation
#print axioms VariableRelationalExecutionRegression.realization_returns_value
#print axioms VariableRelationalExecutionRegression.no_extra_merging
#print axioms VariableRelationalExecutionRegression.certificate_head_exact
#print axioms VariableRelationalExecutionRegression.final_normalization_preserves_sat
#print axioms VariableRelationalExecutionRegression.final_width_is_not_a_label_count
#print axioms VariableRelationalExecutionRegression.public_mixed_widths
/- AXIOM_AUDIT_END -/
