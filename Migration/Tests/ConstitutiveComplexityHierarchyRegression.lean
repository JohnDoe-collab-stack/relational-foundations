import RelationalPerimeter

/-!
# Constitutive complexity hierarchy regression gate

These checks import only the public root.  They protect the actual dependency
chain: the executed role history builds one typed program; the complete
structural frontier is that program's exhaustive profile expansion; the same
program interprets every accepted expanded profile; and independent finite
addressing of those profiles has the exact exponential lower bound.
-/

namespace RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression

open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

set_option maxHeartbeats 800000

theorem programComesFromExecutedRoles (input : Nat) :
    ConstitutiveNormalizerProgram input =
      buildConstitutiveNormalizerProgram (PublicConstitutiveRoles input) :=
  rfl

theorem programInstructionCount (input : Nat) :
    (ConstitutiveNormalizerProgram input).instructionCount = input + 1 :=
  constitutive_program_instruction_count_exact input

theorem extensiveCarrierIsProgramExpansion (input : Nat) :
    structuralFrontier (PublicConstitutiveRoles input) =
      (ConstitutiveNormalizerProgram input).profileFrontier :=
  structural_frontier_is_program_expansion input

theorem programExpansionCardinality (input : Nat) :
    (ConstitutiveNormalizerProgram input).profileWidth = 2 ^ (input + 1) :=
  constitutive_program_profile_width_exact input

theorem programExpansionComplete (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile) :
    List.Mem profile (ConstitutiveNormalizerProgram input).profileFrontier :=
  constitutive_program_profiles_complete input profile

theorem programExpansionNoDuplicates (input : Nat) :
    (ConstitutiveNormalizerProgram input).profileFrontier.Nodup :=
  constitutive_program_profiles_nodup input

def everyProgramProfileAccepted (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile) :
    (ConstitutiveNormalizerProgram input).AcceptedProfilePayload profile :=
  constitutive_program_every_profile_accepted input profile

theorem everyInstructionDoublesTailExpansion
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (instruction : ConstitutiveNormalizerInstruction headRun)
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (tail : ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
      tailRoles) :
    (ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.step
        headRole instruction tail).profileFrontier =
      (tail.profileFrontier.map (fun rest =>
        (ConstitutiveNormalizerInstruction.Alternative.transformed
          (instruction := instruction), rest))) ++
        (tail.profileFrontier.map (fun rest =>
          (ConstitutiveNormalizerInstruction.Alternative.retained
            (instruction := instruction), rest))) :=
  ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.profileFrontier_step
    headRole instruction tail

/-- The two head alternatives are inhabitants of the family indexed by the
stored instruction, not free Boolean data attached only to the program depth. -/
theorem headAlternativesAreIndexedByStoredInstruction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    (instruction : ConstitutiveNormalizerInstruction headRun) :
    ConstitutiveNormalizerInstruction.Alternative.choice
        (ConstitutiveNormalizerInstruction.Alternative.transformed
          (instruction := instruction)) = false ∧
      ConstitutiveNormalizerInstruction.Alternative.choice
        (ConstitutiveNormalizerInstruction.Alternative.retained
          (instruction := instruction)) = true :=
  ⟨rfl, rfl⟩

theorem programProfilesRequireExponentialSlots (input : Nat)
    (addressing : IndependentProgramProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  independent_program_profile_addressing_requires_exponential_slots
    input addressing

theorem programInstructionCountEqualsCodeSize (input : Nat) :
    (ConstitutiveNormalizerProgram input).instructionCount =
      (ConstitutiveNormalizerProgram input).codeSize :=
  constitutive_program_instruction_count_eq_code_size input

theorem programCodeSize (input : Nat) :
    (ConstitutiveNormalizerProgram input).codeSize = input + 1 :=
  constitutive_program_code_size_exact input

theorem programReturnsExecutedCodes (input : Nat) :
    authoritativeNormalizerProgramReturnedCodes
        (ConstitutiveNormalizerProgram input)
        (buildConstitutiveNormalizerProgram_isAuthoritative
          (PublicConstitutiveRoles input)) =
      (executeConstitutiveResolution input).history.returnedCodes :=
  constitutive_program_returns_executed_codes input

theorem programInterpretsItsExpansion (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile)
    (payload : (ConstitutiveNormalizerProgram input).AcceptedProfilePayload
      profile) :
    canonicalProgramNormalizedPayloadToOperational
        (PublicConstitutiveRoles input)
        (interpretConstitutiveNormalizerProgramProfile
          (ConstitutiveNormalizerProgram input) profile payload) =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile
        (canonicalProgramAcceptedPayloadToStructural
          (PublicConstitutiveRoles input) profile payload) :=
  constitutive_program_profile_interpreter_exact input profile payload

theorem everyProgramStepConsumesStoredInstruction
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state stage}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (instruction : ConstitutiveNormalizerInstruction headRun)
    {tailRoles : ThreadedConstitutiveRoleHistory tailRun}
    (tail : ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
      tailRoles)
    (alternative : instruction.Alternative) (rest : tail.Profile)
    (headPayload : LocalAcceptedPayload headRun alternative.choice)
    (tailPayload : tail.AcceptedProfilePayload rest) :
    interpretConstitutiveNormalizerProgramProfile
        (ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram.step
          headRole instruction tail)
        (alternative, rest) (headPayload, tailPayload) =
      (interpretConstitutiveNormalizerInstruction headRun instruction
          alternative.choice headPayload,
        interpretConstitutiveNormalizerProgramProfile tail rest tailPayload) :=
  interpretConstitutiveNormalizerProgramProfile_step
    headRole instruction tail alternative rest headPayload tailPayload

/-- The interpreter's dependence on a raw instruction is semantic: differing
instruction actions force differing interpreted outputs on the same accepted
source payload. -/
theorem rawInterpreterSeparatesDifferentInstructionActions
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (first second : ConstitutiveNormalizerInstruction run)
    (payload : LocalAcceptedPayload run false)
    (different :
      (first.toAcceptingTransport run).map
          (leftPayloadAtScheduleSource run payload).1 ≠
        (second.toAcceptingTransport run).map
          (leftPayloadAtScheduleSource run payload).1) :
    (interpretConstitutiveNormalizerInstruction run first false payload).1 ≠
      (interpretConstitutiveNormalizerInstruction run second false payload).1 :=
  interpretConstitutiveNormalizerInstruction_sensitive
    run first second payload different

theorem authoritativeInstructionProjectsToExecutedView
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      ExecutedExtensionalSeparator.executedTransportProjection run
        ((authoritativeNormalizerInstruction run).toAcceptingTransport run) :=
  executed_extensional_view_is_authoritative_instruction_projection run

theorem projectedViewDoesNotDetermineAuthoritativeAction
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ConstitutiveSearch.ActionFactorsThrough
      (ExecutedExtensionalSeparator.executedTransportProjection run)
      (ExecutedExtensionalSeparator.executedTransportAction run) :=
  executed_state_width_view_does_not_determine_total_action run

/-- The collision statement itself, not only its proof, is anchored at the
authoritative instruction returned by the execution. -/
theorem authoritativeInstructionHasTypedProjectionCollision
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ∃ comparison argument,
      ExecutedExtensionalSeparator.executedTransportProjection run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run) =
        ExecutedExtensionalSeparator.executedTransportProjection run comparison ∧
      ExecutedExtensionalSeparator.executedTransportAction run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run)
          argument ≠
        ExecutedExtensionalSeparator.executedTransportAction run
          comparison argument :=
  authoritative_instruction_has_projection_collision run

theorem instrumentedWorkRemainsSeparate (input : Nat) :
    (executeConstitutiveResolution input).instrumentedWork ≤
      resolutionInstrumentedPolynomial.eval input :=
  constitutive_normalizer_instrumented_work_bound input

end RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programInstructionCount
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programComesFromExecutedRoles
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.extensiveCarrierIsProgramExpansion
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programExpansionCardinality
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programExpansionComplete
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programExpansionNoDuplicates
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.everyProgramProfileAccepted
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.everyInstructionDoublesTailExpansion
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.headAlternativesAreIndexedByStoredInstruction
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programProfilesRequireExponentialSlots
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programInstructionCountEqualsCodeSize
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programCodeSize
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programReturnsExecutedCodes
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.programInterpretsItsExpansion
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.everyProgramStepConsumesStoredInstruction
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.rawInterpreterSeparatesDifferentInstructionActions
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.authoritativeInstructionProjectsToExecutedView
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.authoritativeInstructionHasTypedProjectionCollision
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.projectedViewDoesNotDetermineAuthoritativeAction
#print axioms RelationalPerimeter.Tests.ConstitutiveComplexityHierarchyRegression.instrumentedWorkRemainsSeparate
/- AXIOM_AUDIT_END -/
