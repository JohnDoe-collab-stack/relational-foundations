import RelationalPerimeter

/-!
# Regression gate for constitutive normalizer succinctness

These checks use only the public root.  They protect the exact index shared by
the structural profiles and the executed program, the authority proof for the
stored codes, the pointwise interpreter theorem, the exact code erasure, and
the representation-relative exponential addressing lower bound.
-/

namespace Tests.ConstitutiveNormalizerSuccinctnessRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

def certificateZero : ConstitutiveNormalizerSuccinctnessEvidence 0 :=
  constitutiveNormalizerSuccinctnessEvidence 0

theorem publicStageCountZero :
    certificateZero.stageCountExact =
      (show operationalStageCount (PublicConstitutiveRoles 0) = 1 from rfl) := by
  rfl

theorem publicStructuralCaseCountZero :
    structuralWidth (PublicConstitutiveRoles 0) = 2 := by
  exact certificateZero.structuralCaseCountExact

theorem publicPendingCaseCountZero :
    pendingWidth (PublicConstitutiveRoles 0) = 2 := by
  exact certificateZero.pendingCaseCountExact

theorem publicRetainedCaseCountZero :
    executedWidth (PublicConstitutiveRoles 0) = 1 :=
  certificateZero.retainedCaseCountExact

theorem publicStructuralProfilesComplete (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input)) :
    List.Mem profile (structuralFrontier (PublicConstitutiveRoles input)) :=
  (constitutiveNormalizerSuccinctnessEvidence input).structuralComplete profile

theorem publicStructuralProfilesNoDuplicates (input : Nat) :
    (structuralFrontier (PublicConstitutiveRoles input)).Nodup :=
  (constitutiveNormalizerSuccinctnessEvidence input).structuralNoDuplicates

theorem publicPendingProfilesComplete (input : Nat)
    (profile : PendingOperationalObligation (PublicConstitutiveRoles input)) :
    List.Mem profile (pendingFrontier (PublicConstitutiveRoles input)) :=
  (constitutiveNormalizerSuccinctnessEvidence input).pendingComplete profile

theorem publicPendingProfilesNoDuplicates (input : Nat) :
    (pendingFrontier (PublicConstitutiveRoles input)).Nodup :=
  (constitutiveNormalizerSuccinctnessEvidence input).pendingNoDuplicates

def publicAcceptedPayload (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input)) :
    StructuralAcceptedPayload (PublicConstitutiveRoles input) profile :=
  (constitutiveNormalizerSuccinctnessEvidence input).everyProfileAccepted profile

theorem publicProgramIsAuthoritative (input : Nat) :
    (constitutiveNormalizerSuccinctnessEvidence input).program.program.IsAuthoritative :=
  (constitutiveNormalizerSuccinctnessEvidence input).program.authoritative

theorem genericIndependentAddressingBound
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (addressing :
      ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing roles) :
    structuralWidth roles <= addressing.slotCount :=
  independentProfileAddressing_slots_ge_structuralWidth addressing

theorem canonicalInstructionStoresReturnedCode
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (authoritativeNormalizerInstruction run).code = stage.execution.code :=
  rfl

theorem scheduledSourceUsesTheSameDiscovery
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.schedule.entry.source =
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var false stage.discovery.fresh :=
  scheduledSource_from_discovery_exact run

theorem scheduledTargetUsesTheSameDiscovery
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stage.schedule.entry.target =
      (constructStage (depth + 1)).operationalRoot.child
        stage.discovery.var true stage.discovery.fresh :=
  scheduledTarget_from_discovery_exact run

theorem leftInterpreterComputesTheStoredCode
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run)
    (payload : LocalAcceptedPayload run false) :
    interpretConstitutiveNormalizerInstruction run instruction false payload =
      let source := leftPayloadAtScheduleSource run payload
      let transport := instruction.code.eval
          (generatedStructuralFlipAtAction
            (distinctGrowingDiscoveryFormula
              (constructStage (depth + 1)).searchIndex)
            stage.schedule.entry.var)
      scheduleTargetAsRetainedPayload run
        ⟨transport.map source.1,
          transport.preservesAccept source.1 source.2⟩ :=
  rfl

theorem rightInterpreterRetainsItsPayload
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage)
    (instruction : ConstitutiveNormalizerInstruction run)
    (payload : LocalAcceptedPayload run true) :
    interpretConstitutiveNormalizerInstruction run instruction true payload =
      payload :=
  rfl

theorem publicProgramInterpretsEveryProfile (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input))
    (payload : StructuralAcceptedPayload (PublicConstitutiveRoles input) profile) :
    interpretConstitutiveNormalizerProgram
        (constitutiveNormalizerSuccinctnessEvidence input).program.program
        profile payload =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile payload :=
  constitutive_normalizer_interpreter_exact input profile payload

theorem publicProgramReturnsExactExecutedCodes (input : Nat) :
    authoritativeNormalizerProgramReturnedCodes
        (constitutiveNormalizerSuccinctnessEvidence input).program.program
        (constitutiveNormalizerSuccinctnessEvidence input).program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes :=
  constitutive_normalizer_returns_executed_codes input

theorem publicProgramAtomCountIsLinear (input : Nat) :
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          (constitutiveNormalizerSuccinctnessEvidence input).program.program
          (constitutiveNormalizerSuccinctnessEvidence input).program.authoritative) =
      input + 1 :=
  constitutive_normalizer_code_size_exact input

theorem publicRawProgramAtomCountIsLinear (input : Nat) :
    (constitutiveNormalizerSuccinctnessEvidence input).program.program.codeSize =
      input + 1 :=
  constitutive_normalizer_program_code_size_exact input

theorem rawAndErasedProgramMetricsAgree (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  constitutive_normalizer_code_metric_exact input

theorem independentAddressingCannotUseFewerSlots (input : Nat)
    (addressing : IndependentProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  independent_profile_addressing_requires_exponential_slots input addressing

theorem derivedWidthReadoutRemainsBounded (input : Nat) :
    WidthTraceAtMost 2 (executedWidthTrace (PublicConstitutiveRoles input)) :=
  (constitutiveNormalizerSuccinctnessEvidence input).derivedWidthReadoutBound

theorem publicInstrumentedWorkBoundRemainsSeparate (input : Nat) :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input :=
  constitutive_normalizer_instrumented_work_bound input

theorem priorNonfactorizationResultRemainsAvailable (input : Nat) :
    ¬ ActionFactorsThrough
      (ExecutedExtensionalSeparator.executedTransportProjection
        (nextDiscoveryCommonOrigin input).run)
      (ExecutedExtensionalSeparator.executedTransportAction
        (nextDiscoveryCommonOrigin input).run) :=
  executed_state_width_view_does_not_determine_total_action
    (nextDiscoveryCommonOrigin input).run

end Tests.ConstitutiveNormalizerSuccinctnessRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.certificateZero
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicStageCountZero
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicStructuralCaseCountZero
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicPendingCaseCountZero
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicRetainedCaseCountZero
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicStructuralProfilesComplete
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicStructuralProfilesNoDuplicates
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicPendingProfilesComplete
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicPendingProfilesNoDuplicates
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicAcceptedPayload
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicProgramIsAuthoritative
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.genericIndependentAddressingBound
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.canonicalInstructionStoresReturnedCode
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.scheduledSourceUsesTheSameDiscovery
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.scheduledTargetUsesTheSameDiscovery
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.leftInterpreterComputesTheStoredCode
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.rightInterpreterRetainsItsPayload
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicProgramInterpretsEveryProfile
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicProgramReturnsExactExecutedCodes
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicProgramAtomCountIsLinear
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicRawProgramAtomCountIsLinear
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.rawAndErasedProgramMetricsAgree
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.independentAddressingCannotUseFewerSlots
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.derivedWidthReadoutRemainsBounded
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.publicInstrumentedWorkBoundRemainsSeparate
#print axioms Tests.ConstitutiveNormalizerSuccinctnessRegression.priorNonfactorizationResultRemainsAvailable
/- AXIOM_AUDIT_END -/
