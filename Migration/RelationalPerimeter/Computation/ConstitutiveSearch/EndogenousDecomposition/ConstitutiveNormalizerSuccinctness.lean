import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAccounting

/-!
# Constitutive normalizer succinctness

The public execution constitutes an exact Boolean structural-profile carrier.
Any interface retaining those profiles as independently addressable cases needs
at least `2^(input+1)` finite slots.  The same execution produces an
authoritative normalizer program with exactly `input+1` transport atoms, and
that program acts on every accepted structural payload exactly as the existing
normalizer does.

The comparison is deliberately typed and metric-specific.  It establishes a
succinct executed representation relative to independent finite profile
addressing; it does not claim a universal lower bound for every representation,
nor a general time- or memory-complexity separation.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

set_option maxHeartbeats 800000

/-- The unique public dependent role history for one input. -/
abbrev PublicConstitutiveRoles (input : Nat) :=
  (executeConstitutiveResolution input).feedbackRoleHistory

/-- The authoritative raw program constructed from the public execution. -/
abbrev PublicConstitutiveNormalizerProgram (input : Nat) :=
  buildConstitutiveNormalizerProgram (PublicConstitutiveRoles input)

/-- Closed certificate joining the exact structural case space, its finite
independent-addressing lower bound, and the authoritative executed normalizer.
The constructor is private so clients consume the built witness rather than
assembling causal fields independently. -/
structure ConstitutiveNormalizerSuccinctness (input : Nat) : Type 3 where
  private mk ::
  program :
    AuthoritativeConstitutiveNormalizerProgram
      (PublicConstitutiveRoles input)
  stageCountExact :
    operationalStageCount (PublicConstitutiveRoles input) = input + 1
  structuralCaseCountExact :
    structuralWidth (PublicConstitutiveRoles input) = 2 ^ (input + 1)
  pendingCaseCountExact :
    pendingWidth (PublicConstitutiveRoles input) = 2 ^ (input + 1)
  retainedCaseCountExact :
    executedWidth (PublicConstitutiveRoles input) = 1
  structuralComplete :
    forall profile,
      List.Mem profile (structuralFrontier (PublicConstitutiveRoles input))
  structuralNoDuplicates :
    (structuralFrontier (PublicConstitutiveRoles input)).Nodup
  pendingComplete :
    forall profile,
      List.Mem profile (pendingFrontier (PublicConstitutiveRoles input))
  pendingNoDuplicates :
    (pendingFrontier (PublicConstitutiveRoles input)).Nodup
  everyProfileAccepted :
    forall profile,
      StructuralAcceptedPayload (PublicConstitutiveRoles input) profile
  programInterpreterExact :
    forall profile payload,
      interpretConstitutiveNormalizerProgram program.program profile payload =
        normalizeStructuralAcceptedPayload
          (PublicConstitutiveRoles input) profile payload
  programReturnsExecutedCodes :
    authoritativeNormalizerProgramReturnedCodes
        program.program program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes
  programCodeSizeExact :
    program.program.codeSize = input + 1
  programCodeMetricExact :
    program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          program.program program.authoritative)
  returnedCodeAtomCountExact :
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          program.program program.authoritative) = input + 1
  independentAddressingLowerBound :
    forall addressing : IndependentProfileAddressing
        (PublicConstitutiveRoles input),
      2 ^ (input + 1) <= addressing.slotCount
  derivedWidthReadoutBound :
    WidthTraceAtMost 2
      (executedWidthTrace (PublicConstitutiveRoles input))
  instrumentedWorkBound :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input

/-- Construct the certificate entirely from the public execution. -/
def publicConstitutiveNormalizerSuccinctness
    (input : Nat) : ConstitutiveNormalizerSuccinctness input := by
  let run := executeConstitutiveResolution input
  let roles : ThreadedConstitutiveRoleHistory run.constitutiveFeedbackHistory :=
    run.feedbackRoleHistory
  let program := buildAuthoritativeConstitutiveNormalizerProgram roles
  have stageCount : operationalStageCount roles = input + 1 :=
    operationalStageCount_eq_historyCount roles
  have structuralCount : structuralWidth roles = 2 ^ (input + 1) :=
    Eq.trans (structuralWidth_eq_two_pow_stageCount roles)
      (congrArg (fun count => 2 ^ count) stageCount)
  have pendingCount : pendingWidth roles = 2 ^ (input + 1) :=
    Eq.trans (pendingWidth_eq_two_pow_stageCount roles)
      (congrArg (fun count => 2 ^ count) stageCount)
  refine
    { program := program
      stageCountExact := stageCount
      structuralCaseCountExact := structuralCount
      pendingCaseCountExact := pendingCount
      retainedCaseCountExact := executedWidth_eq_one roles
      structuralComplete := structuralFrontier_complete roles
      structuralNoDuplicates := structuralFrontier_nodup roles
      pendingComplete := pendingFrontier_complete roles
      pendingNoDuplicates := pendingFrontier_nodup roles
      everyProfileAccepted := everyStructuralObligationHasAcceptedPayload roles
      programInterpreterExact := ?_
      programReturnsExecutedCodes := ?_
      programCodeSizeExact := ?_
      programCodeMetricExact := ?_
      returnedCodeAtomCountExact := ?_
      independentAddressingLowerBound := ?_
      derivedWidthReadoutBound := executedWidthTrace_le_two roles
      instrumentedWorkBound := run.instrumentedWork_polynomial_bound }
  · intro profile payload
    exact interpretAuthoritativeConstitutiveNormalizerProgram_exact
      program.program program.authoritative profile payload
  · exact Eq.trans
      (authoritativeNormalizerProgramReturnedCodes_exact
        program.program program.authoritative)
      (congrArg SequentialHistory.returnedCodes
        run.historyFromCausalExecution.symm)
  · exact Eq.trans
      (buildConstitutiveNormalizerProgram_codeSize roles)
      stageCount
  · exact authoritativeNormalizerProgram_codeSize_eq_compiledLocalSize
      program.program program.authoritative
  · exact Eq.trans
      (authoritativeNormalizerProgram_compiledSize_eq_stageCount
        program.program program.authoritative)
      stageCount
  · intro addressing
    exact Eq.mp
      (congrArg (fun width => width <= addressing.slotCount)
        (congrArg (fun count => 2 ^ count) stageCount))
      (independentProfileAddressing_slots_ge_two_pow_stageCount addressing)

/-- The public program contains one instruction for each executed stage. -/
theorem public_constitutive_program_instructionCount_exact (input : Nat) :
    (PublicConstitutiveNormalizerProgram input).instructionCount = input + 1 :=
  Eq.trans
    (buildConstitutiveNormalizerProgram_instructionCount
      (PublicConstitutiveRoles input))
    (operationalStageCount_eq_historyCount (PublicConstitutiveRoles input))

/-- The complete structural carrier is literally the profile type generated
by the public program, rather than a parallel role-indexed construction. -/
theorem public_structural_frontier_is_program_expansion (input : Nat) :
    structuralFrontier (PublicConstitutiveRoles input) =
      (PublicConstitutiveNormalizerProgram input).profileFrontier :=
  rfl

/-- The public program's exhaustive profile expansion has exactly the claimed
exponential cardinality. -/
theorem public_constitutive_program_profileWidth_exact (input : Nat) :
    (PublicConstitutiveNormalizerProgram input).profileWidth =
      2 ^ (input + 1) :=
  Eq.trans
    (ConstitutiveNormalizerProgram.profileWidth_eq_two_pow_instructionCount
      (PublicConstitutiveNormalizerProgram input))
    (congrArg (fun count => 2 ^ count)
      (public_constitutive_program_instructionCount_exact input))

/-- Every profile of the public program occurs in its own exhaustive
expansion. -/
theorem public_constitutive_program_profiles_complete (input : Nat)
    (profile : (PublicConstitutiveNormalizerProgram input).Profile) :
    List.Mem profile
      (PublicConstitutiveNormalizerProgram input).profileFrontier :=
  ConstitutiveNormalizerProgram.profileFrontier_complete
    (PublicConstitutiveNormalizerProgram input) profile

/-- The public program's exhaustive expansion contains no duplicate profile. -/
theorem public_constitutive_program_profiles_nodup (input : Nat) :
    (PublicConstitutiveNormalizerProgram input).profileFrontier.Nodup :=
  ConstitutiveNormalizerProgram.profileFrontier_nodup
    (PublicConstitutiveNormalizerProgram input)

/-- Every profile produced by the public program has an accepted payload in
the payload family indexed by that exact program. -/
def public_constitutive_program_everyProfileAccepted (input : Nat)
    (profile : (PublicConstitutiveNormalizerProgram input).Profile) :
    (PublicConstitutiveNormalizerProgram input).AcceptedProfilePayload profile :=
  everyCanonicalProgramProfileHasAcceptedPayload
    (PublicConstitutiveRoles input) profile

/-- The interpreter of the same program realizes the canonical normalizer on
each of the profiles expanded by that program. -/
theorem public_constitutive_program_profile_interpreter_exact (input : Nat)
    (profile : (PublicConstitutiveNormalizerProgram input).Profile)
    (payload : (PublicConstitutiveNormalizerProgram input).AcceptedProfilePayload
      profile) :
    canonicalProgramNormalizedPayloadToOperational
        (PublicConstitutiveRoles input)
        (interpretConstitutiveNormalizerProgramProfile
          (PublicConstitutiveNormalizerProgram input) profile payload) =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile
        (canonicalProgramAcceptedPayloadToStructural
          (PublicConstitutiveRoles input) profile payload) :=
  interpretBuiltConstitutiveNormalizerProgramProfile_exact
    (PublicConstitutiveRoles input) profile payload

/-- Any interface that keeps every profile of the public program independently
addressable needs at least `2^(input+1)` slots. -/
theorem public_independent_program_profile_slots_exponential (input : Nat)
    (addressing : IndependentProgramProfileAddressing
      (PublicConstitutiveRoles input)
      (PublicConstitutiveNormalizerProgram input)) :
    2 ^ (input + 1) <= addressing.slotCount := by
  rw [<- public_constitutive_program_instructionCount_exact input]
  exact
    independentProgramProfileAddressing_slots_ge_two_pow_instructionCount
      addressing

/-- The canonical public program stores exactly one transport atom per typed
instruction.  Both metrics are computed from the same program value. -/
theorem public_constitutive_program_instructionCount_eq_codeSize (input : Nat) :
    (PublicConstitutiveNormalizerProgram input).instructionCount =
      (PublicConstitutiveNormalizerProgram input).codeSize :=
  Eq.trans
    (buildConstitutiveNormalizerProgram_instructionCount
      (PublicConstitutiveRoles input))
    (buildConstitutiveNormalizerProgram_codeSize
      (PublicConstitutiveRoles input)).symm

/-- Direct code-size readout on the same public program whose profiles are
expanded above. -/
theorem public_constitutive_program_codeSize_exact (input : Nat) :
    (PublicConstitutiveNormalizerProgram input).codeSize = input + 1 :=
  Eq.trans
    (buildConstitutiveNormalizerProgram_codeSize
      (PublicConstitutiveRoles input))
    (operationalStageCount_eq_historyCount (PublicConstitutiveRoles input))

/-- Erasing the same canonical program yields exactly the codes returned by
the public execution. -/
theorem public_constitutive_program_returns_executed_codes (input : Nat) :
    authoritativeNormalizerProgramReturnedCodes
        (PublicConstitutiveNormalizerProgram input)
        (buildConstitutiveNormalizerProgram_isAuthoritative
          (PublicConstitutiveRoles input)) =
      (executeConstitutiveResolution input).history.returnedCodes :=
  Eq.trans
    (authoritativeNormalizerProgramReturnedCodes_exact
      (PublicConstitutiveNormalizerProgram input)
      (buildConstitutiveNormalizerProgram_isAuthoritative
        (PublicConstitutiveRoles input)))
    (congrArg SequentialHistory.returnedCodes
      (executeConstitutiveResolution input).historyFromCausalExecution.symm)

/-- Exact raw-program metric: one stored transport atom per public stage. -/
theorem public_constitutive_normalizer_programCodeSize_exact (input : Nat) :
    (publicConstitutiveNormalizerSuccinctness input).program.program.codeSize =
      input + 1 :=
  (publicConstitutiveNormalizerSuccinctness input).programCodeSizeExact

/-- The raw dependent-program metric agrees exactly with `compiledLocalSize`
after authoritative erasure. -/
theorem public_constitutive_normalizer_codeMetric_exact (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  (publicConstitutiveNormalizerSuccinctness input).programCodeMetricExact

/-- Public lower bound for every independently addressing representation of
the exact structural profiles. -/
theorem public_independent_profile_slots_exponential (input : Nat)
    (addressing : IndependentProfileAddressing
      (PublicConstitutiveRoles input)) :
    2 ^ (input + 1) <= addressing.slotCount :=
  (publicConstitutiveNormalizerSuccinctness input).independentAddressingLowerBound
    addressing

/-- Exact code-atom size of the public authoritative normalizer. -/
theorem public_constitutive_normalizer_codeSize_exact (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) =
      input + 1 :=
  (publicConstitutiveNormalizerSuccinctness input).returnedCodeAtomCountExact

/-- The public program computes the canonical normalizer for every profile and
accepted payload. -/
theorem public_constitutive_normalizer_interpreter_exact (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input))
    (payload : StructuralAcceptedPayload
      (PublicConstitutiveRoles input) profile) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    interpretConstitutiveNormalizerProgram certificate.program.program
        profile payload =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile payload :=
  (publicConstitutiveNormalizerSuccinctness input).programInterpreterExact
    profile payload

/-- The program erases to the exact code list returned by the public run. -/
theorem public_constitutive_normalizer_returns_executed_codes (input : Nat) :
    let certificate := publicConstitutiveNormalizerSuccinctness input
    authoritativeNormalizerProgramReturnedCodes
        certificate.program.program certificate.program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes :=
  (publicConstitutiveNormalizerSuccinctness input).programReturnsExecutedCodes

/-- The existing instrumented polynomial bound is carried by the same closed
public certificate; it is not inferred from the code-size comparison. -/
theorem public_constitutive_normalizer_instrumentedWork_bound (input : Nat) :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input :=
  (publicConstitutiveNormalizerSuccinctness input).instrumentedWorkBound

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicConstitutiveRoles
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicConstitutiveNormalizerProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicConstitutiveNormalizerSuccinctness
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_instructionCount_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_structural_frontier_is_program_expansion
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_profileWidth_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_profiles_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_profiles_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_everyProfileAccepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_profile_interpreter_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_independent_program_profile_slots_exponential
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_instructionCount_eq_codeSize
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_codeSize_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_program_returns_executed_codes
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_programCodeSize_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_codeMetric_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_independent_profile_slots_exponential
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_codeSize_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_interpreter_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_returns_executed_codes
#print axioms ConstitutiveSearch.EndogenousDecomposition.public_constitutive_normalizer_instrumentedWork_bound
/- AXIOM_AUDIT_END -/
