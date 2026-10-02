import Constitution.ExitDiagnostics
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Autonomous non-vacuous instance -/

namespace Example

inductive Explicit where
  | first
  | second
  | third
  | fourth

inductive Implicit where
  | first
  | second
  | third
  | fourth

inductive Difference where
  | first
  | second
  | third
  | fourth

inductive Provenance : Difference → Type
  | first : Provenance .first
  | second : Provenance .second
  | third : Provenance .third
  | fourth : Provenance .fourth

inductive Compatible : Implicit → Explicit → Type
  | internalFirst : Compatible .first .first
  | internalSecond : Compatible .second .second
  | internalThird : Compatible .third .third
  | internalFourth : Compatible .fourth .fourth
  | firstToSecond : Compatible .first .second
  | secondToThird : Compatible .second .third
  | thirdToFourth : Compatible .third .fourth
  | fourthToFirst : Compatible .fourth .first

def firstNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .first
    implicit := .first
    difference := .first
    provenance := .first
    internallyCompatible := .internalFirst }

def secondNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .second
    implicit := .second
    difference := .second
    provenance := .second
    internallyCompatible := .internalSecond }

def thirdNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .third
    implicit := .third
    difference := .third
    provenance := .third
    internallyCompatible := .internalThird }

def fourthNode :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  { explicit := .fourth
    implicit := .fourth
    difference := .fourth
    provenance := .fourth
    internallyCompatible := .internalFourth }

def examplePerimeter : PerimeterSpine Compatible firstNode :=
  @PerimeterSpine.advance _ _ _ _ _ firstNode secondNode
    (.firstToSecond : Compatible .first .second)
    (@PerimeterSpine.advance _ _ _ _ _ secondNode thirdNode
      (.secondToThird : Compatible .second .third)
      (@PerimeterSpine.advance _ _ _ _ _ thirdNode fourthNode
        (.thirdToFourth : Compatible .third .fourth)
        (.boundary fourthNode)))

def examplePerimeterPositive : NonClosingPosition examplePerimeter := .here

def leftPole (_ : Difference) : Bool := false

def rightPole (_ : Difference) : Bool := true

def rejectFalseEqualsTrue : false = true → False := by
  intro equality
  cases equality

def examplePresentation : CircularPresentation :=
  { Explicit := Explicit
    Implicit := Implicit
    Compatible := Compatible
    Difference := Difference
    Provenance := Provenance
    initialNode := firstNode
    perimeter := examplePerimeter
    perimeterPositive := examplePerimeterPositive
    finalJunction := Compatible.fourthToFirst
    Endpoint := Bool
    leftEndpoint := false
    rightEndpoint := true
    leftPole := leftPole
    rightPole := rightPole
    initialLeftPole := rfl
    initialRightPole := rfl
    TotalLoop := PLift (false = true)
    closeFromIdentification := fun equality => ⟨equality⟩
    loopContractsInitialDifference := fun loop => loop.down
    rejectInitialContraction := fun _ equality => rejectFalseEqualsTrue equality }

/-! ### Experimental permutation separator -/

/- The three inhabited non-closing positions of `examplePerimeter`. -/
def exampleP1 :
    NonClosingPosition examplePresentation.perimeter :=
  .here

def exampleP2 :
    NonClosingPosition examplePresentation.perimeter :=
  .later .here

def exampleP3 :
    NonClosingPosition examplePresentation.perimeter :=
  .later (.later .here)

/- The carrier keeps the three canonical located steps but deliberately
   permutes the first two occurrences. -/
def permutedExampleTrace :
    SemanticTrace examplePresentation :=
  { steps :=
      [ positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP2,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP1,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP3 ] }

def permutedExampleRealize :
    NonClosingPosition examplePresentation.perimeter →
      permutedExampleTrace.Occurrence
  | .here => ⟨1, by decide⟩
  | .later .here => ⟨0, by decide⟩
  | .later (.later .here) => ⟨2, by decide⟩
  | .later (.later (.later impossible)) => nomatch impossible

def permutedExampleDecode :
    permutedExampleTrace.Occurrence →
      NonClosingPosition examplePresentation.perimeter :=
  fun occurrence =>
    if occurrence.val = 0 then exampleP2
    else if occurrence.val = 1 then exampleP1
    else exampleP3

theorem permutedExampleDecode_realize :
    (position : NonClosingPosition examplePresentation.perimeter) →
      permutedExampleDecode (permutedExampleRealize position) = position
  | .here => by
      change (if (1 : Nat) = 0 then exampleP2
        else if (1 : Nat) = 1 then exampleP1 else exampleP3) = exampleP1
      rfl
  | .later .here => by
      change (if (0 : Nat) = 0 then exampleP2
        else if (0 : Nat) = 1 then exampleP1 else exampleP3) = exampleP2
      rfl
  | .later (.later .here) => by
      change (if (2 : Nat) = 0 then exampleP2
        else if (2 : Nat) = 1 then exampleP1 else exampleP3) = exampleP3
      rfl
  | .later (.later (.later impossible)) => nomatch impossible

theorem permutedExampleRealize_injective :
    Function.Injective permutedExampleRealize := by
  intro first second equality
  have decoded := congrArg permutedExampleDecode equality
  exact (permutedExampleDecode_realize first).symm.trans
    (decoded.trans (permutedExampleDecode_realize second))

def permutedExampleAgreement :
    (position : NonClosingPosition examplePresentation.perimeter) →
      LocatedRequirementAgreement examplePresentation position
        (permutedExampleTrace.locatedStep
          (permutedExampleRealize position))
  | .here => ⟨rfl⟩
  | .later .here => ⟨rfl⟩
  | .later (.later .here) => ⟨rfl⟩
  | .later (.later (.later impossible)) => nomatch impossible

/- Exact and injective local realization survives the explicit permutation. -/
def permutedExampleRealization :
    SemanticExactNonClosingRealization
      examplePresentation permutedExampleTrace :=
  { realize := permutedExampleRealize
    realize_injective := permutedExampleRealize_injective
    agreement := permutedExampleAgreement }

@[simp] theorem permutedExample_realizes_p1_at_one :
    (permutedExampleRealization.realize exampleP1).val = 1 :=
  rfl

@[simp] theorem permutedExample_realizes_p2_at_zero :
    (permutedExampleRealization.realize exampleP2).val = 0 :=
  rfl

@[simp] theorem permutedExample_realizes_p3_at_two :
    (permutedExampleRealization.realize exampleP3).val = 2 :=
  rfl

theorem permutedExample_reverses_first_two :
    (permutedExampleRealization.realize exampleP2).val <
      (permutedExampleRealization.realize exampleP1).val := by
  change 0 < 1
  exact Nat.zero_lt_succ 0

def exampleP1_precedes_exampleP2 :
    NonClosingPrecedes
      examplePresentation.perimeter
      exampleP1
      exampleP2 :=
  .here_later .here

/- The explicit permutation is locally exact and injective, but it does not
   preserve the structural order of the first two perimeter requirements. -/
theorem permutedExample_not_order_preserved :
    ¬ SemanticOrderPreserved permutedExampleRealization := by
  intro preserved
  have forward :=
    preserved exampleP1 exampleP2 exampleP1_precedes_exampleP2
  change
    (permutedExampleRealization.realize exampleP1).val <
      (permutedExampleRealization.realize exampleP2).val
    at forward
  exact Nat.lt_asymm forward permutedExample_reverses_first_two

/-! ### Experimental interleaving separator -/

/- These two extra occurrences are genuine locally generated steps beyond the
   perimeter.  They are constructed without a `History`, so their insertion in
   the semantic trace does not reintroduce global composability. -/
def exampleExtra1Source :
    PositiveConstitution examplePresentation :=
  perimeterEndpoint examplePresentation

def exampleExtra1 :
    History.LocatedStep (@GeneratedStep examplePresentation) :=
  ⟨exampleExtra1Source,
    canonicalTarget exampleExtra1Source,
    generatedStepOfFreeK exampleExtra1Source⟩

def exampleExtra2Source :
    PositiveConstitution examplePresentation :=
  canonicalTarget exampleExtra1Source

def exampleExtra2 :
    History.LocatedStep (@GeneratedStep examplePresentation) :=
  ⟨exampleExtra2Source,
    canonicalTarget exampleExtra2Source,
    generatedStepOfFreeK exampleExtra2Source⟩

/- The required non-closing steps remain in canonical order while two genuine
   locally valid generated steps are interleaved between them. -/
def interleavedExampleTrace :
    SemanticTrace examplePresentation :=
  { steps :=
      [ positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP1,
        exampleExtra1,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP2,
        exampleExtra2,
        positionLocatedStep examplePresentation
          FreeConstitution.root BoundaryDifference.initial exampleP3 ] }

def interleavedExampleRealize :
    NonClosingPosition examplePresentation.perimeter →
      interleavedExampleTrace.Occurrence
  | .here => ⟨0, by decide⟩
  | .later .here => ⟨2, by decide⟩
  | .later (.later .here) => ⟨4, by decide⟩
  | .later (.later (.later impossible)) => nomatch impossible

def interleavedExampleDecode :
    interleavedExampleTrace.Occurrence →
      NonClosingPosition examplePresentation.perimeter :=
  fun occurrence =>
    if occurrence.val = 0 then exampleP1
    else if occurrence.val = 2 then exampleP2
    else exampleP3

theorem interleavedExampleDecode_realize :
    (position : NonClosingPosition examplePresentation.perimeter) →
      interleavedExampleDecode (interleavedExampleRealize position) = position
  | .here => by
      change (if (0 : Nat) = 0 then exampleP1
        else if (0 : Nat) = 2 then exampleP2 else exampleP3) = exampleP1
      rfl
  | .later .here => by
      change (if (2 : Nat) = 0 then exampleP1
        else if (2 : Nat) = 2 then exampleP2 else exampleP3) = exampleP2
      rfl
  | .later (.later .here) => by
      change (if (4 : Nat) = 0 then exampleP1
        else if (4 : Nat) = 2 then exampleP2 else exampleP3) = exampleP3
      rfl
  | .later (.later (.later impossible)) => nomatch impossible

theorem interleavedExampleRealize_injective :
    Function.Injective interleavedExampleRealize := by
  intro first second equality
  have decoded := congrArg interleavedExampleDecode equality
  exact (interleavedExampleDecode_realize first).symm.trans
    (decoded.trans (interleavedExampleDecode_realize second))

def interleavedExampleAgreement :
    (position : NonClosingPosition examplePresentation.perimeter) →
      LocatedRequirementAgreement examplePresentation position
        (interleavedExampleTrace.locatedStep
          (interleavedExampleRealize position))
  | .here => ⟨rfl⟩
  | .later .here => ⟨rfl⟩
  | .later (.later .here) => ⟨rfl⟩
  | .later (.later (.later impossible)) => nomatch impossible

/- Exact local realization survives the interleaving of two additional valid
   generated steps. -/
def interleavedExampleRealization :
    SemanticExactNonClosingRealization
      examplePresentation interleavedExampleTrace :=
  { realize := interleavedExampleRealize
    realize_injective := interleavedExampleRealize_injective
    agreement := interleavedExampleAgreement }

@[simp] theorem interleavedExample_realizes_p1_at_zero :
    (interleavedExampleRealization.realize exampleP1).val = 0 :=
  rfl

@[simp] theorem interleavedExample_realizes_p2_at_two :
    (interleavedExampleRealization.realize exampleP2).val = 2 :=
  rfl

@[simp] theorem interleavedExample_realizes_p3_at_four :
    (interleavedExampleRealization.realize exampleP3).val = 4 :=
  rfl

/- The interleaved realization preserves every structural precedence relation
   of the three non-closing requirements.  No contiguity condition is used. -/
def interleavedExample_order_preserved :
    SemanticOrderPreserved interleavedExampleRealization := by
  intro first second precedes
  cases precedes with
  | here_later position =>
      cases position with
      | here =>
          change 0 < 2
          exact Nat.zero_lt_succ 1
      | later position =>
          cases position with
          | here =>
              change 0 < 4
              exact Nat.zero_lt_succ 3
          | later impossible => nomatch impossible
  | later_later precedes =>
      cases precedes with
      | here_later position =>
          cases position with
          | here =>
              change 2 < 4
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
          | later impossible => nomatch impossible
      | later_later precedes =>
          cases precedes with
          | here_later impossible => nomatch impossible
          | later_later deeper => cases deeper


def exampleP1_next_exampleP2 :
    NonClosingNext
      examplePresentation.perimeter
      exampleP1
      exampleP2 :=
  .here_next

def exampleP2_next_exampleP3 :
    NonClosingNext
      examplePresentation.perimeter
      exampleP2
      exampleP3 :=
  .later_next .here_next

/- The extra occurrences at indices 1 and 3 are positionally between the
   canonically adjacent required occurrences. -/
def interleavedExample_extra1_between :
    interleavedExampleTrace.Between
      (interleavedExampleRealization.realize exampleP1)
      (interleavedExampleRealization.realize exampleP2) := by
  refine ⟨⟨1, by decide⟩, ?_, ?_⟩
  · change 0 < 1
    exact Nat.zero_lt_succ 0
  · change 1 < 2
    exact Nat.succ_lt_succ (Nat.zero_lt_succ 0)

def interleavedExample_extra2_between :
    interleavedExampleTrace.Between
      (interleavedExampleRealization.realize exampleP2)
      (interleavedExampleRealization.realize exampleP3) := by
  refine ⟨⟨3, by decide⟩, ?_, ?_⟩
  · change 2 < 3
    exact Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
  · change 3 < 4
    exact Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

/- `extra1` may be positioned between p1 and p2, but it cannot be exactly an
   occurrence of a generated constitutive bridge between these canonically
   adjacent requirements. -/
theorem interleavedExample_no_effective_bridge_p1_p2 :
    EffectiveConstitutiveBridge
      interleavedExampleTrace
      (interleavedExampleRealization.realize exampleP1)
      (interleavedExampleRealization.realize exampleP2) → False := by
  intro effective
  exact effectiveBridge_between_empty_of_next
    interleavedExampleRealization
    exampleP1_next_exampleP2
    effective
    interleavedExample_extra1_between

/- Symmetrically, `extra2` cannot be exactly an occurrence of a generated
   constitutive bridge between p2 and p3. -/
theorem interleavedExample_no_effective_bridge_p2_p3 :
    EffectiveConstitutiveBridge
      interleavedExampleTrace
      (interleavedExampleRealization.realize exampleP2)
      (interleavedExampleRealization.realize exampleP3) → False := by
  intro effective
  exact effectiveBridge_between_empty_of_next
    interleavedExampleRealization
    exampleP2_next_exampleP3
    effective
    interleavedExample_extra2_between


def exampleCertificate :
    StrongPerimetralTurningCertificate examplePresentation :=
  strongPerimetralTurning examplePresentation

theorem exampleEndpointsSeparated : false ≠ true :=
  examplePresentation.endpointsSeparated

def examplePerimeterHasPositiveHistory :
    Σ continuation : History.Positive
      (@GeneratedStep examplePresentation)
      (initialPositive examplePresentation)
      (perimeterEndpoint examplePresentation),
      PLift (continuation.toHistory = perimeterHistory examplePresentation) :=
  perimeterDeployment_positive examplePresentation

theorem exampleNoIntermediate
    {history : RootedGeneratedHistory examplePresentation}
    (refinement : CircularRefinement examplePresentation history) :
    history = perimeterDeployment examplePresentation :=
  noIntermediateRefinement refinement

def exampleGeneratorContinuesBeyond :
    Σ target : PositiveConstitution examplePresentation,
      GeneratedStep (perimeterEndpoint examplePresentation) target :=
  generate_after_perimeter examplePresentation

def exampleBeyondHistory : RootedGeneratedHistory examplePresentation :=
  oneStepAfterPerimeter examplePresentation

def exampleBeyondStrict :
    StrictConstitutivePrefix
      (perimeterDeployment examplePresentation) exampleBeyondHistory :=
  oneStepAfterPerimeterStrict examplePresentation

theorem exampleBeyondIsNotSamePerimeter :
    CircularRefinement examplePresentation exampleBeyondHistory → False :=
  oneStepAfterPerimeter_notCircularRefinement examplePresentation

theorem exampleLengthExact :
    (perimeterHistory examplePresentation).length = 3 := rfl

theorem exampleNoLongerSamePerimeter
    {history : RootedGeneratedHistory examplePresentation}
    (refinement : CircularRefinement examplePresentation history) :
    ¬ 3 < history.history.length := by
  rw [← exampleLengthExact]
  exact no_longer_samePerimeter refinement

def exampleAfterPerimeterCursorIsBeyond :
    (exampleGeneratorContinuesBeyond.1).1 = .beyond .first :=
  generate_after_perimeter_is_beyond examplePresentation

def canonicalPositiveStep
    (source : PositiveConstitution examplePresentation) :
    History.Positive (@GeneratedStep examplePresentation)
      source (canonicalTarget source) :=
  ⟨source, .root, generatedStepOfFreeK source⟩

theorem canonicalTarget_ne_source
    (source : PositiveConstitution examplePresentation) :
    canonicalTarget source ≠ source := by
  intro equality
  exact positiveGeneratedHistory_source_ne_target
    (canonicalPositiveStep source) equality.symm

def exampleAfterFirst : PositiveConstitution examplePresentation :=
  canonicalTarget (initialPositive examplePresentation)

theorem exampleInitialObstructionStored :
    BoundaryDifferenceCode.inheritedClosureObstruction
        (FreeConstitution.root (P := examplePresentation)).1 =
      examplePresentation.positiveClosureObstruction :=
  rfl

theorem exampleAfterFirstObstructionPreserved :
    BoundaryDifferenceCode.inheritedClosureObstruction
        exampleAfterFirst.2.1.1 =
      BoundaryDifferenceCode.inheritedClosureObstruction
        (initialPositive examplePresentation).2.1.1 :=
  canonicalTarget_inheritedClosureObstruction_exact
    (initialPositive examplePresentation)

theorem exampleFormationConsumesInitialObstruction :
    FreeKCore.integratedClosureObstruction
        (canonicalFreeLayer
          (initialPositive examplePresentation)).core =
      BoundaryDifferenceCode.inheritedClosureObstruction
        (initialPositive examplePresentation).2.1.1 :=
  rfl

theorem exampleIntegratedProvenanceStored :
    FreeKCore.integratedProvenance
        (canonicalFreeLayer
          (initialPositive examplePresentation)).core =
      provenanceAtCursor
        (P := examplePresentation) (.within examplePerimeter) :=
  rfl

def exampleHistoricalFirstProvenancePreserved :
    HistoricalProvenanceRecord examplePresentation
      (initialPositive examplePresentation) exampleAfterFirst.2.1 :=
  canonicalSourceProvenanceInscribed (initialPositive examplePresentation)

theorem exampleHistoricalRecordReadsFirst :
    exampleHistoricalFirstProvenancePreserved.recordedProvenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

theorem exampleCurrentTargetReadsSecond :
    boundaryProvenanceReadout exampleAfterFirst.2.2 =
      ReturnedProvenance.source Provenance.second :=
  rfl

def exampleRecoveredAfterFirst :
    RecoveredImmediateOrigin examplePresentation exampleAfterFirst.2.1 :=
  recoverImmediateOriginFromFormation
    (currentRecordInCanonicalTarget
      (initialPositive examplePresentation))

theorem exampleRecoveredAfterFirstReadsStoredProvenance :
    exampleRecoveredAfterFirst.provenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

def exampleRawFinalJunctionCompatibility :
    FinalJunctionCompatibility examplePresentation :=
  examplePresentation.finalJunction

def exampleRawJunctionWithSeparatedEndpoints :
    RawJunctionWithSeparatedEndpoints examplePresentation :=
  { junction := exampleRawFinalJunctionCompatibility
    separated := exampleEndpointsSeparated }

def exampleOneStepFaithfulLabelling :
    FaithfulPerimeterLabelling examplePresentation exampleBeyondHistory
      (oneStepAfterPerimeter_is_extension examplePresentation) :=
  oneStepFaithfulLabelling examplePresentation

def examplePositiveContinuation :
    PositiveContinuation
      (oneStepAfterPerimeter_is_extension examplePresentation) :=
  oneStepAfterPerimeter_positiveContinuation examplePresentation

def exampleFinalBoundaryOccurrence :
    FinalBoundaryOccurrence examplePresentation exampleBeyondHistory :=
  finalBoundaryOccurrence
    (oneStepFaithfullyLabelledExtension examplePresentation)
    examplePositiveContinuation

def exampleFinalClosureInterpretation :
    FinalClosureInterpretation examplePresentation exampleBeyondHistory :=
  finalClosureInterpretation exampleFinalBoundaryOccurrence

theorem exampleActualFreeStep_source_is_fourth :
    implicitRead exampleFinalBoundaryOccurrence.source =
      ReturnedImplicit.source Implicit.fourth :=
  exampleFinalClosureInterpretation.actualFreeStep_source_is_terminalImplicit

theorem exampleActualFreeStep_target_is_beyondFirst :
    explicitRead exampleFinalBoundaryOccurrence.target =
      ReturnedExplicit.formed (.beyond .first) :=
  exampleFinalClosureInterpretation.actualFreeStep_target_is_freeExplicit

theorem exampleActualFreeStep_is_leaveBoundary :
    HEq exampleFinalBoundaryOccurrence.step.compatibility
      (ReturnedCompatible.leaveBoundary
        (P := examplePresentation) fourthNode) :=
  exampleFinalBoundaryOccurrence.compatibility_is_leaveBoundary

theorem exampleInvokedJunction_is_fourthToFirst :
    exampleFinalClosureInterpretation.junction = Compatible.fourthToFirst :=
  exampleFinalClosureInterpretation.junctionIsDistinguished

theorem exampleFinalObstruction_is_initial :
    exampleFinalClosureInterpretation.targetObstruction =
      examplePresentation.positiveClosureObstruction :=
  exampleFinalClosureInterpretation.targetObstructionIsInitial

theorem exampleFinalProvenance_is_origin :
    exampleFinalClosureInterpretation.provenanceRecord.recordedProvenance =
      boundaryProvenanceReadout exampleFinalBoundaryOccurrence.source.2.2 :=
  exampleFinalClosureInterpretation.provenanceRecord.recordedProvenance_is_origin

theorem exampleFinalFormationRecord_is_current :
    HEq exampleFinalClosureInterpretation.formationRecord
      (currentRecordInCanonicalTarget
        exampleFinalBoundaryOccurrence.source) :=
  (heq_of_eq
    exampleFinalClosureInterpretation.formationRecordIsStepExact).trans
      exampleFinalBoundaryOccurrence.step.currentFormationRecord_is_current

theorem exampleNoBilateralClosureAttemptAt :
    BilateralClosureAttemptAt exampleFinalClosureInterpretation → False :=
  BilateralClosureAttemptAt.rejectExplicit

theorem exampleNoImplicitBilateralClosureAttemptAt :
    BilateralClosureAttemptAt exampleFinalClosureInterpretation → False :=
  BilateralClosureAttemptAt.rejectImplicit

def exampleHistoricalFirstProvenancePreservedAfterSecond :
    HistoricalProvenanceRecord examplePresentation
      (initialPositive examplePresentation)
      (canonicalTarget exampleAfterFirst).2.1 :=
  preserveHistoricalProvenanceAlongStep
    (generatedStepOfFreeK exampleAfterFirst)
    exampleHistoricalFirstProvenancePreserved

theorem exampleHistoricalRecordAfterSecondStillReadsFirst :
    exampleHistoricalFirstProvenancePreservedAfterSecond.recordedProvenance =
      ReturnedProvenance.source Provenance.first :=
  rfl

def exampleSecondStepFreshFormation :
    FreshFormationRecord examplePresentation
      exampleAfterFirst (canonicalTarget exampleAfterFirst) :=
  positiveGeneratedHistory_hasFreshFormation
    (canonicalPositiveStep exampleAfterFirst)

theorem exampleFreshFormationRejectsPreviousRecord :
    exampleSecondStepFreshFormation.freshRecord ≠
      preserveFormationRecordAlongStep
        exampleSecondStepFreshFormation.lastStep
        (currentRecordInCanonicalTarget
          (initialPositive examplePresentation)) :=
  exampleSecondStepFreshFormation.notFromPredecessor _

def exampleConcreteAlgebra :
    ConcreteContinuationAlgebra.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      examplePresentation :=
  { ConcreteState := PositiveConstitution examplePresentation
    ConcreteStep := @GeneratedStep examplePresentation
    stateAt := fun state => state
    ConcreteExplicit := ReturnedExplicit examplePresentation
    ConcreteImplicit := ReturnedImplicit examplePresentation
    ConcreteCompatible := ReturnedCompatible examplePresentation
    interpretExplicit := fun explicit => explicit
    interpretImplicit := fun implicit => implicit
    interpretCompatible := fun compatible => compatible
    ConcreteDifference := ReturnedDifference examplePresentation
    ConcreteProvenance := ReturnedProvenance examplePresentation
    interpretDifference := fun difference => difference
    interpretProvenance := fun provenance => provenance
    ConcreteIntegration := fun _ => PUnit
    ConcreteContinuation := fun _ _ => PUnit
    ConcreteFreshBoundary := fun _ _ => PUnit
    ConcreteBoundaryRecord := PositiveConstitution examplePresentation
    boundaryRecordAt := fun state => state
    concreteStep := generatedStepOfFreeK
    explicitPoleStep := generatedStepOfFreeK
    implicitPoleStep := generatedStepOfFreeK
    differenceStep := generatedStepOfFreeK
    admissibleStep := fun source _ => generatedStepOfFreeK source
    successorFormationExact := fun _ => rfl
    compatibilityRealized := fun source => stepCompatibleAt source.1
    compatibilityRealizedExact := fun _ => rfl
    differenceIntegrated := fun _ => ⟨⟩
    provenancePreserved := fun source =>
      boundaryProvenanceReadout source.2.2
    provenancePreservedExact := fun _ => rfl
    differenceContinued := fun _ => ⟨⟩
    boundaryFresh := fun _ => ⟨⟩
    boundaryRecordFresh := canonicalTarget_ne_source }

def exampleFirstTail : PerimeterSpine Compatible secondNode :=
  @PerimeterSpine.advance _ _ _ _ _ secondNode thirdNode
    (.secondToThird : Compatible .second .third)
    (@PerimeterSpine.advance _ _ _ _ _ thirdNode fourthNode
      (.thirdToFourth : Compatible .third .fourth)
      (.boundary fourthNode))

def exampleConcreteFirstPath :
    ConcreteFaithfulPartialPath examplePresentation exampleConcreteAlgebra
      exampleFirstTail
      (canonicalTarget (initialPositive examplePresentation)).2.1
      (canonicalTarget (initialPositive examplePresentation)).2.2
      (.extend .root
        (exampleConcreteAlgebra.concreteStep
          (initialPositive examplePresentation))) :=
  .advance .root

def exampleConcreteFirstRealization :
    ConcreteFaithfulPartialRealization
      examplePresentation exampleConcreteAlgebra :=
  { node := secondNode
    remaining := exampleFirstTail
    data := (canonicalTarget (initialPositive examplePresentation)).2.1
    difference := (canonicalTarget (initialPositive examplePresentation)).2.2
    concreteHistory :=
      .extend .root
        (exampleConcreteAlgebra.concreteStep
          (initialPositive examplePresentation))
    derivation := exampleConcreteFirstPath }

def exampleConcreteInterpretation :
    FaithfulPartialInterpretation exampleConcreteAlgebra
      exampleConcreteFirstRealization :=
  interpretEveryFaithfulPartialRealization exampleConcreteFirstRealization

end Example


end StrongPerimetralTurning
