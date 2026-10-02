import Constitution.CardinalReadout
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Exact concrete interpretations

The concrete layer interprets the free generators pointwise.  Its path type is
inductive in its own right and stores no free history.  A free prefix together
with exact occurrence round trips is reconstructed from that derivation. -/

structure ConcreteContinuationAlgebra
    (P : CircularPresentation) where
  ConcreteState : Type uA
  ConcreteStep : ConcreteState → ConcreteState → Type uB
  stateAt : PositiveConstitution P → ConcreteState

  ConcreteExplicit : Type uC
  ConcreteImplicit : Type uD
  ConcreteCompatible : ConcreteImplicit → ConcreteExplicit → Type uE
  interpretExplicit : ReturnedExplicit P → ConcreteExplicit
  interpretImplicit : ReturnedImplicit P → ConcreteImplicit
  interpretCompatible :
    {implicit : ReturnedImplicit P} →
    {explicit : ReturnedExplicit P} →
    ReturnedCompatible P implicit explicit →
      ConcreteCompatible
        (interpretImplicit implicit) (interpretExplicit explicit)

  ConcreteDifference : Type uF
  ConcreteProvenance : ConcreteDifference → Type uG
  interpretDifference : ReturnedDifference P → ConcreteDifference
  interpretProvenance :
    {difference : ReturnedDifference P} →
    ReturnedProvenance P difference →
      ConcreteProvenance (interpretDifference difference)

  ConcreteIntegration : ConcreteDifference → Type uH
  ConcreteContinuation :
    ConcreteDifference → ConcreteDifference → Type uI
  ConcreteFreshBoundary :
    ConcreteDifference → ConcreteDifference → Type uJ
  ConcreteBoundaryRecord : Type uK
  boundaryRecordAt : PositiveConstitution P → ConcreteBoundaryRecord

  concreteStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  explicitPoleStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  implicitPoleStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  differenceStep :
    (source : PositiveConstitution P) →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))
  admissibleStep :
    (source : PositiveConstitution P) →
    CompatibleExplicitation P source.1 →
      ConcreteStep (stateAt source) (stateAt (canonicalTarget source))

  successorFormationExact :
    (source : PositiveConstitution P) →
      admissibleStep source (successorCompatibleExplicitation source.1) =
        concreteStep source
  compatibilityRealized :
    (source : PositiveConstitution P) →
      ConcreteCompatible
        (interpretImplicit (implicitRead source))
        (interpretExplicit (explicitRead (canonicalTarget source)))
  compatibilityRealizedExact :
    (source : PositiveConstitution P) →
      compatibilityRealized source =
        interpretCompatible (stepCompatibleAt source.1)
  differenceIntegrated :
    (source : PositiveConstitution P) →
      ConcreteIntegration
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
  provenancePreserved :
    (source : PositiveConstitution P) →
      ConcreteProvenance
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
  provenancePreservedExact :
    (source : PositiveConstitution P) →
      provenancePreserved source =
        interpretProvenance
          (boundaryProvenanceReadout source.2.2)
  differenceContinued :
    (source : PositiveConstitution P) →
      ConcreteContinuation
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
        (interpretDifference
          (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryFresh :
    (source : PositiveConstitution P) →
      ConcreteFreshBoundary
        (interpretDifference
          (boundaryDifferenceReadout source.2.2))
        (interpretDifference
          (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryRecordFresh :
    (source : PositiveConstitution P) →
      boundaryRecordAt (canonicalTarget source) ≠ boundaryRecordAt source

namespace ConcreteContinuationAlgebra

def formLayer
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    FreeKAlgebra P source.1 :=
  { Carrier := A.ConcreteStep
      (A.stateAt source) (A.stateAt (canonicalTarget source))
    explicitPole := A.explicitPoleStep source
    implicitPole := A.implicitPoleStep source
    currentDifference := A.differenceStep source
    admissible := A.admissibleStep source }

theorem successor_fold_exact
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    FreeKAtom.fold (A.formLayer source) (successorFormationTerm source) =
      A.concreteStep source :=
  A.successorFormationExact source

end ConcreteContinuationAlgebra

structure ConcreteStepAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) : Type _ where
  formedByFreeEliminator :
    FreeKAtom.fold (A.formLayer source) (successorFormationTerm source) =
      A.concreteStep source
  interpretsCompatibility :
    A.ConcreteCompatible
      (A.interpretImplicit (implicitRead source))
      (A.interpretExplicit (explicitRead (canonicalTarget source)))
  compatibilityIsExactImage :
    interpretsCompatibility =
      A.interpretCompatible (stepCompatibleAt source.1)
  integratesDifference :
    A.ConcreteIntegration
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
  preservesProvenance :
    A.ConcreteProvenance
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
  provenanceIsExactImage :
    preservesProvenance =
      A.interpretProvenance (boundaryProvenanceReadout source.2.2)
  continuesDifference :
    A.ConcreteContinuation
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
      (A.interpretDifference
        (boundaryDifferenceReadout (canonicalTarget source).2.2))
  distinguishesFreshBoundary :
    A.ConcreteFreshBoundary
      (A.interpretDifference (boundaryDifferenceReadout source.2.2))
      (A.interpretDifference
        (boundaryDifferenceReadout (canonicalTarget source).2.2))
  boundaryRecordIsFresh :
    A.boundaryRecordAt (canonicalTarget source) ≠ A.boundaryRecordAt source

def ConcreteContinuationAlgebra.stepAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (source : PositiveConstitution P) :
    ConcreteStepAgreement A source :=
  { formedByFreeEliminator := A.successor_fold_exact source
    interpretsCompatibility := A.compatibilityRealized source
    compatibilityIsExactImage := A.compatibilityRealizedExact source
    integratesDifference := A.differenceIntegrated source
    preservesProvenance := A.provenancePreserved source
    provenanceIsExactImage := A.provenancePreservedExact source
    continuesDifference := A.differenceContinued source
    distinguishesFreshBoundary := A.boundaryFresh source
    boundaryRecordIsFresh := A.boundaryRecordFresh source }

def ConcreteContinuationAlgebra.realizeHistory
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P} :
    GeneratedHistory source target →
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)
  | .root => .root
  | .extend history step => by
      cases step.formedByFreeLayer
      exact .extend (A.realizeHistory history) (A.concreteStep _)

def concreteForwardOccurrence
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    History.Occurrence history →
      History.Occurrence (A.realizeHistory history) :=
  match history with
  | .root => fun occurrence => nomatch occurrence
  | .extend previous step => by
      cases step.formedByFreeLayer
      intro occurrence
      cases occurrence with
      | last => exact .last
      | earlier earlier =>
          exact .earlier (concreteForwardOccurrence A previous earlier)

def concreteBackwardOccurrence
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    History.Occurrence (A.realizeHistory history) →
      History.Occurrence history :=
  match history with
  | .root => fun occurrence => nomatch occurrence
  | .extend previous step => by
      cases step.formedByFreeLayer
      intro occurrence
      cases occurrence with
      | last => exact .last
      | earlier earlier =>
          exact .earlier (concreteBackwardOccurrence A previous earlier)

theorem concreteBackwardForward
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (occurrence : History.Occurrence history) :
    concreteBackwardOccurrence A history
      (concreteForwardOccurrence A history occurrence) = occurrence := by
  induction history with
  | root => cases occurrence
  | extend history step inductionHypothesis =>
      cases step.formedByFreeLayer
      cases occurrence with
      | last => rfl
      | earlier earlier =>
          exact congrArg History.Occurrence.earlier
            (inductionHypothesis earlier)

theorem concreteForwardBackward
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (occurrence : History.Occurrence (A.realizeHistory history)) :
    concreteForwardOccurrence A history
      (concreteBackwardOccurrence A history occurrence) = occurrence := by
  induction history with
  | root => cases occurrence
  | extend history step inductionHypothesis =>
      cases step.formedByFreeLayer
      cases occurrence with
      | last => rfl
      | earlier earlier =>
          exact congrArg History.Occurrence.earlier
            (inductionHypothesis earlier)

structure ConcreteOccurrenceAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (freeOccurrence : History.Occurrence freeHistory)
    (concreteOccurrence : History.Occurrence concreteHistory) : Type _ where
  sourceExact :
    concreteOccurrence.locatedStep.source =
      A.stateAt freeOccurrence.locatedStep.source
  targetExact :
    concreteOccurrence.locatedStep.target =
      A.stateAt freeOccurrence.locatedStep.target
  stepExact :
    HEq concreteOccurrence.locatedStep.step
      (A.concreteStep freeOccurrence.locatedStep.source)
  interpretedStep : ConcreteStepAgreement A freeOccurrence.locatedStep.source

def concreteOccurrenceAgreement
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source : PositiveConstitution P} :
    {target : PositiveConstitution P} →
    (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      ConcreteOccurrenceAgreement A occurrence
        (concreteForwardOccurrence A history occurrence)
  | _, .root, occurrence => nomatch occurrence
  | _, .extend previous step, .last => by
      cases step.formedByFreeLayer
      exact
        { sourceExact := rfl
          targetExact := rfl
          stepExact := HEq.rfl
          interpretedStep := A.stepAgreement _ }
  | _, .extend previous step, .earlier earlier => by
      cases step.formedByFreeLayer
      let prior := concreteOccurrenceAgreement A previous earlier
      exact
        { sourceExact := prior.sourceExact
          targetExact := prior.targetExact
          stepExact := prior.stepExact
          interpretedStep := prior.interpretedStep }

structure ExactHistoryInterpretation
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (freeHistory : GeneratedHistory source target)
    (concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)) : Type _ where
  forwardOccurrence :
    History.Occurrence freeHistory → History.Occurrence concreteHistory
  backwardOccurrence :
    History.Occurrence concreteHistory → History.Occurrence freeHistory
  forwardBackward :
    (occurrence : History.Occurrence freeHistory) →
      backwardOccurrence (forwardOccurrence occurrence) = occurrence
  backwardForward :
    (occurrence : History.Occurrence concreteHistory) →
      forwardOccurrence (backwardOccurrence occurrence) = occurrence
  occurrenceAgreement :
    (occurrence : History.Occurrence freeHistory) →
      ConcreteOccurrenceAgreement A occurrence (forwardOccurrence occurrence)

namespace ExactHistoryInterpretation

/- Readouts transport contravariantly along the exact occurrence maps.  This
   is reindexing only: structural agreement belongs to the interpretation,
   while any semantic law of the values remains an independent obligation. -/
def pullbackReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout concreteHistory Value) :
    History.OccurrenceReadout freeHistory Value :=
  fun occurrence => readout (interpretation.forwardOccurrence occurrence)

def pushforwardReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout freeHistory Value) :
    History.OccurrenceReadout concreteHistory Value :=
  fun occurrence => readout (interpretation.backwardOccurrence occurrence)

theorem pullbackReadout_pushforwardReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout freeHistory Value)
    (occurrence : History.Occurrence freeHistory) :
    interpretation.pullbackReadout
        (interpretation.pushforwardReadout readout) occurrence =
      readout occurrence := by
  change readout
      (interpretation.backwardOccurrence
        (interpretation.forwardOccurrence occurrence)) = readout occurrence
  rw [interpretation.forwardBackward]

theorem pushforwardReadout_pullbackReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory)
    {Value : Type uV}
    (readout : History.OccurrenceReadout concreteHistory Value)
    (occurrence : History.Occurrence concreteHistory) :
    interpretation.pushforwardReadout
        (interpretation.pullbackReadout readout) occurrence =
      readout occurrence := by
  change readout
      (interpretation.forwardOccurrence
        (interpretation.backwardOccurrence occurrence)) = readout occurrence
  rw [interpretation.backwardForward]

def transportConcreteHistory
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {first second :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (equality : first = second) :
    ExactHistoryInterpretation A freeHistory first →
      ExactHistoryInterpretation A freeHistory second := by
  cases equality
  exact id

theorem forwardOccurrence_injective
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory) :
    Function.Injective interpretation.forwardOccurrence := by
  intro first second equality
  have transported := congrArg interpretation.backwardOccurrence equality
  rw [interpretation.forwardBackward first,
    interpretation.forwardBackward second] at transported
  exact transported

theorem backwardOccurrence_injective
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory) :
    Function.Injective interpretation.backwardOccurrence := by
  intro first second equality
  have transported := congrArg interpretation.forwardOccurrence equality
  rw [interpretation.backwardForward first,
    interpretation.backwardForward second] at transported
  exact transported

end ExactHistoryInterpretation

def exactlyInterpretHistory
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    ExactHistoryInterpretation A history (A.realizeHistory history) :=
  { forwardOccurrence := concreteForwardOccurrence A history
    backwardOccurrence := concreteBackwardOccurrence A history
    forwardBackward := concreteBackwardForward A history
    backwardForward := concreteForwardBackward A history
    occurrenceAgreement := concreteOccurrenceAgreement A history }


end StrongPerimetralTurning
