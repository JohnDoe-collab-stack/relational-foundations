import Constitution.Regime
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Direct core coupled circular regime

This is the production coupled path.  Its regime, interpretation, attempt,
and residual boundary are all core-level data; the historical rich regime is
not used to determine the residual occurrence. -/
def perimetralCoreCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (fun history => CoreCircularResidualContext P history)
      (fun {_history} context =>
        History.Occurrence context.extension.continuation)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (finalRequirementContractible P) :=
  { Regime := CoreCircularRefinement P
    Interpretation := fun history => CoreResidualClosureInterpretation history
    Attempt := fun {history} interpretation =>
      CoreResidualClosureAttempt history interpretation
    canonicalRegime := identityCoreCircularRefinement P
    interpretResidual := fun boundary unique =>
      coreInterpretResidual boundary unique
    analyzeRegime := by
      intro candidate refinement
      cases History.appendRootOrPositive
          (perimeterHistory P) refinement.extension.continuation with
      | inl rootData =>
          rcases rootData with ⟨endpointEquality, continuationEquality⟩
          exact .inl ⟨rootedGeneratedHistory_ext endpointEquality.down
            ((heq_of_eq refinement.extension.recompose.symm).trans
              continuationEquality.down)⟩
      | inr positiveData =>
          rcases positiveData with ⟨positive, continuationEquality⟩
          let positiveContinuation : PositiveContinuation refinement.extension :=
            { path := positive
              historyExact := continuationEquality.down }
          rcases refinement.positiveBranch positiveContinuation with
            ⟨core, attempt⟩
          let boundary :=
            coreCircularPositiveResidualBoundary
              refinement.extension positiveContinuation core
          exact .inr ⟨boundary, attempt⟩
    rejectTotalization := by
      intro candidate interpretation attempt
      exact rejectCoreResidualClosureAttempt attempt }

theorem perimetralCoreCoupledInterpretation_occurrence
    (P : CircularPresentation)
    {history : RootedGeneratedHistory P}
    (boundary : coreCircularBoundaryType P history)
    (unique : SegmentedResidualRole.CoreUniqueResidualOccurrence
      boundary.core) :
    ((perimetralCoreCoupledRegime P).interpretResidual boundary unique).residualOccurrence =
      unique.occurrence := by
  rfl

def perimetralCoreObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoreCoupledRegime P).toObstructedRegime

def perimetralCoupledRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledObstructedRegime
      (perimetralBoundaryGenerator P)
      (CircularResidualBoundaryContext P)
      (circularBoundaryNewOccurrence P)
      (circularBoundaryCombinedOccurrence P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { Regime := CircularRefinement P
    Interpretation := ResidualFinalClosureInterpretation P
    Attempt := ResidualBilateralClosureAttempt
    canonicalRegime := identityCircularRefinement P
    interpretResidual := interpretCircularResidual
    analyzeRegime := analyzeCircularRegimeWithResidualAttempt
    rejectTotalization := rejectResidualBilateralClosureAttempt }

/- A circular refinement has exactly the generic obstructed-regime shape:
   it is either the canonical perimeter or supplies a bilateral totalization
   attempt, and every such attempt is rejected. -/
def perimetralObstructedRegime
    (P : CircularPresentation) :
    AbstractSegmentedTurning.ObstructedRegime
      (perimetralBoundaryGenerator P) :=
  (perimetralCoupledRegime P).toObstructedRegime

def oneStepCoreTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreTurningConclusion
      (oneStepCoreSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  AbstractSegmentedTurning.coreTurning
    (oneStepCoreSegmentedBoundary P)
    (perimetralCoreObstructedRegime P)

/- Reattach the direct core turning to the historical rich boundary type.  The
   occurrence and its uniqueness come from the core result; only the public
   rich label is checked at this boundary. -/
def oneStepCoreTurning_toPublic
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) :=
  let coreResult := oneStepCoreTurning P
  { uniqueResidualOccurrence :=
      { occurrence := coreResult.uniqueResidualOccurrence.occurrence
        labelIsResidual := by rfl
        unique := fun other =>
          coreResult.uniqueResidualOccurrence.unique other }
    exactRelativeClassification := coreResult.exactRelativeClassification
    generatedContinuation := coreResult.generatedContinuation
    continuationIsStrict := coreResult.continuationIsStrict
    continuationOutsideRegime := coreResult.continuationOutsideRegime
    noStrictRegimeExtension := coreResult.noStrictRegimeExtension
    totalizationRejected := coreResult.totalizationRejected }

def perimetralCoreCoupledTurning
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  AbstractSegmentedTurning.coreCoupledTurning
    (perimetralCoreCoupledRegime P)

def historicalCoupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoupledTurningConclusion
      (perimetralCoupledRegime P) :=
  AbstractSegmentedTurning.coupledTurning (perimetralCoupledRegime P)

def coupledTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion
      (perimetralCoreCoupledRegime P) :=
  perimetralCoreCoupledTurning P

/- The historical rich turning remains available under an explicit name. -/
def historicalAbstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralObstructedRegime P) :=
  AbstractSegmentedTurning.abstractTurning
    (oneStepSegmentedBoundary P)
    (perimetralObstructedRegime P)

/- The whole circle-independent turning theorem is now instantiated by the
   direct core path, its residual occurrence, and its core obstructed regime. -/
def abstractTurningOfCircularPresentation
    (P : CircularPresentation) :
    AbstractSegmentedTurning.TurningConclusion
      (oneStepSegmentedBoundary P)
      (perimetralCoreObstructedRegime P) := by
  exact oneStepCoreTurning_toPublic P

theorem oneStepCoreResidualOccurrence_agrees_with_weak
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      (oneStepWeakResidualOccurrence P).occurrence :=
  rfl

theorem oneStepCoreResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepCoreResidualOccurrence P).occurrence =
      ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence).occurrence :=
  rfl

/- The abstract turning consumes the same residual occurrence as the weak
   producer-facing construction.  This is a direct agreement with the
   published consumer, not an agreement between two new adapters. -/
theorem oneStepWeakResidualOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  (oneStepCoreResidualOccurrence_agrees_with_weak P).symm.trans
    (oneStepCoreResidualOccurrence_agrees_with_consumedTurning P)

theorem noIntermediateRefinement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    history = perimeterDeployment P :=
  (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
    |>.regimeImpliesEquality refinement

structure ExactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ where
  refinementImpliesEquality :
    CircularRefinement P history → history = perimeterDeployment P
  equalityBuildsRefinement :
    history = perimeterDeployment P → CircularRefinement P history

def exactCircularRefinementClassification
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    ExactCircularRefinementClassification P history :=
  let classification :=
    (historicalCoupledTurningOfCircularPresentation P).exactRelativeClassification
  { refinementImpliesEquality :=
      classification.regimeImpliesEquality
    equalityBuildsRefinement :=
      classification.equalityBuildsRegime }

theorem oneStepAfterPerimeter_notCircularRefinement
    (P : CircularPresentation) :
    CircularRefinement P (oneStepAfterPerimeter P) → False :=
  (historicalCoupledTurningOfCircularPresentation P).continuationOutsideRegime

def strictRefinementProducesFinalJunctionRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalJunctionRealization P history := by
  cases refinementOutcome refinement with
  | inl equality => exact False.elim (strictPrefix_ne strict equality.down)
  | inr realization => exact realization

def strictRefinementProducesFinalLoopRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalLoopRealization P history :=
  FinalJunctionRealization.toFinalLoopRealization
    (strictRefinementProducesFinalJunctionRealization strict refinement)

def strictRefinementProducesFinalIdentification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) :
    FinalIdentification P history :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toFinalIdentification

def strictRefinementProducesTotalLoop
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix (perimeterDeployment P) history)
    (refinement : CircularRefinement P history) : P.TotalLoop :=
  (strictRefinementProducesFinalLoopRealization strict refinement).toTotalLoop

/- Soundness of the circular regime relative to the independent specification:
   the regime's perimeter extension supplies local exactness, while strict
   refinement closure supplies the trajectory obligation. -/
def circularRefinement_soundSpecification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CircularSpecificationSatisfaction P history :=
  { «local» :=
      refinement.extension.toExactNonClosingRealization
    trajectory :=
      fun strict =>
        strictRefinementProducesTotalLoop strict refinement }

theorem noStrictSamePerimeterExtension
    (P : CircularPresentation) :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix (perimeterDeployment P) history ×
        CircularRefinement P history) → False :=
  (historicalCoupledTurningOfCircularPresentation P).noStrictRegimeExtension

inductive PerimetrallyAdmissible
    (P : CircularPresentation) : RootedGeneratedHistory P → Type _
  | properPartial
      {history : RootedGeneratedHistory P} :
      FreePartialRealization P history → PerimetrallyAdmissible P history
  | samePerimeter
      {history : RootedGeneratedHistory P} :
      CircularRefinement P history → PerimetrallyAdmissible P history

def admissible_is_prefix_of_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    PerimetrallyAdmissible P history →
      ConstitutivePrefix history (perimeterDeployment P)
  | .properPartial partialPath => partial_is_prefix_of_perimeter partialPath
  | .samePerimeter refinement => by
      cases noIntermediateRefinement refinement
      exact prefixReflexive _

structure StrongPerimetralTurningCertificate
    (P : CircularPresentation) where
  initialClosureObstruction : PositiveClosureObstruction P
  initialClosureObstructionIsCanonical :
    initialClosureObstruction = P.positiveClosureObstruction
  engender :
    (source : PositiveConstitution P) →
      Σ target : PositiveConstitution P, GeneratedStep source target
  obstructionTransportedByEveryStep :
    {source target : PositiveConstitution P} →
      (step : GeneratedStep source target) →
        target.2.1.1.inheritedClosureObstruction =
          source.2.1.1.inheritedClosureObstruction
  deployment : RootedGeneratedHistory P
  generatedOnly : GeneratedOnlyByFreeConstruction deployment
  terminalClosureObstructionIsInitial :
    deployment.terminalClosureObstruction = P.positiveClosureObstruction
  exactPerimeter : ExactPerimeterRealization P deployment
  absorbsPartial :
    {history : RootedGeneratedHistory P} →
      FreePartialRealization P history → ConstitutivePrefix history deployment
  noIntermediate :
    {history : RootedGeneratedHistory P} →
      CircularRefinement P history → history = deployment
  rejectsExplicitTotalization : ExplicitTotalization P → False
  rejectsImplicitTotalization : ImplicitTotalization P → False
  rejectsFinalJunction :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  rejectsFinalJunctionImplicit :
    {history : RootedGeneratedHistory P} →
      FinalJunctionRealization P history → False
  finalBoundaryFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalBoundaryOccurrence P history
  finalInterpretationFromPositive :
    {history : RootedGeneratedHistory P} →
    (labelled : FaithfullyLabelledPerimeterExtension P history) →
    (positive : PositiveContinuation labelled.extension) →
      FinalClosureInterpretation P history
  rejectsExplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  rejectsImplicitAttemptAt :
    {history : RootedGeneratedHistory P} →
    {interpretation : FinalClosureInterpretation P history} →
      BilateralClosureAttemptAt interpretation → False
  noStrictSamePerimeter :
    (Σ history : RootedGeneratedHistory P,
      StrictConstitutivePrefix deployment history ×
        CircularRefinement P history) → False
  continuesFreelyBeyondPerimeter :
    Σ target : PositiveConstitution P,
      GeneratedStep deployment.endpoint target

def strongPerimetralTurning
    (P : CircularPresentation) : StrongPerimetralTurningCertificate P :=
  { initialClosureObstruction := P.positiveClosureObstruction
    initialClosureObstructionIsCanonical := rfl
    engender := generate
    obstructionTransportedByEveryStep :=
      GeneratedStep.inheritedClosureObstructionExact
    deployment := perimeterDeployment P
    generatedOnly := perimeterDeployment_generatedOnly P
    terminalClosureObstructionIsInitial :=
      RootedGeneratedHistory.terminalClosureObstruction_is_initial _
    exactPerimeter := perimeterRealization P
    absorbsPartial := partial_is_prefix_of_perimeter
    noIntermediate := noIntermediateRefinement
    rejectsExplicitTotalization := explicitTotalizationRejected
    rejectsImplicitTotalization := implicitTotalizationRejected
    rejectsFinalJunction := rejectFinalJunctionRealization
    rejectsFinalJunctionImplicit := rejectFinalJunctionRealizationImplicit
    finalBoundaryFromPositive := finalBoundaryOccurrence
    finalInterpretationFromPositive := fun labelled positive =>
      finalClosureInterpretation
        (finalBoundaryOccurrence labelled positive)
    rejectsExplicitAttemptAt := BilateralClosureAttemptAt.rejectExplicit
    rejectsImplicitAttemptAt := BilateralClosureAttemptAt.rejectImplicit
    noStrictSamePerimeter := noStrictSamePerimeterExtension P
    continuesFreelyBeyondPerimeter :=
      generate (perimeterDeployment P).endpoint }


end StrongPerimetralTurning
