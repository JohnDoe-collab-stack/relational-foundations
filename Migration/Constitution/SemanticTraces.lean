import Constitution.Specification
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Experimental semantic traces -/

/- `SemanticTrace` deliberately forgets global composability while retaining
   the complete located data of every generated step.  Occurrences are list
   positions, so equal located steps may still occur at distinct indices. -/
structure SemanticTrace
    (P : CircularPresentation) where
  steps : List (History.LocatedStep (@GeneratedStep P))

namespace SemanticTrace

abbrev Occurrence
    {P : CircularPresentation}
    (trace : SemanticTrace P) : Type :=
  Fin trace.steps.length

def locatedStep
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (occurrence : trace.Occurrence) :
    History.LocatedStep (@GeneratedStep P) :=
  trace.steps.get occurrence

end SemanticTrace

/- Experimental counterpart of `RequirementOccurrenceAgreement`.  It keeps
   only the exact local semantic content and does not assume a generated
   history, a circular labelling, or any regime structure. -/
structure LocatedRequirementAgreement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter)
    (located : History.LocatedStep (@GeneratedStep P)) where
  locatedStepExact :
    located =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position

/- Experimental exact local coverage.  Injectivity preserves occurrence
   individuation, while no global composability or ordering constraint is
   imposed beyond the explicit list positions of the semantic trace. -/
structure SemanticExactNonClosingRealization
    (P : CircularPresentation)
    (trace : SemanticTrace P) where
  realize :
    NonClosingPosition P.perimeter → trace.Occurrence
  realize_injective :
    Function.Injective realize
  agreement :
    (position : NonClosingPosition P.perimeter) →
      LocatedRequirementAgreement P position
        (trace.locatedStep (realize position))

/- Order preservation adds exactly one constraint to the experimental local
   realization: structural precedence in the perimeter must be reflected by
   the order of occurrence indices in the semantic trace. -/
def SemanticOrderPreserved
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace) :
    Prop :=
  ∀ first second,
    NonClosingPrecedes P.perimeter first second →
      realization.realize first < realization.realize second


namespace SemanticTrace

/- Occurrences strictly between two trace positions.  The subtype preserves
   occurrence individuation independently of the located-step reading. -/
abbrev Between
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) : Type :=
  { occurrence : trace.Occurrence //
      left < occurrence ∧ occurrence < right }

end SemanticTrace

/- Exact participation of the positionally intermediate occurrences in one
   generated constitutive bridge.  Exactness is occurrence-level first, with
   located-step agreement supplied afterwards. -/
structure ExactSemanticBridgeSegment
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence)
    {source target : PositiveConstitution P}
    (bridge : GeneratedHistory source target) where
  forwardOccurrence :
    trace.Between left right → History.Occurrence bridge
  backwardOccurrence :
    History.Occurrence bridge → trace.Between left right
  forwardBackward :
    (occurrence : trace.Between left right) →
      backwardOccurrence (forwardOccurrence occurrence) = occurrence
  backwardForward :
    (occurrence : History.Occurrence bridge) →
      forwardOccurrence (backwardOccurrence occurrence) = occurrence
  locatedStepAgreement :
    (occurrence : trace.Between left right) →
      trace.locatedStep occurrence.1 =
        (forwardOccurrence occurrence).locatedStep

/- A constitutively effective bridge is not merely a generated history with
   matching endpoints.  Its generated occurrences must correspond exactly to
   all occurrences strictly between the two selected semantic-trace indices. -/
structure EffectiveConstitutiveBridge
    {P : CircularPresentation}
    (trace : SemanticTrace P)
    (left right : trace.Occurrence) where
  leftBeforeRight : left < right
  bridge :
    GeneratedHistory
      (trace.locatedStep left).target
      (trace.locatedStep right).source
  exactSegment :
    ExactSemanticBridgeSegment trace left right bridge

/- Between canonically adjacent requirements, an exact constitutive bridge has
   no intermediate occurrences.  Positional interleaving alone therefore does
   not establish constitutive participation. -/
theorem bridgeParticipation_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (bridge : GeneratedHistory
      (trace.locatedStep (realization.realize first)).target
      (trace.locatedStep (realization.realize second)).source)
    (participates :
      trace.Between (realization.realize first) (realization.realize second) →
        History.Occurrence bridge) :
    trace.Between (realization.realize first) (realization.realize second) →
      False := by
  let firstCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial first
  let secondCanonical :=
    positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial second
  have firstExact := (realization.agreement first).locatedStepExact
  have secondExact := (realization.agreement second).locatedStepExact
  have canonicalEndpointEquality :
      firstCanonical.target = secondCanonical.source :=
    NonClosingNext.target_eq_source next
      FreeConstitution.root BoundaryDifference.initial
  have endpointEquality :
      (trace.locatedStep (realization.realize first)).target =
        (trace.locatedStep (realization.realize second)).source :=
    (congrArg
      (fun located : History.LocatedStep (@GeneratedStep P) => located.target)
      firstExact).trans
      (canonicalEndpointEquality.trans
        (congrArg
          (fun located : History.LocatedStep (@GeneratedStep P) => located.source)
          secondExact).symm)
  intro between
  exact generatedHistory_equalEndpoints_noOccurrence
    bridge endpointEquality (participates between)


/- The strong exact bridge statement is a direct corollary of the minimal
   participation theorem. -/
theorem effectiveBridge_between_empty_of_next
    {P : CircularPresentation}
    {trace : SemanticTrace P}
    (realization : SemanticExactNonClosingRealization P trace)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second)
    (effective : EffectiveConstitutiveBridge trace
      (realization.realize first) (realization.realize second)) :
    trace.Between (realization.realize first) (realization.realize second) →
      False :=
  bridgeParticipation_between_empty_of_next realization next
    effective.bridge effective.exactSegment.forwardOccurrence


structure FaithfulPerimeterLabelling
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P)
    (extension : PerimeterExtension P history) where
  label : History.Occurrence history.history → CircularRequirement P
  preservesNonClosingLabels :
    (position : NonClosingPosition P.perimeter) →
      label (extension.oldOccurrence position) = .inl position
  requirementFaithful :
    (first second : History.Occurrence history.history) →
      label first = label second → first = second

/- This weak positive layer contains only the constitutive extension and its
   faithful circular labelling.  It deliberately precedes every semantic
   realization and every totalization. -/
structure FaithfullyLabelledPerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension

namespace FaithfullyLabelledPerimeterExtension

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  labelled.extension.continuation

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    History.Occurrence history.history → CircularRequirement P :=
  labelled.labelling.label

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  labelled.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    History.Occurrence history.history :=
  labelled.extension.newOccurrence occurrence

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    labelled.label (labelled.oldOccurrence position) = .inl position :=
  labelled.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence history.history) :
    labelled.label first = labelled.label second → first = second :=
  labelled.labelling.requirementFaithful first second

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.oldOccurrence position ≠ labelled.newOccurrence occurrence :=
  labelled.extension.old_new_occurrences_disjoint position occurrence

/- Every faithfully labelled perimeter extension instantiates the abstract
   segmented residual-role interface. -/
def toSegmentedResidualExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    SegmentedResidualRole.FaithfulExtension
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence (perimeterHistory P))
      (History.Occurrence labelled.continuation)
      (History.Occurrence history.history)
      (perimeterInternalRoleRealization P)
      (finalRequirementContractible P) :=
  { embedOld := fun occurrence =>
      transportOccurrence labelled.extension.recompose
        (History.embedLeftOccurrence occurrence labelled.continuation)
    embedNew := labelled.newOccurrence
    oldNewDisjoint := by
      intro oldOccurrence newOccurrence equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.leftRightDisjoint
        oldOccurrence newOccurrence beforeTransport
    embedNewInjective := by
      intro first second equality
      have beforeTransport :=
        transportOccurrence_injective
          labelled.extension.recompose equality
      exact History.embedRightOccurrence_injective
        (perimeterHistory P) beforeTransport
    label := labelled.label
    preservesInternal := labelled.preservesNonClosingLabels
    labelFaithful := labelled.requirementFaithful }

theorem segmentedResidualExtension_embedOld_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history) :
    Function.Injective labelled.toSegmentedResidualExtension.embedOld := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective labelled.extension.recompose equality
  exact History.embedLeftOccurrence_injective
    labelled.continuation embeddedEquality

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      labelled.label (labelled.newOccurrence occurrence) = .inl position) :
    False :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_cannotReuseInternalRole
      occurrence position labelEquality

theorem newOccurrence_label_is_final
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (occurrence : History.Occurrence labelled.continuation) :
    labelled.label (labelled.newOccurrence occurrence) =
      .inr .distinguished :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrence_label_is_residual occurrence

theorem continuation_occurrences_unique
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (first second : History.Occurrence labelled.continuation) :
    first = second :=
  labelled.toSegmentedResidualExtension
    |>.newOccurrences_unique first second

end FaithfullyLabelledPerimeterExtension

structure PositiveContinuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) where
  path : History.Positive
    (@GeneratedStep P) (perimeterEndpoint P) history.endpoint
  historyExact : extension.continuation = path.toHistory

namespace PositiveContinuation

def toResidualPositive
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {labelled : FaithfullyLabelledPerimeterExtension P history}
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence labelled.continuation) :=
  { occurrence :=
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence }

end PositiveContinuation

namespace FaithfullyLabelledPerimeterExtension

def reconstructedInternalCompletion
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    SegmentedResidualRole.ExactInternalCompletion
      labelled.toSegmentedResidualExtension.toResidualUniquenessKernel :=
  labelled.toSegmentedResidualExtension.reconstructInternalCompletion
    positive.toResidualPositive

theorem reconstructed_roleToOccurrence_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (position : NonClosingPosition P.perimeter) :
    (labelled.reconstructedInternalCompletion positive
      |>.toExactInternalRealization).roleToOccurrence position =
        requirementToOccurrence P position :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_roleToOccurrence_agrees
      positive.toResidualPositive position

theorem reconstructed_occurrenceToRole_agrees
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (labelled.reconstructedInternalCompletion positive).occurrenceToRole
        occurrence = occurrenceToRequirement P occurrence :=
  labelled.toSegmentedResidualExtension
    |>.reconstructed_occurrenceToRole_agrees
      positive.toResidualPositive occurrence

end FaithfullyLabelledPerimeterExtension

def oneStepAfterPerimeter_positiveContinuation
    (P : CircularPresentation) :
    PositiveContinuation (oneStepAfterPerimeter_is_extension P) :=
  { path :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

def History.exactlyOneOfPositiveAndUnique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (unique :
      (first second : History.Occurrence positive.toHistory) →
        first = second) :
    History.ExactlyOne positive.toHistory := by
  cases positive with
  | mk predecessor priorHistory lastStep =>
      cases priorHistory with
      | root => exact .single lastStep
      | extend previous penultimateStep =>
          have impossible := unique
            (.last : History.Occurrence
              (.extend (.extend previous penultimateStep) lastStep))
            (.earlier (.last : History.Occurrence
              (.extend previous penultimateStep)))
          cases impossible

def positiveContinuation_exactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    History.ExactlyOne labelled.continuation :=
  let pathExactlyOne : History.ExactlyOne positive.path.toHistory :=
    History.exactlyOneOfPositiveAndUnique positive.path fun first second =>
      transportOccurrence_injective positive.historyExact.symm
        (labelled.continuation_occurrences_unique
          (transportOccurrence positive.historyExact.symm first)
          (transportOccurrence positive.historyExact.symm second))
  cast
    (congrArg
      (fun continuation => History.ExactlyOne continuation)
      positive.historyExact.symm)
    pathExactlyOne

theorem rootContinuation_not_positive
    (P : CircularPresentation) :
    PositiveContinuation (identityPerimeterExtension P) → False := by
  intro positive
  have equality := positive.historyExact
  cases positive.path with
  | mk predecessor priorHistory lastStep =>
      cases equality

structure FinalBoundaryOccurrence
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  labelled : FaithfullyLabelledPerimeterExtension P history
  positive : PositiveContinuation labelled.extension
  continuationOccurrence : History.Occurrence labelled.continuation
  occurrenceIsCanonical :
    continuationOccurrence =
      transportOccurrence positive.historyExact.symm
        positive.path.lastOccurrence
  labelIsFinal :
    labelled.label (labelled.newOccurrence continuationOccurrence) =
      .inr .distinguished

def finalBoundaryOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (labelled : FaithfullyLabelledPerimeterExtension P history)
    (positive : PositiveContinuation labelled.extension) :
    FinalBoundaryOccurrence P history :=
  let occurrence :=
    transportOccurrence positive.historyExact.symm
      positive.path.lastOccurrence
  { labelled := labelled
    positive := positive
    continuationOccurrence := occurrence
    occurrenceIsCanonical := rfl
    labelIsFinal := labelled.newOccurrence_label_is_final occurrence }

namespace FinalBoundaryOccurrence

def historyOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.Occurrence history.history :=
  boundary.labelled.newOccurrence boundary.continuationOccurrence

def locatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.LocatedStep (@GeneratedStep P) :=
  boundary.continuationOccurrence.locatedStep

def source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.source

def target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    PositiveConstitution P :=
  boundary.locatedStep.target

def step
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.locatedStep.step

def step_is_generatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    GeneratedStep boundary.source boundary.target :=
  boundary.step

def continuationExactlyOne
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    History.ExactlyOne boundary.labelled.continuation :=
  positiveContinuation_exactlyOne boundary.labelled boundary.positive

theorem uniqueContinuationOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history)
    (occurrence : History.Occurrence boundary.labelled.continuation) :
    occurrence = boundary.continuationOccurrence :=
  boundary.labelled.continuation_occurrences_unique
    occurrence boundary.continuationOccurrence

theorem source_is_perimeterEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source = perimeterEndpoint P :=
  boundary.continuationExactlyOne.locatedStep_source
    boundary.continuationOccurrence

theorem target_is_historyEndpoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = history.endpoint :=
  boundary.continuationExactlyOne.locatedStep_target
    boundary.continuationOccurrence

theorem target_is_canonicalTarget
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target = canonicalTarget (perimeterEndpoint P) := by
  exact boundary.step.formedByFreeLayer.trans
    (congrArg canonicalTarget boundary.source_is_perimeterEndpoint)

theorem source_cursor_is_boundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.source.1 = .within (.boundary P.perimeter.finalNode) :=
  (congrArg Sigma.fst boundary.source_is_perimeterEndpoint).trans
    (perimeterEndpoint_cursor_boundary P)

theorem target_cursor_is_beyond_first
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    boundary.target.1 = .beyond .first := by
  exact (congrArg Sigma.fst boundary.target_is_canonicalTarget).trans
    (generate_after_perimeter_is_beyond P)

theorem compatibility_is_leaveBoundary
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    HEq boundary.step.compatibility
      (ReturnedCompatible.leaveBoundary P.perimeter.finalNode) := by
  have exactCompatibility := boundary.step.compatibilityWitnessExact
  exact exactCompatibility.trans (by
    rw [boundary.source_cursor_is_boundary]
    rfl)

end FinalBoundaryOccurrence

/- The interpretation keeps the actual free boundary step and the invoked
   circular junction in one positive witness without identifying them.  It
   also records the exact formation, provenance and transported obstruction
   carried by the actual occurrence. -/
structure FinalClosureInterpretation
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  boundary : FinalBoundaryOccurrence P history
  actualStepCompatibility :
    ReturnedCompatible P
      (implicitRead boundary.source)
      (explicitRead boundary.target)
  actualStepCompatibilityIsExact :
    actualStepCompatibility = boundary.step.compatibility
  junction : FinalJunctionCompatibility P
  junctionIsDistinguished : junction = P.finalJunction
  formationRecord : FormationRecord P boundary.target.2.1
  formationRecordIsStepExact :
    formationRecord = boundary.step.currentFormationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      boundary.source boundary.target.2.1
  provenanceRecordIsStepExact :
    provenanceRecord = boundary.step.sourceProvenanceInscribedInTarget
  sourceObstruction : PositiveClosureObstruction P
  sourceObstructionIsExact :
    sourceObstruction =
      boundary.source.2.1.1.inheritedClosureObstruction
  targetObstruction : PositiveClosureObstruction P
  targetObstructionIsExact :
    targetObstruction =
      boundary.target.2.1.1.inheritedClosureObstruction
  targetObstructionIsInherited : targetObstruction = sourceObstruction
  targetObstructionIsInitial :
    targetObstruction = P.positiveClosureObstruction

def finalClosureInterpretation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (boundary : FinalBoundaryOccurrence P history) :
    FinalClosureInterpretation P history :=
  { boundary := boundary
    actualStepCompatibility := boundary.step.compatibility
    actualStepCompatibilityIsExact := rfl
    junction := P.finalJunction
    junctionIsDistinguished := rfl
    formationRecord := boundary.step.currentFormationRecord
    formationRecordIsStepExact := rfl
    provenanceRecord := boundary.step.sourceProvenanceInscribedInTarget
    provenanceRecordIsStepExact := rfl
    sourceObstruction :=
      boundary.source.2.1.1.inheritedClosureObstruction
    sourceObstructionIsExact := rfl
    targetObstruction :=
      boundary.target.2.1.1.inheritedClosureObstruction
    targetObstructionIsExact := rfl
    targetObstructionIsInherited :=
      boundary.step.inheritedClosureObstructionExact
    targetObstructionIsInitial :=
      (congrArg
        (fun state : PositiveConstitution P =>
          state.2.1.1.inheritedClosureObstruction)
        boundary.target_is_historyEndpoint).trans
        (RootedGeneratedHistory.terminalClosureObstruction_is_initial history) }

namespace FinalClosureInterpretation

def actualFreeStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    GeneratedStep interpretation.boundary.source
      interpretation.boundary.target :=
  interpretation.boundary.step

def invokedFinalJunction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    FinalJunctionCompatibility P :=
  interpretation.junction

theorem sourceObstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.sourceObstruction = P.positiveClosureObstruction :=
  interpretation.targetObstructionIsInherited.symm.trans
    interpretation.targetObstructionIsInitial

theorem actualFreeStep_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    implicitRead interpretation.boundary.source =
      .source P.perimeter.finalNode.implicit := by
  rw [interpretation.boundary.source_is_perimeterEndpoint]
  change implicitAt (perimeterEndpoint P).1 = _
  rw [perimeterEndpoint_cursor_boundary]
  rfl

theorem actualFreeStep_target_is_freeExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    explicitRead interpretation.boundary.target =
      .formed (.beyond .first) := by
  change explicitAt interpretation.boundary.target.1 = _
  rw [interpretation.boundary.target_cursor_is_beyond_first]
  rfl

def invokedFinalJunction_source
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Implicit :=
  P.perimeter.finalNode.implicit

def invokedFinalJunction_target
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (_interpretation : FinalClosureInterpretation P history) : P.Explicit :=
  P.initialNode.explicit

theorem invokedFinalJunction_source_is_terminalImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_source =
      P.perimeter.finalNode.implicit :=
  rfl

theorem invokedFinalJunction_target_is_initialExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    interpretation.invokedFinalJunction_target =
      P.initialNode.explicit :=
  rfl

end FinalClosureInterpretation

structure ConstitutiveClosureAttachment
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  formationRecord :
    FormationRecord P interpretation.boundary.target.2.1
  formationRecordIsExact :
    formationRecord = interpretation.formationRecord
  provenanceRecord :
    HistoricalProvenanceRecord P
      interpretation.boundary.source
      interpretation.boundary.target.2.1
  provenanceRecordIsExact :
    provenanceRecord = interpretation.provenanceRecord
  obstruction : PositiveClosureObstruction P
  obstructionIsExact : obstruction = interpretation.targetObstruction

def ConstitutiveClosureAttachment.canonical
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) :
    ConstitutiveClosureAttachment interpretation :=
  { formationRecord := interpretation.formationRecord
    formationRecordIsExact := rfl
    provenanceRecord := interpretation.provenanceRecord
    provenanceRecordIsExact := rfl
    obstruction := interpretation.targetObstruction
    obstructionIsExact := rfl }

namespace ConstitutiveClosureAttachment

theorem formationRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.formationRecord =
      interpretation.boundary.step.currentFormationRecord :=
  attachment.formationRecordIsExact.trans
    interpretation.formationRecordIsStepExact

theorem provenanceRecordIsStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.provenanceRecord =
      interpretation.boundary.step.sourceProvenanceInscribedInTarget :=
  attachment.provenanceRecordIsExact.trans
    interpretation.provenanceRecordIsStepExact

theorem obstructionIsInitial
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attachment : ConstitutiveClosureAttachment interpretation) :
    attachment.obstruction = P.positiveClosureObstruction :=
  attachment.obstructionIsExact.trans
    interpretation.targetObstructionIsInitial

end ConstitutiveClosureAttachment

structure BilateralClosureAttemptAt
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (interpretation : FinalClosureInterpretation P history) where
  attachment : ConstitutiveClosureAttachment interpretation
  explicitTotalization : ExplicitTotalization P
  implicitTotalization : ImplicitTotalization P

namespace BilateralClosureAttemptAt

def explicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (explicitTotalizationContractsClosureDifference
        attempt.explicitTotalization).poleContraction }

def implicitContraction
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := attempt.attachment.obstruction.provenance
    poleContraction :=
      (implicitTotalizationContractsClosureDifference
        attempt.implicitTotalization).poleContraction }

structure Contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) where
  explicitSide : ContractedClosureDifference P
  explicitSideIsDerived : explicitSide = attempt.explicitContraction
  implicitSide : ContractedClosureDifference P
  implicitSideIsDerived : implicitSide = attempt.implicitContraction

def contractions
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) :
    attempt.Contractions :=
  { explicitSide := attempt.explicitContraction
    explicitSideIsDerived := rfl
    implicitSide := attempt.implicitContraction
    implicitSideIsDerived := rfl }

def rejectExplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.explicitContraction.initialPoleContraction

def rejectImplicit
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {interpretation : FinalClosureInterpretation P history}
    (attempt : BilateralClosureAttemptAt interpretation) : False :=
  attempt.attachment.obstruction.rejectsContraction
    attempt.implicitContraction.initialPoleContraction

end BilateralClosureAttemptAt

structure CircularRefinement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  extension : PerimeterExtension P history
  labelling : FaithfulPerimeterLabelling P history extension
  realizesNonClosing :
    (occurrence : History.Occurrence history.history) →
    (position : NonClosingPosition P.perimeter) →
    labelling.label occurrence = .inl position →
      RequirementOccurrenceAgreement P history position occurrence
  realizesFinal :
    (positive : PositiveContinuation extension) →
      BilateralClosureAttemptAt
        (finalClosureInterpretation
          (finalBoundaryOccurrence
            { extension := extension, labelling := labelling }
            positive))

namespace CircularRefinement

def toLabelled
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    FaithfullyLabelledPerimeterExtension P history :=
  { extension := refinement.extension
    labelling := refinement.labelling }

def continuation
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    GeneratedHistory (perimeterEndpoint P) history.endpoint :=
  refinement.extension.continuation

def recompose
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.append (perimeterHistory P) refinement.continuation =
      history.history :=
  refinement.extension.recompose

def label
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    History.Occurrence history.history → CircularRequirement P :=
  refinement.labelling.label

def preservesNonClosingLabels
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    refinement.label (refinement.extension.oldOccurrence position) =
      .inl position :=
  refinement.labelling.preservesNonClosingLabels position

def requirementFaithful
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (first second : History.Occurrence history.history) :
    refinement.label first = refinement.label second → first = second :=
  refinement.labelling.requirementFaithful first second

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  refinement.extension.oldOccurrence position

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (occurrence : History.Occurrence refinement.continuation) :
    History.Occurrence history.history :=
  refinement.extension.newOccurrence occurrence

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence refinement.continuation) :
    refinement.oldOccurrence position ≠
      refinement.newOccurrence occurrence := by
  exact refinement.extension.old_new_occurrences_disjoint position occurrence

theorem newOccurrence_cannotReuseNonClosingRequirement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history)
    (newOccurrence : History.Occurrence refinement.continuation)
    (position : NonClosingPosition P.perimeter)
    (labelEquality :
      refinement.label (refinement.newOccurrence newOccurrence) =
        .inl position) : False := by
  exact refinement.toLabelled.newOccurrence_cannotReuseNonClosingRequirement
    newOccurrence position labelEquality

end CircularRefinement

def identityCircularRefinement (P : CircularPresentation) :
    CircularRefinement P (perimeterDeployment P) :=
  { extension := identityPerimeterExtension P
    labelling :=
      { label := fun occurrence =>
          .inl (occurrenceToRequirement P occurrence)
        preservesNonClosingLabels := by
          intro position
          exact congrArg Sum.inl
            (requirementToOccurrence_toRequirement P position)
        requirementFaithful := by
          intro first second labelEquality
          have positionEquality :
              occurrenceToRequirement P first =
                occurrenceToRequirement P second :=
            Sum.inl.inj labelEquality
          exact (occurrenceToRequirement_toOccurrence P first).symm.trans
            ((congrArg (requirementToOccurrence P) positionEquality).trans
              (occurrenceToRequirement_toOccurrence P second)) }
    realizesNonClosing := by
      intro occurrence position labelEquality
      have positionEquality :
          occurrenceToRequirement P occurrence = position :=
        Sum.inl.inj labelEquality
      cases positionEquality
      have roundTrip := occurrenceToRequirement_toOccurrence P occurrence
      exact RequirementOccurrenceAgreement.transportOccurrence roundTrip
        (canonicalRequirementAgreement P _)
    realizesFinal := fun positive =>
      False.elim (rootContinuation_not_positive P positive) }


end StrongPerimetralTurning
