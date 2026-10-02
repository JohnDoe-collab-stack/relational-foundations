import Constitution.CanonicalDeployment
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Faithful refinements and the final junction -/

def transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    History.Occurrence first → History.Occurrence second := by
  cases equality
  exact id

theorem transportOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second) :
    Function.Injective (transportOccurrence equality) := by
  cases equality
  intro left right same
  exact same

theorem locatedStep_transportOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {first second : History Step source target}
    (equality : first = second)
    (occurrence : History.Occurrence first) :
    (transportOccurrence equality occurrence).locatedStep =
      occurrence.locatedStep := by
  cases equality
  rfl

namespace History

/- An occurrence whose located step is exactly a generated step from the
   source of the history determines an initial one-step factorization.  The
   proof recurses on occurrence data.  A nonempty prefix before that occurrence
   would be a positive generated history returning to the same source. -/
def factorInitialGeneratedStep
    {P : CircularPresentation}
    {source middle target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (step : GeneratedStep source middle)
    (occurrence : History.Occurrence history)
    (locatedStepExact :
      occurrence.locatedStep =
        (⟨source, middle, step⟩ : History.LocatedStep (@GeneratedStep P))) :
    Σ continuation : GeneratedHistory middle target,
      { recompose : History.append (.extend .root step) continuation = history //
        transportOccurrence recompose
          (History.embedLeftOccurrence
            (.last : History.Occurrence (.extend .root step))
            continuation) = occurrence } :=
  match occurrence with
  | @Occurrence.last _ _ _ _ _ prior lastStep => by
      cases locatedStepExact
      cases prior with
      | root =>
          exact ⟨.root, ⟨rfl, rfl⟩⟩
      | extend priorHistory previousStep =>
          let positive : History.Positive (@GeneratedStep P) source source :=
            ⟨_, priorHistory, previousStep⟩
          exact False.elim
            (positiveGeneratedHistory_source_ne_target positive rfl)
  | @Occurrence.earlier _ _ _ _ _ prior lastStep earlier => by
      rcases factorInitialGeneratedStep prior step earlier locatedStepExact with
        ⟨continuation, ⟨recompose, occurrenceExact⟩⟩
      cases recompose
      exact ⟨.extend continuation lastStep, ⟨rfl,
        congrArg
          (fun occurrence =>
            History.Occurrence.earlier (step := lastStep) occurrence)
          occurrenceExact⟩⟩

/- Once the initial step has been factored, any distinct occurrence belongs to
   the right-hand continuation.  Classification is performed on occurrence
   data, while the inequality is used only to eliminate the impossible old
   branch. -/
def extractRightOccurrenceAfterSingle
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstStep : Step source middle)
    (continuation : History Step middle target)
    {history : History Step source target}
    (recompose :
      History.append (.extend .root firstStep) continuation = history)
    (occurrence : History.Occurrence history)
    (notFirst :
      transportOccurrence recompose
        (History.embedLeftOccurrence
          (.last : History.Occurrence (.extend .root firstStep)) continuation) ≠
        occurrence) :
    Σ newOccurrence : History.Occurrence continuation,
      PLift (transportOccurrence recompose
        (History.embedRightOccurrence
          (.extend .root firstStep) newOccurrence) = occurrence) := by
  cases recompose
  cases History.classifyAppendOccurrence
      (.extend .root firstStep) continuation occurrence with
  | inl oldData =>
      rcases oldData with ⟨oldOccurrence, reconstruction⟩
      cases oldOccurrence with
      | last => exact False.elim (notFirst reconstruction.down)
      | earlier impossible => exact nomatch impossible
  | inr newData =>
      rcases newData with ⟨newOccurrence, reconstruction⟩
      exact ⟨newOccurrence, ⟨reconstruction.down⟩⟩

end History

/- Recursive structural factorization of a canonical perimeter deployment from
   exact, injective occurrences inside a genuine generated history.  No
   numerical rank or length is used. -/
def factorDeployRemainingFromExactOccurrences
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (target : PositiveConstitution P) →
    (history : GeneratedHistory
      (positiveAtRemaining P remaining data difference) target) →
    (realize : NonClosingPosition remaining → History.Occurrence history) →
    Function.Injective realize →
    ((position : NonClosingPosition remaining) →
      (realize position).locatedStep =
        positionLocatedStep P data difference position) →
    Σ continuation : GeneratedHistory
        (deployRemaining P remaining data difference).1 target,
      PLift (History.append
        (deployRemaining P remaining data difference).2 continuation = history
      )
  | .boundary node, data, difference, target, history,
      _realize, _realizeInjective, _locatedStepExact =>
      ⟨history, ⟨History.root_append history⟩⟩
  | .advance compatible tail, data, difference, target, history,
      realize, realizeInjective, locatedStepExact => by
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let next := canonicalTarget source
      have firstLocatedStepExact :
          (realize (.here : NonClosingPosition (.advance compatible tail))).locatedStep =
            (⟨source, next, generatedStepOfFreeK source⟩ :
              History.LocatedStep (@GeneratedStep P)) := by
        have exactAtFirst := locatedStepExact
          (.here : NonClosingPosition (.advance compatible tail))
        dsimp [positionLocatedStep, positionSourceState,
          positionSourceStateAux, positionTargetState, source, next] at exactAtFirst
        exact exactAtFirst
      rcases History.factorInitialGeneratedStep history
          (generatedStepOfFreeK source) (realize .here) firstLocatedStepExact with
        ⟨afterFirst, ⟨firstRecompose, firstOccurrenceExact⟩⟩
      have laterNotFirst (position : NonClosingPosition tail) :
          transportOccurrence firstRecompose
            (History.embedLeftOccurrence
              (.last : History.Occurrence
                (.extend .root (generatedStepOfFreeK source))) afterFirst) ≠
              realize (.later position) := by
        intro equality
        have realizedEquality : realize .here = realize (.later position) :=
          firstOccurrenceExact.symm.trans equality
        have positionEquality := realizeInjective realizedEquality
        cases positionEquality
      let tailOccurrenceData := fun position : NonClosingPosition tail =>
        History.extractRightOccurrenceAfterSingle
          (generatedStepOfFreeK source) afterFirst firstRecompose
          (realize (.later position)) (laterNotFirst position)
      let tailRealize :
          NonClosingPosition tail → History.Occurrence afterFirst :=
        fun position => (tailOccurrenceData position).1
      have tailRealizeInjective : Function.Injective tailRealize := by
        intro first second equality
        have embeddedEquality :
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize first)) =
            transportOccurrence firstRecompose
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK source))
                (tailRealize second)) :=
          congrArg
            (fun occurrence =>
              transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source)) occurrence))
            equality
        have realizedEquality :
            realize (.later first) = realize (.later second) :=
            (tailOccurrenceData first).2.down.symm.trans
            (embeddedEquality.trans (tailOccurrenceData second).2.down)
        exact NonClosingPosition.later.inj
          (realizeInjective realizedEquality)
      have tailLocatedStepExact
          (position : NonClosingPosition tail) :
          (tailRealize position).locatedStep =
            positionLocatedStep P next.2.1 next.2.2 position := by
        have reconstructed := (tailOccurrenceData position).2.down
        calc
          (tailRealize position).locatedStep
              = (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).locatedStep :=
                (History.locatedStep_embedRight
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position)).symm
          _ = (transportOccurrence firstRecompose
                (History.embedRightOccurrence
                  (.extend .root (generatedStepOfFreeK source))
                  (tailRealize position))).locatedStep :=
                (locatedStep_transportOccurrence firstRecompose
                  (History.embedRightOccurrence
                    (.extend .root (generatedStepOfFreeK source))
                    (tailRealize position))).symm
          _ = (realize (.later position)).locatedStep :=
                congrArg
                  (fun occurrence : History.Occurrence history =>
                    occurrence.locatedStep) reconstructed
          _ = positionLocatedStep P data difference (.later position) :=
                locatedStepExact (.later position)
          _ = positionLocatedStep P next.2.1 next.2.2 position := by
                rfl
      rcases factorDeployRemainingFromExactOccurrences P tail
          next.2.1 next.2.2 target afterFirst tailRealize
          tailRealizeInjective tailLocatedStepExact with
        ⟨continuation, tailRecompose⟩
      refine ⟨continuation, ⟨?_⟩⟩
      change History.append
          (History.append
            (.extend .root (generatedStepOfFreeK source))
            (deployRemaining P tail next.2.1 next.2.2).2)
          continuation = history
      calc
        History.append
            (History.append
              (.extend .root (generatedStepOfFreeK source))
              (deployRemaining P tail next.2.1 next.2.2).2)
            continuation
            = History.append
                (.extend .root (generatedStepOfFreeK source))
                (History.append
                  (deployRemaining P tail next.2.1 next.2.2).2
                  continuation) :=
              History.append_associative _ _ _
        _ = History.append
              (.extend .root (generatedStepOfFreeK source)) afterFirst :=
            congrArg
              (History.append
                (.extend .root (generatedStepOfFreeK source)))
              tailRecompose.down
        _ = history := firstRecompose

structure PerimeterExtension
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  continuation :
    GeneratedHistory (perimeterEndpoint P) history.endpoint
  recompose :
    History.append (perimeterHistory P) continuation = history.history

namespace ExactNonClosingRealization

/- Exact local realization inside a genuine rooted generated history is already
   enough to reconstruct the canonical perimeter as an initial extension. -/
def toPerimeterExtension
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    PerimeterExtension P history := by
  let factor :=
    factorDeployRemainingFromExactOccurrences P P.perimeter
      FreeConstitution.root BoundaryDifference.initial history.endpoint
      history.history realization.realize realization.realize_injective
      (fun position => (realization.agreement position).locatedStepExact)
  exact
      { continuation := factor.1
        recompose := factor.2.down }

end ExactNonClosingRealization

namespace PerimeterExtension

def oldOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedLeftOccurrence
      (requirementToOccurrence P position) extension.continuation)

def newOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (occurrence : History.Occurrence extension.continuation) :
    History.Occurrence history.history :=
  transportOccurrence extension.recompose
    (History.embedRightOccurrence (perimeterHistory P) occurrence)

def oldOccurrenceAgreement
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter) :
    RequirementOccurrenceAgreement P history position
      (extension.oldOccurrence position) := by
  refine ⟨?_⟩
  exact congrArg
    (fun located : History.LocatedStep (@GeneratedStep P) => located.source.1)
    ((locatedStep_transportOccurrence extension.recompose
        (History.embedLeftOccurrence
          (requirementToOccurrence P position) extension.continuation)).trans
      ((History.locatedStep_embedLeft
        (requirementToOccurrence P position) extension.continuation).trans
          (canonicalRequirementAgreement P position).locatedStepExact))

theorem oldOccurrence_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    Function.Injective extension.oldOccurrence := by
  intro first second equality
  have embeddedEquality :=
    transportOccurrence_injective extension.recompose equality
  have canonicalEquality :=
    History.embedLeftOccurrence_injective extension.continuation embeddedEquality
  exact requirementToOccurrence_injective P canonicalEquality

def toExactNonClosingRealization
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history) :
    ExactNonClosingRealization P history :=
  { realize := extension.oldOccurrence
    agreement := extension.oldOccurrenceAgreement }

theorem old_new_occurrences_disjoint
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (extension : PerimeterExtension P history)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence extension.continuation) :
    extension.oldOccurrence position ≠ extension.newOccurrence occurrence := by
  intro equality
  have beforeTransport :=
    transportOccurrence_injective extension.recompose equality
  exact History.leftRightDisjoint
    (requirementToOccurrence P position) occurrence beforeTransport

end PerimeterExtension

def identityPerimeterExtension (P : CircularPresentation) :
    PerimeterExtension P (perimeterDeployment P) :=
  { continuation := .root
    recompose := rfl }

def oneStepAfterPerimeter_is_extension (P : CircularPresentation) :
    PerimeterExtension P (oneStepAfterPerimeter P) :=
  { continuation := .extend .root (generate_after_perimeter P).2
    recompose := rfl }

/-! ## Direct circular residual-determination core

This is the core consumed by the canonical one-step construction.  Its label
is defined directly on the exactly-one continuation occurrence; no rich
perimeter realization or residual-labelling adapter is involved. -/
def oneStepResidualDeterminationCore
    (P : CircularPresentation) :
    SegmentedResidualRole.ResidualDeterminationCore
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) := by
  let exactlyOne :
      History.ExactlyOne
        (oneStepAfterPerimeter_is_extension P).continuation := by
    change History.ExactlyOne
      (.extend .root (generate_after_perimeter P).2)
    exact .single (generate_after_perimeter P).2
  refine
    { newLabel := fun _ => .inr .distinguished
      newLabelInjective := ?_
      noInternalReuse := ?_ }
  · intro first second _
    exact (exactlyOne.occurrence_unique first).trans
      (exactlyOne.occurrence_unique second).symm
  · intro occurrence role equality
    cases equality

def oneStepCorePositive
    (P : CircularPresentation) :
    SegmentedResidualRole.PositiveNewPart
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation) :=
  { occurrence := .last }

def oneStepCoreResidualOccurrence
    (P : CircularPresentation) :
    SegmentedResidualRole.CoreUniqueResidualOccurrence
      (oneStepResidualDeterminationCore P) :=
  SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence
    (oneStepResidualDeterminationCore P)
    (oneStepCorePositive P)

def oneStepCoreSegmentedBoundary
    (P : CircularPresentation) :
    AbstractSegmentedTurning.CoreSegmentedBoundary
      (perimetralBoundaryGenerator P)
      (NonClosingPosition P.perimeter)
      (FinalRequirement P)
      (History.Occurrence
        (oneStepAfterPerimeter_is_extension P).continuation)
      (finalRequirementContractible P) :=
  { core := oneStepResidualDeterminationCore P
    positive := oneStepCorePositive P }

def oneStepAfterPerimeter_nonClosingRealization
    (P : CircularPresentation) :
    ExactNonClosingRealization P (oneStepAfterPerimeter P) :=
  (oneStepAfterPerimeter_is_extension P).toExactNonClosingRealization


end StrongPerimetralTurning
