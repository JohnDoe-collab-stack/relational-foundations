import Constitution.ConstitutedHistory
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Canonical deployment of the non-closing perimeter -/

def positiveAtRemaining
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) : PositiveConstitution P :=
  ⟨.within remaining, data, difference⟩

def deployRemaining
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    Σ target : PositiveConstitution P,
      GeneratedHistory (positiveAtRemaining P remaining data difference) target
  | @PerimeterSpine.boundary _ _ _ _ _ node, data, difference =>
      ⟨positiveAtRemaining P (.boundary node) data difference, .root⟩
  | @PerimeterSpine.advance _ _ _ _ _ node _nextNode compatible tail,
      data, difference =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let next := canonicalTarget source
      let rest := deployRemaining P tail next.2.1 next.2.2
      ⟨rest.1,
        History.append
          (.extend .root (generatedStepOfFreeK source))
          rest.2⟩

def perimeterDeployment (P : CircularPresentation) : RootedGeneratedHistory P :=
  let deployed := deployRemaining P P.perimeter
    FreeConstitution.root BoundaryDifference.initial
  ⟨deployed.1, deployed.2⟩

def perimeterEndpoint (P : CircularPresentation) : PositiveConstitution P :=
  (perimeterDeployment P).endpoint

def perimeterHistory (P : CircularPresentation) :
    GeneratedHistory (initialPositive P) (perimeterEndpoint P) :=
  (perimeterDeployment P).history

theorem deployRemaining_finalCursor
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    (deployRemaining P remaining data difference).1.1 =
      .within (.boundary remaining.finalNode) := by
  induction remaining with
  | boundary node => rfl
  | @advance node nextNode compatible tail ih =>
      change
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).1.1 =
          .within (.boundary tail.finalNode)
      exact ih _ _

theorem perimeterEndpoint_cursor_boundary
    (P : CircularPresentation) :
    (perimeterEndpoint P).1 =
      .within (.boundary P.perimeter.finalNode) :=
  deployRemaining_finalCursor P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

def generate_after_perimeter
    (P : CircularPresentation) :
    Σ target : PositiveConstitution P,
      GeneratedStep (perimeterEndpoint P) target :=
  generate (perimeterEndpoint P)

theorem generate_after_perimeter_is_beyond
    (P : CircularPresentation) :
    (generate_after_perimeter P).1.1 = .beyond .first := by
  change advanceCursor (perimeterEndpoint P).1 = .beyond .first
  rw [perimeterEndpoint_cursor_boundary]
  rfl

def oneStepAfterPerimeter (P : CircularPresentation) :
    RootedGeneratedHistory P :=
  appendGenerated (perimeterDeployment P) (generate_after_perimeter P)

def oneStepAfterPerimeterStrict
    (P : CircularPresentation) :
    StrictConstitutivePrefix
      (perimeterDeployment P) (oneStepAfterPerimeter P) :=
  { continuation :=
      { predecessor := perimeterEndpoint P
        priorHistory := .root
        lastStep := (generate_after_perimeter P).2 }
    historyExact := rfl }

theorem oneStepAfterPerimeter_ne
    (P : CircularPresentation) :
    oneStepAfterPerimeter P ≠ perimeterDeployment P :=
  fun equality => strictPrefix_ne (oneStepAfterPerimeterStrict P) equality

/- The canonical perimeter and its freely generated successor instantiate the
   circle-independent boundary generator. -/
def perimetralBoundaryGenerator
    (P : CircularPresentation) :
    AbstractSegmentedTurning.BoundaryGenerator
      (RootedGeneratedHistory P) (@StrictConstitutivePrefix P) :=
  { boundary := perimeterDeployment P
    continuation := oneStepAfterPerimeter P
    generates := oneStepAfterPerimeterStrict P
    extensionIrreflexive := fun _history strict =>
      strictPrefix_ne strict rfl }

inductive GeneratedOnlyPath
    {P : CircularPresentation} :
    {source target : PositiveConstitution P} →
    GeneratedHistory source target → Prop
  | root : GeneratedOnlyPath (.root : GeneratedHistory source source)
  | extend
      {source middle : PositiveConstitution P}
      {history : GeneratedHistory source middle}
      (generated : GeneratedOnlyPath history) :
      GeneratedOnlyPath
        (.extend history (generatedStepOfFreeK middle))

def prependGeneratedOnly
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {continuation : GeneratedHistory (canonicalTarget source) target}
    (generated : GeneratedOnlyPath continuation) :
    GeneratedOnlyPath
      (History.append
        (.extend .root (generatedStepOfFreeK source)) continuation) :=
  match generated with
  | .root => .extend .root
  | .extend previous => .extend (prependGeneratedOnly previous)

def deployRemaining_generatedOnly
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    GeneratedOnlyPath (deployRemaining P remaining data difference).2 := by
  induction remaining with
  | boundary node => exact .root
  | @advance node nextNode compatible tail ih =>
      exact prependGeneratedOnly (ih _ _)

def GeneratedOnlyByFreeConstruction
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) : Prop :=
  GeneratedOnlyPath history.history

def perimeterDeployment_generatedOnly
    (P : CircularPresentation) :
    GeneratedOnlyByFreeConstruction (perimeterDeployment P) :=
  deployRemaining_generatedOnly P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

inductive FreePartialPath
    (P : CircularPresentation) :
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference) → Prop
  | root :
      FreePartialPath P P.perimeter
        FreeConstitution.root
        BoundaryDifference.initial
        (.root : GeneratedHistory (initialPositive P) (initialPositive P))
  | advance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {data : FreeConstitution P (.within (.advance compatible tail))}
      {difference : BoundaryDifference P data}
      {history : GeneratedHistory (initialPositive P)
        (positiveAtRemaining P (.advance compatible tail) data difference)}
      (previous : FreePartialPath P (.advance compatible tail)
        data difference history) :
      FreePartialPath P tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        (.extend history
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference)))

namespace FreePartialPath

def rootedAt
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) :
    RootedGeneratedHistory P :=
  ⟨positiveAtRemaining P remaining data difference, history⟩

def completedRooted
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) :
    RootedGeneratedHistory P :=
  let deployed := deployRemaining P remaining data difference
  ⟨deployed.1, History.append history deployed.2⟩

theorem completion
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    {history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)}
    (partialPath : FreePartialPath P remaining data difference history) :
    completedRooted remaining data difference history =
      perimeterDeployment P := by
  induction partialPath with
  | root =>
      exact rootedHistoryEq
        (first := completedRooted P.perimeter
          FreeConstitution.root BoundaryDifference.initial History.root)
        (second := perimeterDeployment P)
        rfl
        (heq_of_eq
          (History.root_append
            (deployRemaining P P.perimeter
              FreeConstitution.root BoundaryDifference.initial).2))
  | @advance node nextNode compatible tail data difference history previous ih =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let one : GeneratedHistory source (canonicalTarget source) :=
        .extend .root (generatedStepOfFreeK source)
      let rest := deployRemaining P tail
        (canonicalTarget source).2.1 (canonicalTarget source).2.2
      have historyExact :
          History.append history (History.append one rest.2) =
            History.append (History.append history one) rest.2 :=
        (History.append_associative history one rest.2).symm
      have currentEqualsNext :
          completedRooted (.advance compatible tail) data difference history =
            completedRooted tail
              (canonicalTarget source).2.1
              (canonicalTarget source).2.2
              (.extend history (generatedStepOfFreeK source)) :=
        rootedHistoryEq rfl (heq_of_eq historyExact)
      exact currentEqualsNext.symm.trans ih

def finish
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (history : GeneratedHistory (initialPositive P)
      (positiveAtRemaining P remaining data difference)) →
    FreePartialPath P remaining data difference history →
    Σ finalData : FreeConstitution P
        (.within (.boundary remaining.finalNode)),
      Σ finalDifference : BoundaryDifference P finalData,
        Σ finalHistory : GeneratedHistory (initialPositive P)
          (positiveAtRemaining P (.boundary remaining.finalNode)
            finalData finalDifference),
          PLift (FreePartialPath P (.boundary remaining.finalNode)
            finalData finalDifference finalHistory)
  | @PerimeterSpine.boundary _ _ _ _ _ boundaryNode,
      data, difference, history, partialPath =>
      ⟨data, difference, history, ⟨partialPath⟩⟩
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, history, partialPath =>
      finish tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail)
            data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail)
            data difference)).2.2
        (.extend history
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail)
              data difference)))
        (.advance partialPath)

end FreePartialPath

inductive FreePartialRealization
    (P : CircularPresentation) : RootedGeneratedHistory P → Type _
  | ofPath
      {node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {remaining : PerimeterSpine P.Compatible node}
      {data : FreeConstitution P (.within remaining)}
      {difference : BoundaryDifference P data}
      {history : GeneratedHistory (initialPositive P)
        (positiveAtRemaining P remaining data difference)} :
      FreePartialPath P remaining data difference history →
      FreePartialRealization P
        ⟨positiveAtRemaining P remaining data difference, history⟩

def prefixFromCompletedRooted
    {P : CircularPresentation}
    (current : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (continuation : GeneratedHistory current.endpoint target)
    (completion : appendRooted current continuation = perimeterDeployment P) :
    ConstitutivePrefix current (perimeterDeployment P) :=
  Eq.rec
    (motive := fun completed _ => ConstitutivePrefix current completed)
    (⟨continuation, rfl⟩ :
      ConstitutivePrefix current (appendRooted current continuation))
    completion

def partial_is_prefix_of_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P} :
    FreePartialRealization P history →
      ConstitutivePrefix history (perimeterDeployment P)
  | .ofPath partialPath => by
      exact prefixFromCompletedRooted _
        (deployRemaining P _ _ _).2 partialPath.completion

def transportFreePartialRealization
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (equality : first = second) :
    FreePartialRealization P first → FreePartialRealization P second :=
  Eq.rec
    (motive := fun target _ =>
      FreePartialRealization P first → FreePartialRealization P target)
    (fun realization => realization)
    equality

def perimeterPartialPath (P : CircularPresentation) :
    FreePartialRealization P (perimeterDeployment P) := by
  let rootPath := FreePartialPath.root (P := P)
  let finished := FreePartialPath.finish P.perimeter
    FreeConstitution.root BoundaryDifference.initial History.root rootPath
  let finishedRooted : RootedGeneratedHistory P :=
    ⟨positiveAtRemaining P (.boundary P.perimeter.finalNode)
        finished.1 finished.2.1,
      finished.2.2.1⟩
  have exactPerimeter : finishedRooted = perimeterDeployment P := by
    simpa only [finishedRooted, FreePartialPath.completedRooted,
      deployRemaining, History.append] using
      finished.2.2.2.down.completion
  exact transportFreePartialRealization exactPerimeter
    (.ofPath finished.2.2.2.down)

def perimeterIsFreePartial (P : CircularPresentation) :
    FreePartialRealization P (perimeterDeployment P) :=
  perimeterPartialPath P

def deployPositionToOccurrence
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    NonClosingPosition remaining →
      History.Occurrence (deployRemaining P remaining data difference).2
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .here =>
      History.embedLeftOccurrence
        (.last : History.Occurrence
          (.extend .root (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference))))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).2
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .later position =>
      History.embedRightOccurrence
        (.extend .root (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail) data difference)))
        (deployPositionToOccurrence P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
          position)

def classifyDeploymentOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    {firstStep : Step source middle}
    (continuation : History Step middle target)
    (occurrence : History.Occurrence
      (History.append (.extend .root firstStep) continuation)) :
    PLift (occurrence = History.embedLeftOccurrence
      (.last : History.Occurrence (.extend .root firstStep)) continuation) ⊕
      (Σ later : History.Occurrence continuation,
        PLift (occurrence = History.embedRightOccurrence
          (.extend .root firstStep) later)) := by
  cases History.classifyAppendOccurrence
      (.extend .root firstStep) continuation occurrence with
  | inl firstData =>
      rcases firstData with ⟨first, reconstruction⟩
      cases first with
      | last =>
          apply Sum.inl
          exact ⟨reconstruction.down.symm⟩
      | earlier earlier => exact nomatch earlier
  | inr laterData =>
      rcases laterData with ⟨later, reconstruction⟩
      apply Sum.inr
      exact ⟨later, ⟨reconstruction.down.symm⟩⟩

def decodeDeploymentOccurrence
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) →
      Σ position : NonClosingPosition remaining,
        PLift (deployPositionToOccurrence P remaining data difference position =
          occurrence)
  | @PerimeterSpine.boundary _ _ _ _ _ boundaryNode,
      _data, _difference, occurrence => nomatch occurrence
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, occurrence =>
      match classifyDeploymentOccurrence
          (deployRemaining P tail
            (canonicalTarget
              (positiveAtRemaining P (.advance compatible tail)
                data difference)).2.1
            (canonicalTarget
              (positiveAtRemaining P (.advance compatible tail)
                data difference)).2.2).2
          occurrence with
      | .inl hereExact =>
          ⟨NonClosingPosition.here, ⟨hereExact.down.symm⟩⟩
      | .inr ⟨later, laterExact⟩ =>
          let decoded := decodeDeploymentOccurrence P tail
              (canonicalTarget
                (positiveAtRemaining P (.advance compatible tail)
                  data difference)).2.1
              (canonicalTarget
                (positiveAtRemaining P (.advance compatible tail)
                  data difference)).2.2
              later
          ⟨NonClosingPosition.later decoded.1,
            ⟨(congrArg
              (History.embedRightOccurrence
                (.extend .root (generatedStepOfFreeK
                  (positiveAtRemaining P (.advance compatible tail)
                    data difference))))
              decoded.2.down).trans laterExact.down.symm⟩⟩

def deployOccurrenceToPosition
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) :
    NonClosingPosition remaining :=
  (decodeDeploymentOccurrence P remaining data difference occurrence).1

theorem deployOccurrence_position_roundTrip
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (occurrence : History.Occurrence
      (deployRemaining P remaining data difference).2) :
    deployPositionToOccurrence P remaining data difference
      (deployOccurrenceToPosition P remaining data difference occurrence) =
        occurrence :=
  (decodeDeploymentOccurrence P remaining data difference occurrence).2.down

theorem deployPositionToOccurrence_injective
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    Function.Injective
      (deployPositionToOccurrence P remaining data difference) := by
  induction remaining with
  | boundary node =>
      intro first
      exact nomatch first
  | @advance node nextNode compatible tail inductionHypothesis =>
      intro first second equality
      cases first with
      | here =>
          cases second with
          | here => rfl
          | later second =>
              exact False.elim (History.leftRightDisjoint
                (.last : History.Occurrence
                  (.extend .root (generatedStepOfFreeK
                    (positiveAtRemaining P (.advance compatible tail)
                      data difference))))
                (deployPositionToOccurrence P tail _ _ second) equality)
      | later first =>
          cases second with
          | here =>
              exact False.elim (History.leftRightDisjoint
                (.last : History.Occurrence
                  (.extend .root (generatedStepOfFreeK
                    (positiveAtRemaining P (.advance compatible tail)
                      data difference))))
                (deployPositionToOccurrence P tail _ _ first) equality.symm)
          | later second =>
              apply congrArg NonClosingPosition.later
              apply inductionHypothesis _ _
              exact History.embedRightOccurrence_injective _ equality

theorem deployPosition_occurrence_roundTrip
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    deployOccurrenceToPosition P remaining data difference
      (deployPositionToOccurrence P remaining data difference position) =
        position := by
  induction position with
  | @here node nextNode compatible tail =>
      apply deployPositionToOccurrence_injective P
        (.advance compatible tail) data difference
      exact deployOccurrence_position_roundTrip P _ _ _
        (deployPositionToOccurrence P (.advance compatible tail)
          data difference .here)
  | @later node nextNode compatible tail position inductionHypothesis =>
      apply deployPositionToOccurrence_injective P
        (.advance compatible tail) data difference
      exact deployOccurrence_position_roundTrip P _ _ _
        (deployPositionToOccurrence P (.advance compatible tail)
          data difference (.later position))

def requirementToOccurrence
    (P : CircularPresentation) :
    NonClosingPosition P.perimeter →
      History.Occurrence (perimeterHistory P) :=
  deployPositionToOccurrence P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

def occurrenceToRequirement
    (P : CircularPresentation) :
    History.Occurrence (perimeterHistory P) →
      NonClosingPosition P.perimeter :=
  deployOccurrenceToPosition P P.perimeter
    FreeConstitution.root BoundaryDifference.initial

theorem occurrenceToRequirement_toOccurrence
    (P : CircularPresentation)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    requirementToOccurrence P (occurrenceToRequirement P occurrence) =
      occurrence :=
  deployOccurrence_position_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial occurrence

theorem requirementToOccurrence_toRequirement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    occurrenceToRequirement P (requirementToOccurrence P position) =
      position :=
  deployPosition_occurrence_roundTrip P P.perimeter
    FreeConstitution.root BoundaryDifference.initial position

/- These maps only reindex a supplied readout along the already established
   perimeter/occurrence correspondence.  They add no values and assert no
   semantic adequacy of the supplied readout. -/
def perimeterReadout
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : History.OccurrenceReadout (perimeterHistory P) Value) :
    NonClosingPosition P.perimeter → Value :=
  fun position => readout (requirementToOccurrence P position)

def occurrenceReadoutOfPerimeter
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : NonClosingPosition P.perimeter → Value) :
    History.OccurrenceReadout (perimeterHistory P) Value :=
  fun occurrence => readout (occurrenceToRequirement P occurrence)

theorem occurrenceReadoutOfPerimeter_perimeterReadout
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : History.OccurrenceReadout (perimeterHistory P) Value)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    occurrenceReadoutOfPerimeter (perimeterReadout readout) occurrence =
      readout occurrence := by
  change readout
      (requirementToOccurrence P (occurrenceToRequirement P occurrence)) =
    readout occurrence
  rw [occurrenceToRequirement_toOccurrence]

theorem perimeterReadout_occurrenceReadoutOfPerimeter
    {P : CircularPresentation}
    {Value : Type uV}
    (readout : NonClosingPosition P.perimeter → Value)
    (position : NonClosingPosition P.perimeter) :
    perimeterReadout (occurrenceReadoutOfPerimeter readout) position =
      readout position := by
  change readout
      (occurrenceToRequirement P (requirementToOccurrence P position)) =
    readout position
  rw [requirementToOccurrence_toRequirement]

theorem requirementToOccurrence_injective
    (P : CircularPresentation) :
    Function.Injective (requirementToOccurrence P) := by
  intro first second equality
  exact (requirementToOccurrence_toRequirement P first).symm.trans
    ((congrArg (occurrenceToRequirement P) equality).trans
      (requirementToOccurrence_toRequirement P second))

def positionSourceStateAux
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    NonClosingPosition remaining → PositiveConstitution P
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .here =>
      positiveAtRemaining P (.advance compatible tail) data difference
  | @PerimeterSpine.advance _ _ _ _ _ sourceNode _nextNode compatible tail,
      data, difference, .later position =>
      positionSourceStateAux P tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        position

def positionSourceState
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) : PositiveConstitution P :=
  positionSourceStateAux P remaining data difference position

def positionTargetState
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) : PositiveConstitution P :=
  canonicalTarget (positionSourceState P data difference position)

def positionSourceCursorReachAux
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    CursorReach P (.within remaining)
      (positionSourceState P data difference position).1 :=
  match remaining, position with
  | .advance _compatible _tail, .here => .root
  | .advance compatible tail, .later position =>
      let source :=
        positiveAtRemaining P (.advance compatible tail) data difference
      let target := canonicalTarget source
      have firstReach :
          CursorReach P (.within (.advance compatible tail)) target.1 :=
        .extend .root
          (generatedStepCursorAdvance (generatedStepOfFreeK source))
      CursorReach.trans firstReach
        (positionSourceCursorReachAux P tail target.2.1 target.2.2 position)

def positionSourceCursorReach
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    CursorReach P (.within remaining)
      (positionSourceState P data difference position).1 :=
  positionSourceCursorReachAux P remaining data difference position

def positionLocatedStep
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    History.LocatedStep (@GeneratedStep P) :=
  ⟨positionSourceState P data difference position,
    positionTargetState P data difference position,
    generatedStepOfFreeK (positionSourceState P data difference position)⟩

namespace NonClosingPrecedes

theorem sourceCursorFutureAt
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {first second : NonClosingPosition remaining}
    (precedes : NonClosingPrecedes remaining first second)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    Nonempty (CursorFuture P
      (positionSourceState P data difference first).1
      (positionSourceState P data difference second).1) := by
  induction precedes with
  | @here_later node nextNode nextCompatible tail position =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      let target := canonicalTarget source
      have firstFuture : CursorFuture P source.1 target.1 :=
        (generatedStepCursorAdvance (generatedStepOfFreeK source)).toFuture
      exact ⟨firstFuture.transReach
        (positionSourceCursorReach P target.2.1 target.2.2 position)⟩
  | @later_later node nextNode nextCompatible tail first second precedes inductionHypothesis =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      let target := canonicalTarget source
      exact inductionHypothesis target.2.1 target.2.2

end NonClosingPrecedes

namespace NonClosingNext

/- Canonically adjacent non-closing positions meet at exactly the same
   positive constitution: the target of the first required step is the source
   of the second.  This is structural adjacency, not a numerical rank fact. -/
theorem target_eq_source
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {first second : NonClosingPosition remaining}
    (next : NonClosingNext remaining first second)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data) :
    (positionLocatedStep P data difference first).target =
      (positionLocatedStep P data difference second).source := by
  induction next with
  | @here_next node nextNode thirdNode firstCompatible secondCompatible tail =>
      rfl
  | @later_next node nextNode nextCompatible tail first second next inductionHypothesis =>
      let source :=
        positiveAtRemaining P (.advance nextCompatible tail) data difference
      exact inductionHypothesis
        (canonicalTarget source).2.1
        (canonicalTarget source).2.2

end NonClosingNext


theorem deployPosition_locatedStep
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (position : NonClosingPosition remaining) :
    (deployPositionToOccurrence P remaining data difference position).locatedStep =
      positionLocatedStep P data difference position := by
  induction position with
  | @here sourceNode nextNode compatible tail =>
      exact History.locatedStep_embedLeft
        (.last : History.Occurrence
          (.extend .root (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail)
              data difference))))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail)
              data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail)
              data difference)).2.2).2
  | @later sourceNode nextNode compatible tail position inductionHypothesis =>
      exact (History.locatedStep_embedRight
        (.extend .root (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail)
            data difference)))
        (deployPositionToOccurrence P tail _ _ position)).trans
          (inductionHypothesis _ _)

def perimeterPositionSource
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) : PositiveConstitution P :=
  positionSourceState P FreeConstitution.root
    BoundaryDifference.initial position

def perimeterPositionTarget
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) : PositiveConstitution P :=
  positionTargetState P FreeConstitution.root
    BoundaryDifference.initial position

namespace NonClosingPrecedes

theorem sourceCursorFuture
    {P : CircularPresentation}
    {first second : NonClosingPosition P.perimeter}
    (precedes : NonClosingPrecedes P.perimeter first second) :
    Nonempty (CursorFuture P
      (perimeterPositionSource P first).1
      (perimeterPositionSource P second).1) :=
  sourceCursorFutureAt precedes
    FreeConstitution.root BoundaryDifference.initial

end NonClosingPrecedes

abbrev ExactCompatibleTransport := RelationalFoundations.ExactTransport

abbrev ExactProvenanceTransport := RelationalFoundations.ExactTransport

/- A generated occurrence in a rooted history is determined by its source
   cursor.  The proof stays at the structural layer: it follows the unary
   formation depth, uses the canonical generated successor, and excludes two
   distinct depths at one cursor by `CursorFuture.irreflexive`.  No numerical
   rank or readout is used. -/
theorem freeKCore_uniqueForCursorAgreement
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {code : BoundaryDifferenceCode P cursor}
    (first second : FreeKCore P cursor code) : first = second := by
  cases first with
  | mk formationTerm formationExact obstruction obstructionExact
      provenance provenanceExact =>
    cases second with
    | mk formationTerm' formationExact' obstruction' obstructionExact'
        provenance' provenanceExact' =>
      cases formationExact
      cases formationExact'
      cases obstructionExact
      cases obstructionExact'
      cases provenanceExact
      cases provenanceExact'
      rfl

theorem freeK_uniqueForCursorAgreement
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (first second : FreeK P previous difference) : first = second := by
  cases first with
  | mk core =>
    cases second with
    | mk core' =>
      exact congrArg FreeK.mk
        (freeKCore_uniqueForCursorAgreement core core')

theorem integrates_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : Integrates source) : first = second := by
  cases first with
  | mk firstLayer firstExact =>
    cases second with
    | mk secondLayer secondExact =>
      have layerExact : firstLayer = secondLayer :=
        freeK_uniqueForCursorAgreement firstLayer secondLayer
      cases layerExact
      rfl

theorem preservesProvenance_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : PreservesProvenance source target) : first = second := by
  cases first with
  | mk firstTarget firstIntegrated =>
    cases second with
    | mk secondTarget secondIntegrated =>
      cases firstTarget
      cases secondTarget
      exact congrArg (PreservesProvenance.mk rfl)
        (integrates_uniqueForCursorAgreement firstIntegrated secondIntegrated)

theorem integratesClosureObstruction_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : IntegratesClosureObstruction source) : first = second := by
  cases first
  cases second
  rfl

theorem continuesDifference_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : ContinuesDifference source) : first = second := by
  cases first
  cases second
  rfl

theorem freshBoundaryDifference_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : FreshBoundaryDifference source) : first = second := by
  cases first with
  | mk firstContinuation firstRecord firstRecordExact firstFresh =>
    cases second with
    | mk secondContinuation secondRecord secondRecordExact secondFresh =>
      have continuationExact : firstContinuation = secondContinuation :=
        continuesDifference_uniqueForCursorAgreement
          firstContinuation secondContinuation
      have recordExact : firstRecord = secondRecord :=
        firstRecordExact.trans secondRecordExact.symm
      cases continuationExact
      cases recordExact
      rfl

theorem canonicalGeneratedLaws_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (first second : CanonicalGeneratedLaws source) : first = second := by
  cases first with
  | mk firstCompatibility firstCompatibilityExact firstProvenance
      firstObstruction firstDifference firstFresh =>
    cases second with
    | mk secondCompatibility secondCompatibilityExact secondProvenance
      secondObstruction secondDifference secondFresh =>
      have compatibilityExact : firstCompatibility = secondCompatibility :=
        firstCompatibilityExact.trans secondCompatibilityExact.symm
      have provenanceExact : firstProvenance = secondProvenance :=
        preservesProvenance_uniqueForCursorAgreement
          firstProvenance secondProvenance
      have obstructionExact : firstObstruction = secondObstruction :=
        integratesClosureObstruction_uniqueForCursorAgreement
          firstObstruction secondObstruction
      have differenceExact : firstDifference = secondDifference :=
        continuesDifference_uniqueForCursorAgreement
          firstDifference secondDifference
      have freshExact : firstFresh = secondFresh :=
        freshBoundaryDifference_uniqueForCursorAgreement firstFresh secondFresh
      cases compatibilityExact
      cases provenanceExact
      cases obstructionExact
      cases differenceExact
      cases freshExact
      rfl

theorem generatedStep_uniqueForCursorAgreement
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (first second : GeneratedStep source target) : first = second := by
  cases first with
  | mk firstTarget firstLaws =>
    cases second with
    | mk secondTarget secondLaws =>
      exact congrArg (GeneratedStep.mk firstTarget)
        (canonicalGeneratedLaws_uniqueForCursorAgreement
          firstLaws secondLaws)

theorem locatedStep_eq_of_source_eq
    {P : CircularPresentation}
    (first second : History.LocatedStep (@GeneratedStep P))
    (sourceExact : first.source = second.source) : first = second := by
  cases first with
  | mk firstSource firstTarget firstStep =>
    cases second with
    | mk secondSource secondTarget secondStep =>
      cases sourceExact
      have targetExact : firstTarget = secondTarget :=
        firstStep.formedByFreeLayer.trans secondStep.formedByFreeLayer.symm
      cases targetExact
      exact congrArg (History.LocatedStep.mk firstSource firstTarget)
        (generatedStep_uniqueForCursorAgreement firstStep secondStep)

def iterateStructuralDepth
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    StructuralDepth → PositiveConstitution P
  | .root => source
  | .next depth => canonicalTarget (iterateStructuralDepth source depth)

def historyStructuralDepth
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → StructuralDepth
  | .root => .root
  | .extend history _ => .next (historyStructuralDepth history)

def rootProperDepth :
    (depth : StructuralDepth) →
      ProperStructuralDepth .root (.next depth)
  | .root => .direct .root
  | .next depth => .later (rootProperDepth depth)

def nextProperDepth :
    {first second : StructuralDepth} →
    ProperStructuralDepth first second →
      ProperStructuralDepth (.next first) (.next second)
  | _, _, .direct depth => .direct (.next depth)
  | _, _, .later earlier => .later (nextProperDepth earlier)

inductive StructuralDepthComparison
    (first second : StructuralDepth) : Type
  | equal : first = second → StructuralDepthComparison first second
  | forward : ProperStructuralDepth first second →
      StructuralDepthComparison first second
  | backward : ProperStructuralDepth second first →
      StructuralDepthComparison first second

def compareStructuralDepth :
    (first second : StructuralDepth) → StructuralDepthComparison first second
  | .root, .root => .equal rfl
  | .root, .next second => .forward (rootProperDepth second)
  | .next first, .root => .backward (rootProperDepth first)
  | .next first, .next second =>
      match compareStructuralDepth first second with
      | .equal equality => .equal (congrArg StructuralDepth.next equality)
      | .forward proper => .forward (nextProperDepth proper)
      | .backward proper => .backward (nextProperDepth proper)

def iterateStructuralDepth_future
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    {first second : StructuralDepth} →
    ProperStructuralDepth first second →
      CursorFuture P
        (iterateStructuralDepth source first).1
        (iterateStructuralDepth source second).1
  | _, _, .direct depth =>
      (generatedStepCursorAdvance
        (generatedStepOfFreeK (iterateStructuralDepth source depth))).toFuture
  | _, _, .later proper =>
      (iterateStructuralDepth_future source proper).trans
        (generatedStepCursorAdvance
          (generatedStepOfFreeK
            (iterateStructuralDepth source _))).toFuture

theorem iterateStructuralDepth_cursor_injective
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    Function.Injective
      (fun depth => (iterateStructuralDepth source depth).1) := by
  intro first second cursorExact
  cases compareStructuralDepth first second with
  | equal depthExact => exact depthExact
  | forward proper =>
      have future := iterateStructuralDepth_future source proper
      have loop : CursorFuture P
          (iterateStructuralDepth source first).1
          (iterateStructuralDepth source first).1 :=
        cast
          (congrArg
            (CursorFuture P (iterateStructuralDepth source first).1)
            cursorExact.symm)
          future
      exact False.elim (CursorFuture.irreflexive _ loop)
  | backward proper =>
      have future := iterateStructuralDepth_future source proper
      have loop : CursorFuture P
          (iterateStructuralDepth source second).1
          (iterateStructuralDepth source second).1 :=
        cast
          (congrArg
            (CursorFuture P (iterateStructuralDepth source second).1)
            cursorExact)
          future
      exact False.elim (CursorFuture.irreflexive _ loop)

theorem generatedHistory_endpoint_eq_iterateStructuralDepth
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    target =
      iterateStructuralDepth source (historyStructuralDepth history) := by
  induction history with
  | root => rfl
  | extend history step inductionHypothesis =>
      exact step.formedByFreeLayer.trans
        (congrArg canonicalTarget inductionHypothesis)

theorem rootedGeneratedHistory_endpoint_eq_of_cursor_eq
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P)
    (cursorExact : first.endpoint.1 = second.endpoint.1) :
    first.endpoint = second.endpoint := by
  have firstExact :=
    generatedHistory_endpoint_eq_iterateStructuralDepth first.history
  have secondExact :=
    generatedHistory_endpoint_eq_iterateStructuralDepth second.history
  have firstCursorExact := congrArg Sigma.fst firstExact
  have secondCursorExact := congrArg Sigma.fst secondExact
  have depthExact :
      historyStructuralDepth first.history =
        historyStructuralDepth second.history :=
    iterateStructuralDepth_cursor_injective (initialPositive P)
      (firstCursorExact.symm.trans (cursorExact.trans secondCursorExact))
  exact firstExact.trans
    ((congrArg (iterateStructuralDepth (initialPositive P)) depthExact).trans
      secondExact.symm)

def occurrenceSourceHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    (history : History Step source target) →
    (occurrence : History.Occurrence history) →
      History Step source occurrence.locatedStep.source
  | .extend previous _step, .last => previous
  | .extend previous _step, .earlier occurrence =>
      occurrenceSourceHistory previous occurrence

theorem rootedOccurrence_source_eq_of_cursor_eq
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    (occurrence : History.Occurrence history.history)
    (position : NonClosingPosition P.perimeter)
    (cursorExact : occurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1) :
    occurrence.locatedStep.source = perimeterPositionSource P position := by
  let canonicalOccurrence := requirementToOccurrence P position
  let actualPrefix : RootedGeneratedHistory P :=
    { endpoint := occurrence.locatedStep.source
      history := occurrenceSourceHistory history.history occurrence }
  let canonicalPrefix : RootedGeneratedHistory P :=
    { endpoint := canonicalOccurrence.locatedStep.source
      history := occurrenceSourceHistory
        (perimeterDeployment P).history canonicalOccurrence }
  have canonicalLocatedExact : canonicalOccurrence.locatedStep =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position :=
    deployPosition_locatedStep P FreeConstitution.root
      BoundaryDifference.initial position
  have canonicalSourceExact : canonicalOccurrence.locatedStep.source =
      perimeterPositionSource P position :=
    congrArg History.LocatedStep.source canonicalLocatedExact
  have canonicalCursorExact : canonicalOccurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1 :=
    congrArg Sigma.fst canonicalSourceExact
  have prefixCursorExact : actualPrefix.endpoint.1 =
      canonicalPrefix.endpoint.1 :=
    cursorExact.trans canonicalCursorExact.symm
  exact
    (rootedGeneratedHistory_endpoint_eq_of_cursor_eq
      actualPrefix canonicalPrefix prefixCursorExact).trans
      canonicalSourceExact

/- The primitive agreement records only the exact structural address of the
   occurrence.  In a rooted generated history this cursor determines the full
   source state and therefore the canonical target and generated step. -/
structure RequirementOccurrenceAgreement
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P)
    (position : NonClosingPosition P.perimeter)
    (occurrence : History.Occurrence history.history) : Type _ where
  sourceCursorExact :
    occurrence.locatedStep.source.1 =
      (perimeterPositionSource P position).1

namespace RequirementOccurrenceAgreement

def transportOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {first second : History.Occurrence history.history}
    (equality : first = second) :
    RequirementOccurrenceAgreement P history position first →
      RequirementOccurrenceAgreement P history position second := by
  cases equality
  exact id

def locatedStep_stepHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) : HEq first.step second.step := by
  cases equality
  exact HEq.rfl

def locatedStep_compatibilityHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) :
    HEq first.step.compatibility second.step.compatibility := by
  cases equality
  exact HEq.rfl

def locatedStep_provenanceHEq
    {P : CircularPresentation}
    {first second : History.LocatedStep (@GeneratedStep P)}
    (equality : first = second) :
    HEq first.step.preservesProvenance.exactProvenance
      second.step.preservesProvenance.exactProvenance := by
  cases equality
  exact HEq.rfl

def compatibleTransportOfReadoutEqualities
    {P : CircularPresentation}
    {implicitSource implicitTarget : ReturnedImplicit P}
    {explicitSource explicitTarget : ReturnedExplicit P}
    (implicitEquality : implicitSource = implicitTarget)
    (explicitEquality : explicitSource = explicitTarget) :
    ExactCompatibleTransport
      (ReturnedCompatible P implicitSource explicitSource)
      (ReturnedCompatible P implicitTarget explicitTarget) := by
  cases implicitEquality
  cases explicitEquality
  exact RelationalFoundations.ExactTransport.reflexive _

def sourceStateExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.source = perimeterPositionSource P position :=
  rootedOccurrence_source_eq_of_cursor_eq history occurrence position
    agreement.sourceCursorExact

def locatedStepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep =
      positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position :=
  locatedStep_eq_of_source_eq occurrence.locatedStep
    (positionLocatedStep P FreeConstitution.root
      BoundaryDifference.initial position)
    agreement.sourceStateExact

def targetStateExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.target = perimeterPositionTarget P position :=
  congrArg History.LocatedStep.target agreement.locatedStepExact

def targetCursorExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    occurrence.locatedStep.target.1 =
      (perimeterPositionTarget P position).1 :=
  congrArg Sigma.fst agreement.targetStateExact

def explicitReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    explicitRead occurrence.locatedStep.target =
      explicitRead (perimeterPositionTarget P position) :=
  congrArg explicitRead agreement.targetStateExact

def implicitReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    implicitRead occurrence.locatedStep.source =
      implicitRead (perimeterPositionSource P position) :=
  congrArg implicitRead agreement.sourceStateExact

def differenceReadoutExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    boundaryDifferenceReadout occurrence.locatedStep.source.2.2 =
      boundaryDifferenceReadout
        (perimeterPositionSource P position).2.2 :=
  congrArg
    (fun state : PositiveConstitution P =>
      boundaryDifferenceReadout state.2.2)
    agreement.sourceStateExact

def stepExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq occurrence.locatedStep.step
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step :=
  locatedStep_stepHEq agreement.locatedStepExact

def compatibilityTransport
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    ExactCompatibleTransport
      (ReturnedCompatible P
        (implicitRead occurrence.locatedStep.source)
        (explicitRead occurrence.locatedStep.target))
      (ReturnedCompatible P
        (implicitRead (perimeterPositionSource P position))
        (explicitRead (perimeterPositionTarget P position))) :=
  compatibleTransportOfReadoutEqualities
    agreement.implicitReadoutExact agreement.explicitReadoutExact

def compatibilityWitnessExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq occurrence.locatedStep.step.compatibility
      (stepCompatibleAt (perimeterPositionSource P position).1) :=
  (locatedStep_compatibilityHEq agreement.locatedStepExact).trans
    (GeneratedStep.compatibilityWitnessExact
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step)

def provenanceTransport
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    ExactProvenanceTransport
      (ReturnedProvenance P
        (boundaryDifferenceReadout occurrence.locatedStep.source.2.2))
      (ReturnedProvenance P
        (boundaryDifferenceReadout
          (perimeterPositionSource P position).2.2)) :=
  RelationalFoundations.ExactTransport.ofEquality
    (congrArg (ReturnedProvenance P) agreement.differenceReadoutExact)

def provenanceWitnessExact
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    {position : NonClosingPosition P.perimeter}
    {occurrence : History.Occurrence history.history}
    (agreement : RequirementOccurrenceAgreement P history position occurrence) :
    HEq
      occurrence.locatedStep.step.preservesProvenance.exactProvenance
      (boundaryProvenanceReadout
        (perimeterPositionSource P position).2.2) :=
  (locatedStep_provenanceHEq agreement.locatedStepExact).trans
    (heq_of_eq (GeneratedStep.provenanceWitnessExact
      (positionLocatedStep P FreeConstitution.root
        BoundaryDifference.initial position).step))

end RequirementOccurrenceAgreement

def canonicalRequirementAgreement
    (P : CircularPresentation)
    (position : NonClosingPosition P.perimeter) :
    RequirementOccurrenceAgreement P (perimeterDeployment P) position
      (requirementToOccurrence P position) :=
  ⟨congrArg
    (fun located : History.LocatedStep (@GeneratedStep P) => located.source.1)
    (deployPosition_locatedStep P
      FreeConstitution.root BoundaryDifference.initial position)⟩

/- `Exact` refers to the exact realization of each non-closing requirement.
   Exact source-cursor agreement reconstructs the canonical located step and
   already forces the realization map to be
   injective; it does not assert that these occurrences exhaust the history. -/
structure ExactNonClosingRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  realize :
    NonClosingPosition P.perimeter → History.Occurrence history.history
  agreement :
    (position : NonClosingPosition P.perimeter) →
      RequirementOccurrenceAgreement P history position (realize position)

namespace ExactNonClosingRealization

/- Distinct perimeter requirements cannot be absorbed by one occurrence when
   exact source-cursor agreement is available.  Equality of their realized
   occurrences would identify their canonical located steps; the strict cursor
   order between distinct canonical occurrences then yields an impossible
   cursor loop.  Injectivity is therefore a theorem, not an independent field
   of `ExactNonClosingRealization`. -/
theorem realize_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    Function.Injective realization.realize := by
  intro first second equality
  have canonicalFirst :=
    (canonicalRequirementAgreement P first).locatedStepExact
  have canonicalSecond :=
    (canonicalRequirementAgreement P second).locatedStepExact
  have realizedFirst := (realization.agreement first).locatedStepExact
  have realizedSecond := (realization.agreement second).locatedStepExact
  have realizedAgree :
      (realization.realize first).locatedStep =
        (realization.realize second).locatedStep :=
    congrArg (fun occurrence => occurrence.locatedStep) equality
  have stepsAgree :
      (requirementToOccurrence P first).locatedStep =
        (requirementToOccurrence P second).locatedStep :=
    canonicalFirst.trans
      ((realizedFirst.symm.trans (realizedAgree.trans realizedSecond)).trans
        canonicalSecond.symm)
  rcases History.OccurrencePrecedes.trichotomy
      (requirementToOccurrence P first)
      (requirementToOccurrence P second) with
    occurrenceEquality | forward | backward
  · exact requirementToOccurrence_injective P occurrenceEquality
  · rcases (StrongPerimetralTurning.History.OccurrencePrecedes.sourceCursorFuture forward) with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))
  · rcases (StrongPerimetralTurning.History.OccurrencePrecedes.sourceCursorFuture backward) with ⟨future⟩
    exact False.elim
      (CursorFuture.irreflexive _
        (congrArg
          (fun step : History.LocatedStep (@GeneratedStep P) => step.source.1)
          stepsAgree ▸ future))

/- A locally exact realization inside a genuine generated history must preserve
   the structural precedence of the perimeter.  The proof excludes reversed
   chronology by composing the two strict cursor futures into an impossible
   cursor loop. -/
theorem preservesPrecedence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (precedes : NonClosingPrecedes P.perimeter first second) :
    History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) := by
  rcases History.OccurrencePrecedes.trichotomy
      (realization.realize first) (realization.realize second) with
    equality | forward | backward
  · have positionEquality : first = second :=
      realization.realize_injective equality
    exact False.elim (precedes.ne positionEquality)
  · exact forward
  · rcases (StrongPerimetralTurning.NonClosingPrecedes.sourceCursorFuture precedes) with ⟨canonicalForward⟩
    rcases (StrongPerimetralTurning.History.OccurrencePrecedes.sourceCursorFuture backward) with ⟨realizedBackward⟩
    have firstCursorExact := (realization.agreement first).sourceCursorExact
    have secondCursorExact := (realization.agreement second).sourceCursorExact
    have forwardRealized : CursorFuture P
        (realization.realize first).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      firstCursorExact.symm ▸ secondCursorExact.symm ▸ canonicalForward
    exact False.elim
      (CursorFuture.irreflexive _
        (forwardRealized.trans realizedBackward))

/- Canonically adjacent requirements are realized by immediately adjacent
   occurrences in a genuine generated history.  Any positive gap would become
   a strict cursor future from a cursor to itself after transporting the exact
   endpoint data. -/
theorem preservesNext
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    {first second : NonClosingPosition P.perimeter}
    (next : NonClosingNext P.perimeter first second) :
    History.OccurrenceNext
      (realization.realize first) (realization.realize second) := by
  have occurrencePrecedes : History.OccurrencePrecedes
      (realization.realize first) (realization.realize second) :=
    realization.preservesPrecedence next.toPrecedes
  rcases (StrongPerimetralTurning.History.OccurrencePrecedes.next_or_positiveGap occurrencePrecedes) with immediate | gap
  · exact immediate
  · rcases gap with ⟨future⟩
    have canonicalEndpointEquality :=
      NonClosingNext.target_eq_source next
        FreeConstitution.root BoundaryDifference.initial
    have endpointEquality :
        (realization.realize first).locatedStep.target =
          (realization.realize second).locatedStep.source :=
      (realization.agreement first).targetStateExact.trans
        (canonicalEndpointEquality.trans
          (realization.agreement second).sourceStateExact.symm)
    have cursorEquality := congrArg Sigma.fst endpointEquality
    have futureLoop : CursorFuture P
        (realization.realize second).locatedStep.source.1
        (realization.realize second).locatedStep.source.1 :=
      cursorEquality ▸ future
    exact False.elim (CursorFuture.irreflexive _ futureLoop)

/- The canonical perimeter occurrences can be read inside any exact local
   realization without introducing a second realization structure. -/
def embedPerimeterOccurrence
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    History.Occurrence (perimeterHistory P) →
      History.Occurrence history.history :=
  fun occurrence =>
    realization.realize (occurrenceToRequirement P occurrence)

theorem embedPerimeterOccurrence_locatedStep
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history)
    (occurrence : History.Occurrence (perimeterHistory P)) :
    (realization.embedPerimeterOccurrence occurrence).locatedStep =
      occurrence.locatedStep := by
  calc
    (realization.embedPerimeterOccurrence occurrence).locatedStep
        = positionLocatedStep P FreeConstitution.root
            BoundaryDifference.initial (occurrenceToRequirement P occurrence) :=
      (realization.agreement (occurrenceToRequirement P occurrence)).locatedStepExact
    _ = (requirementToOccurrence P
          (occurrenceToRequirement P occurrence)).locatedStep :=
      (canonicalRequirementAgreement P
        (occurrenceToRequirement P occurrence)).locatedStepExact.symm
    _ = occurrence.locatedStep := by
      rw [occurrenceToRequirement_toOccurrence]

theorem embedPerimeterOccurrence_injective
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    Function.Injective realization.embedPerimeterOccurrence := by
  intro first second equality
  have positionEquality :
      occurrenceToRequirement P first = occurrenceToRequirement P second :=
    realization.realize_injective equality
  calc
    first = requirementToOccurrence P (occurrenceToRequirement P first) :=
      (occurrenceToRequirement_toOccurrence P first).symm
    _ = requirementToOccurrence P (occurrenceToRequirement P second) :=
      congrArg (requirementToOccurrence P) positionEquality
    _ = second := occurrenceToRequirement_toOccurrence P second

end ExactNonClosingRealization

def positiveStepThenHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (first : Step source middle)
    (rest : History Step middle target) :
    Σ positive : History.Positive Step source target,
      PLift (positive.toHistory =
        History.append (.extend .root first) rest) := by
  cases rest with
  | root => exact ⟨⟨source, .root, first⟩, ⟨rfl⟩⟩
  | extend priorHistory last =>
      exact ⟨⟨_, History.append (.extend .root first) priorHistory, last⟩,
        ⟨rfl⟩⟩

def deployRemaining_positive
    (P : CircularPresentation)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (_ : NonClosingPosition remaining) :
    Σ positive : History.Positive (@GeneratedStep P)
      (positiveAtRemaining P remaining data difference)
      (deployRemaining P remaining data difference).1,
      PLift (positive.toHistory =
        (deployRemaining P remaining data difference).2) := by
  cases remaining with
  | boundary node => contradiction
  | @advance node nextNode compatible tail =>
      exact positiveStepThenHistory
        (generatedStepOfFreeK
          (positiveAtRemaining P (.advance compatible tail) data difference))
        (deployRemaining P tail
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
          (canonicalTarget
            (positiveAtRemaining P (.advance compatible tail) data difference)).2.2).2

def perimeterDeployment_positive
    (P : CircularPresentation) :
    Σ positive : History.Positive (@GeneratedStep P)
      (initialPositive P) (perimeterEndpoint P),
      PLift (positive.toHistory = perimeterHistory P) :=
  deployRemaining_positive P FreeConstitution.root
    BoundaryDifference.initial P.perimeterPositive

namespace History.Vertex

def boundaryReadout
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    {Endpoint : Type uEnd}
    (left right : Endpoint) : Vertex history → Endpoint
  | .root => left
  | .earlier vertex => boundaryReadout left right vertex
  | .final => right

theorem initial_reads_left
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right (History.initialVertex history) = left := by
  induction history with
  | root => rfl
  | extend history step ih => exact ih

theorem positive_final_reads_right
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right
      (History.finalVertex positive.toHistory) = right := rfl

theorem positive_initial_ne_final
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target) :
    History.initialVertex positive.toHistory ≠
      History.finalVertex positive.toHistory := by
  intro equality
  cases equality

theorem positive_final_reads_right_after_history_equality
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (history : History Step source target)
    (historyEquality : positive.toHistory = history)
    {Endpoint : Type uEnd}
    (left right : Endpoint) :
    boundaryReadout left right (History.finalVertex history) = right := by
  cases historyEquality
  exact positive_final_reads_right positive left right

theorem positive_initial_ne_final_after_history_equality
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (positive : History.Positive Step source target)
    (history : History Step source target)
    (historyEquality : positive.toHistory = history) :
    History.initialVertex history ≠ History.finalVertex history := by
  cases historyEquality
  exact positive_initial_ne_final positive

end History.Vertex

structure ExactPerimeterRealization
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  requirementToOccurrence :
    NonClosingPosition P.perimeter → History.Occurrence history.history
  occurrenceToRequirement :
    History.Occurrence history.history → NonClosingPosition P.perimeter
  occurrenceRoundTrip :
    (occurrence : History.Occurrence history.history) →
      requirementToOccurrence (occurrenceToRequirement occurrence) = occurrence
  requirementRoundTrip :
    (position : NonClosingPosition P.perimeter) →
      occurrenceToRequirement (requirementToOccurrence position) = position
  localAgreement :
    (position : NonClosingPosition P.perimeter) →
      RequirementOccurrenceAgreement P history position
        (requirementToOccurrence position)
  leftBoundary : History.Vertex history.history
  rightBoundary : History.Vertex history.history
  boundaryReadout : History.Vertex history.history → P.Endpoint
  readsLeftBoundary : boundaryReadout leftBoundary = P.leftEndpoint
  readsRightBoundary : boundaryReadout rightBoundary = P.rightEndpoint
  boundariesSeparated : leftBoundary ≠ rightBoundary
  identificationCloses : leftBoundary = rightBoundary → P.TotalLoop

def perimeterRealization (P : CircularPresentation) :
    ExactPerimeterRealization P (perimeterDeployment P) := by
  let positive := (perimeterDeployment_positive P).1
  have historyEquality := (perimeterDeployment_positive P).2.down
  exact
    { requirementToOccurrence := requirementToOccurrence P
      occurrenceToRequirement := occurrenceToRequirement P
      occurrenceRoundTrip := occurrenceToRequirement_toOccurrence P
      requirementRoundTrip := requirementToOccurrence_toRequirement P
      localAgreement := canonicalRequirementAgreement P
      leftBoundary := History.initialVertex (perimeterHistory P)
      rightBoundary := History.finalVertex (perimeterHistory P)
      boundaryReadout :=
        History.Vertex.boundaryReadout P.leftEndpoint P.rightEndpoint
      readsLeftBoundary :=
        History.Vertex.initial_reads_left (perimeterHistory P)
          P.leftEndpoint P.rightEndpoint
      readsRightBoundary :=
        History.Vertex.positive_final_reads_right_after_history_equality
          positive (perimeterHistory P) historyEquality
          P.leftEndpoint P.rightEndpoint
      boundariesSeparated :=
        History.Vertex.positive_initial_ne_final_after_history_equality
          positive (perimeterHistory P) historyEquality
      identificationCloses := fun equality =>
        P.closeFromIdentification
          ((History.Vertex.initial_reads_left (perimeterHistory P)
              P.leftEndpoint P.rightEndpoint).symm.trans
            ((congrArg
              (History.Vertex.boundaryReadout
                P.leftEndpoint P.rightEndpoint) equality).trans
              (History.Vertex.positive_final_reads_right_after_history_equality
                positive (perimeterHistory P) historyEquality
                P.leftEndpoint P.rightEndpoint))) }

/- The exact non-closing part of the perimeter is an instance of the generic
   internal-role realization.  No circular junction or totalization enters
   this adapter. -/
def perimeterInternalRoleRealization
    (P : CircularPresentation) :
    SegmentedResidualRole.ExactInternalRealization
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P)) :=
  { roleToOccurrence := requirementToOccurrence P
    occurrenceToRole := occurrenceToRequirement P
    occurrenceRoundTrip := occurrenceToRequirement_toOccurrence P
    roleRoundTrip := requirementToOccurrence_toRequirement P }


end StrongPerimetralTurning
