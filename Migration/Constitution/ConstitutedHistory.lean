import RelationalFoundations.Regime
import Constitution.FreeConstitution
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Proof-relevant histories -/

/- Generic histories are exported from the independent foundation. -/
abbrev GeneratedHistory
    {P : CircularPresentation}
    (source target : PositiveConstitution P) :=
  History (@GeneratedStep P) source target

theorem generatedHistory_preservesClosureObstruction
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target) :
    target.2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction := by
  induction history with
  | root => rfl
  | extend prior step inductionHypothesis =>
      exact step.inheritedClosureObstructionExact.trans inductionHypothesis

abbrev RootedGeneratedHistory (P : CircularPresentation) := RelationalFoundations.RootedConstruction (@GeneratedStep P) (initialPositive P)
namespace RootedGeneratedHistory
export RelationalFoundations.RootedConstruction (mk)
def endpoint {P : CircularPresentation} (rooted : RootedGeneratedHistory P) : PositiveConstitution P :=
  RelationalFoundations.RootedConstruction.endpoint rooted
def history {P : CircularPresentation} (rooted : RootedGeneratedHistory P) :
    GeneratedHistory (initialPositive P) rooted.endpoint :=
  RelationalFoundations.RootedConstruction.history rooted
end RootedGeneratedHistory

/-! ## Occurrence-indexed normative adequacy -/


/- Normative adequacy is indexed by complete step occurrences.  No projection to
   source, target, cursor, or any returned reading is built into this layer. -/
structure NormativeAdequacy
    (P : CircularPresentation) where
  AlignmentSpec :
    Type uSpec
  RegimeAdequateAtOccurrence :
    AlignmentSpec →
    (R : RootedGeneratedHistory P → Type uRegime) →
    (H : RootedGeneratedHistory P) →
    History.Occurrence H.history →
    Type uAdequacy

/- `AdequateAlong` covers exactly the step occurrences carried by the history.
   The root history has no occurrences, so this type is vacuously inhabited
   there. Any normative obligation on the initial constitution is a separate
   notion and is deliberately not encoded here. -/
abbrev AdequateAlong
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (H : RootedGeneratedHistory P) : Type _ :=
  (occurrence : History.Occurrence H.history) →
    N.RegimeAdequateAtOccurrence S R H occurrence

/- A regime exit becomes specification-relative only by composing the existing
   typed diagnostic with adequacy witnesses for every step occurrence of the
   same candidate.  The `RegimeExit` kernel is intentionally unchanged. -/
structure SpecRelativeHistoryExit
    {P : CircularPresentation}
    (N : NormativeAdequacy P)
    (S : N.AlignmentSpec)
    (R : RootedGeneratedHistory P → Type uRegime)
    (Faithful : RootedGeneratedHistory P → Type uFaithful) where
  exit :
    AbstractSegmentedTurning.RegimeExit Faithful R
  adequacy :
    AdequateAlong N S R exit.candidate

def RootedGeneratedHistory.terminalClosureObstruction
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) : PositiveClosureObstruction P :=
  history.endpoint.2.1.1.inheritedClosureObstruction

theorem RootedGeneratedHistory.terminalClosureObstruction_is_initial
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    history.terminalClosureObstruction = P.positiveClosureObstruction :=
  (generatedHistory_preservesClosureObstruction history.history).trans
    FreeConstitution.root_inheritedClosureObstruction_exact

theorem rootedGeneratedHistory_ext
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) : first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          have exactHistory : firstHistory = secondHistory := eq_of_heq historyEquality
          cases exactHistory
          rfl

def rootedHistoryRoot (P : CircularPresentation) : RootedGeneratedHistory P :=
  ⟨initialPositive P, .root⟩

def appendRooted
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (continuation : GeneratedHistory rooted.endpoint target) :
    RootedGeneratedHistory P :=
  ⟨target, History.append rooted.history continuation⟩

def appendGenerated
    {P : CircularPresentation}
    (rooted : RootedGeneratedHistory P)
    (generated :
      Σ target : PositiveConstitution P,
        GeneratedStep rooted.endpoint target) :
    RootedGeneratedHistory P :=
  appendRooted rooted (.extend .root generated.2)

def preserveHistoricalProvenanceIntoCanonicalTarget
    {P : CircularPresentation}
    {origin source : PositiveConstitution P} :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin (canonicalTarget source).2.1 := by
  intro record
  change HistoricalProvenanceRecord P origin
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveHistoricalProvenanceAlongStep
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  exact preserveHistoricalProvenanceIntoCanonicalTarget record

def preserveHistoricalProvenanceAlongHistory
    {P : CircularPresentation}
    {origin source target : PositiveConstitution P} :
    GeneratedHistory source target →
    HistoricalProvenanceRecord P origin source.2.1 →
      HistoricalProvenanceRecord P origin target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveHistoricalProvenanceAlongStep step
        (preserveHistoricalProvenanceAlongHistory history record)

def preserveFormationRecordAlongStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    FormationRecord P source.2.1 → FormationRecord P target.2.1 := by
  intro record
  cases step.formedByFreeLayer
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved record

def preserveFormationRecordAlongHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target →
      FormationRecord P source.2.1 → FormationRecord P target.2.1
  | .root, record => record
  | .extend history step, record =>
      preserveFormationRecordAlongStep step
        (preserveFormationRecordAlongHistory history record)

theorem current_ne_preserved
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    {layer : FreeK P previous difference}
    (record : FormationRecord P previous) :
    (FormationRecord.current : FormationRecord P
      (FreeConstitution.formed previous difference layer)) ≠
      FormationRecord.preserved record := by
  intro equality
  cases equality

inductive FreshFormationRecord
    (P : CircularPresentation)
    (source : PositiveConstitution P) :
    PositiveConstitution P → Type _
  | after
      {predecessor : PositiveConstitution P}
      {target : PositiveConstitution P}
      (priorHistory : GeneratedHistory source predecessor)
      (lastStep : GeneratedStep predecessor target) :
      FreshFormationRecord P source target

namespace FreshFormationRecord

def predecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → PositiveConstitution P
  | .after (predecessor := predecessor) _ _ => predecessor

def priorHistory
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedHistory source fresh.predecessor := by
  cases fresh with
  | after priorHistory _ => exact priorHistory

def freshRecord
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    FreshFormationRecord P source target → FormationRecord P target.2.1
  | .after _ lastStep => by
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.freshRecord

def lastStep
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target) :
    GeneratedStep fresh.predecessor target := by
  cases fresh with
  | after _ lastStep => exact lastStep

theorem notFromPredecessor
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P fresh.predecessor.2.1) :
  fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep oldRecord := by
  cases fresh with
  | after priorHistory lastStep =>
      cases lastStep.formedByFreeLayer
      exact lastStep.freshBoundaryDifference.notPreservedOld oldRecord

theorem notFromSource
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (fresh : FreshFormationRecord P source target)
    (oldRecord : FormationRecord P source.2.1) :
    fresh.freshRecord ≠
      preserveFormationRecordAlongStep fresh.lastStep
        (preserveFormationRecordAlongHistory fresh.priorHistory oldRecord) :=
  fresh.notFromPredecessor _

end FreshFormationRecord

def positiveGeneratedHistory_hasFreshFormation
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    FreshFormationRecord P source target := by
  exact .after positive.priorHistory positive.lastStep

theorem rootedHistoryEq
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (endpointEquality : first.endpoint = second.endpoint)
    (historyEquality : HEq first.history second.history) :
    first = second := by
  cases first with
  | mk firstEndpoint firstHistory =>
      cases second with
      | mk secondEndpoint secondHistory =>
          cases endpointEquality
          cases historyEquality
          rfl

structure ConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : GeneratedHistory first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation = second.history

structure StrictConstitutivePrefix
    {P : CircularPresentation}
    (first second : RootedGeneratedHistory P) : Type _ where
  continuation : History.Positive
    (@GeneratedStep P) first.endpoint second.endpoint
  historyExact :
    History.append first.history continuation.toHistory = second.history

def prefixReflexive
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P) :
    ConstitutivePrefix history history := ⟨.root, rfl⟩

def prefixTransitive
    {P : CircularPresentation}
    {first second third : RootedGeneratedHistory P} :
    ConstitutivePrefix first second →
    ConstitutivePrefix second third →
    ConstitutivePrefix first third := by
  rintro ⟨left, leftEquality⟩ ⟨right, rightEquality⟩
  refine ⟨History.append left right, ?_⟩
  rw [← History.append_associative, leftEquality, rightEquality]

def generatedStepCursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    CursorAdvance P source.1 target.1 := by
  cases step.formedByFreeLayer
  exact cursorAdvanceGraph source.1

inductive CursorReach (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | root : CursorReach P cursor cursor
  | extend :
      CursorReach P source middle →
      CursorAdvance P middle target →
      CursorReach P source target

def CursorReach.followedByStep
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorAdvance P middle target →
      PositiveCursorAdvance P source target
  | .root, step => .one step
  | .extend previous last, step =>
      .followedBy (previous.followedByStep last) step

def CursorReach.trans
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P} :
    CursorReach P source middle → CursorReach P middle target →
      CursorReach P source target
  | left, .root => left
  | left, .extend previous last =>
      .extend (CursorReach.trans left previous) last

def CursorFuture.transReach
    {P : CircularPresentation}
    {source middle target : PerimeterCursor P}
    (future : CursorFuture P source middle) :
    CursorReach P middle target → CursorFuture P source target
  | .root => future
  | .extend previous last =>
      (future.transReach previous).trans last.toFuture

def generatedHistoryCursorReach
    {P : CircularPresentation}
    {source target : PositiveConstitution P} :
    GeneratedHistory source target → CursorReach P source.1 target.1
  | .root => .root
  | .extend history step =>
      .extend (generatedHistoryCursorReach history)
        (generatedStepCursorAdvance step)

def occurrenceSource_to_historyEndpoint_future
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorFuture P occurrence.locatedStep.source.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last =>
      (generatedStepCursorAdvance step).toFuture
  | .extend history step, .earlier earlier =>
      (occurrenceSource_to_historyEndpoint_future history earlier).trans
        (generatedStepCursorAdvance step).toFuture

def occurrenceTarget_to_historyEndpoint_reach
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (occurrence : History.Occurrence history) →
      CursorReach P occurrence.locatedStep.target.1 target.1
  | .root, occurrence => nomatch occurrence
  | .extend _history step, .last => .root
  | .extend history step, .earlier earlier =>
      .extend (occurrenceTarget_to_historyEndpoint_reach history earlier)
        (generatedStepCursorAdvance step)

namespace History.OccurrencePrecedes

def earlierLast_next_or_positiveGap
    {P : CircularPresentation}
    {source target nextTarget : PositiveConstitution P}
    : (history : GeneratedHistory source target) →
    (step : GeneratedStep target nextTarget) →
    (occurrence : History.Occurrence history) →
    History.OccurrenceNext
        (.earlier occurrence)
        (.last : History.Occurrence (.extend history step)) ∨
      Nonempty (CursorFuture P
        occurrence.locatedStep.target.1
        (History.Occurrence.last : History.Occurrence
          (.extend history step)).locatedStep.source.1)
  | .root, _step, occurrence => nomatch occurrence
  | .extend _history _previousStep, step, .last => Or.inl .previous_last
  | .extend history previousStep, _step, .earlier earlier =>
      Or.inr ⟨
        ((occurrenceTarget_to_historyEndpoint_reach history earlier).followedByStep
          (generatedStepCursorAdvance previousStep)).toFuture⟩

theorem sourceCursorFuture
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    Nonempty (CursorFuture P
      first.locatedStep.source.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact ⟨occurrenceSource_to_historyEndpoint_future _ occurrence⟩
  | earlier_earlier _ inductionHypothesis =>
      exact inductionHypothesis

theorem next_or_positiveGap
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    {history : GeneratedHistory source target}
    {first second : History.Occurrence history}
    (precedes : History.OccurrencePrecedes first second) :
    History.OccurrenceNext first second ∨
      Nonempty (CursorFuture P
        first.locatedStep.target.1 second.locatedStep.source.1) := by
  induction precedes with
  | earlier_last occurrence =>
      exact earlierLast_next_or_positiveGap _ _ occurrence
  | earlier_earlier _ inductionHypothesis =>
      rcases inductionHypothesis with next | gap
      · exact Or.inl (.earlier_earlier next)
      · exact Or.inr gap

end History.OccurrencePrecedes

def positiveGeneratedHistory_cursorAdvance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    PositiveCursorAdvance P source.1 target.1 :=
  (generatedHistoryCursorReach positive.priorHistory).followedByStep
    (generatedStepCursorAdvance positive.lastStep)

theorem positiveGeneratedHistory_source_ne_target
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (positive : History.Positive (@GeneratedStep P) source target) :
    source ≠ target := by
  intro equality
  have cursorEquality : source.1 = target.1 := congrArg Sigma.fst equality
  exact positiveCursorAdvance_irreflexive
    (cast
      (congrArg (PositiveCursorAdvance P source.1) cursorEquality.symm)
      (positiveGeneratedHistory_cursorAdvance positive))


/- A generated history whose endpoints are equal cannot contain any step
   occurrence.  The root case has no occurrences by construction.  Any
   extended history determines a positive history, whose endpoints are forced
   to be distinct by generated cursor advance. -/
theorem generatedHistory_equalEndpoints_noOccurrence
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (history : GeneratedHistory source target)
    (endpointEquality : source = target) :
    History.Occurrence history → False := by
  cases history with
  | root =>
      intro occurrence
      exact nomatch occurrence
  | extend priorHistory step =>
      intro _occurrence
      let positive : History.Positive (@GeneratedStep P) source target :=
        { predecessor := _
          priorHistory := priorHistory
          lastStep := step }
      exact positiveGeneratedHistory_source_ne_target positive endpointEquality


theorem append_positive_ne
    {P : CircularPresentation}
    (history : RootedGeneratedHistory P)
    {target : PositiveConstitution P}
    (positive : History.Positive
      (@GeneratedStep P) history.endpoint target) :
    appendRooted history positive.toHistory ≠ history := by
  intro equality
  have endpointEquality : target = history.endpoint :=
    congrArg RootedGeneratedHistory.endpoint equality
  exact positiveGeneratedHistory_source_ne_target positive endpointEquality.symm

theorem strictPrefix_ne
    {P : CircularPresentation}
    {first second : RootedGeneratedHistory P}
    (strict : StrictConstitutivePrefix first second) : second ≠ first := by
  intro equality
  have appendedEqualsSecond :
      appendRooted first strict.1.toHistory = second :=
    rootedHistoryEq rfl (heq_of_eq strict.2)
  exact append_positive_ne first strict.1
    (appendedEqualsSecond.trans equality)


end StrongPerimetralTurning
