import RelationalFoundations.ExactTransport
set_option genInjectivity false
set_option linter.defProp false
namespace RelationalFoundations
universe uA uB uV
inductive History
    {State : Type uA}
    (Step : State → State → Type uB) : State → State → Type _
  | root : History Step a a
  | extend : History Step a b → Step b c → History Step a c

namespace History

def append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State} :
    History Step a b → History Step b c → History Step a c
  | firstHistory, .root => firstHistory
  | firstHistory, .extend continuation step =>
      .extend (append firstHistory continuation) step

def appendRootExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history :=
  rfl

def appendExtendExact
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (firstHistory : History Step a b)
    (continuation : History Step b c)
    (step : Step c d) :
    append firstHistory (.extend continuation step) =
      .extend (append firstHistory continuation) step :=
  rfl

@[simp] theorem append_root
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append history (.root : History Step b b) = history := rfl

theorem root_append
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) :
    append (.root : History Step a a) history = history := by
  induction history with
  | root => rfl
  | extend history step ih =>
      change History.extend (append .root history) step = .extend history step
      rw [ih]

theorem append_associative
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c d : State}
    (first : History Step a b)
    (second : History Step b c)
    (third : History Step c d) :
    append (append first second) third =
      append first (append second third) := by
  induction third with
  | root => rfl
  | extend third step ih =>
      change History.extend (append (append first second) third) step =
        History.extend (append first (append second third)) step
      rw [ih]

inductive Occurrence
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} : Occurrence (.extend history step)
  | earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c} :
      Occurrence history → Occurrence (.extend history step)

theorem Occurrence.earlier.inj
    {State : Type uA} {Step : State → State → Type uB}
    {a b c : State} {history : History Step a b} {step : Step b c}
    {first second : Occurrence history}
    (eq : Occurrence.earlier (step := step) first = Occurrence.earlier second) : first = second := by
  cases eq
  rfl

/- An occurrence readout is deliberately only a post-constitutive assignment
   of values to occurrences already carried by one history.  The codomain is
   arbitrary, but no inhabitant, injectivity, faithfulness, or compatibility
   law is supplied by this abbreviation.  Such properties must be stated
   separately; the readout neither creates nor identifies occurrences.

   Conceptually, occurrences and their exact correspondences form a structural
   bus onto which independent readouts can be connected after constitution. -/
abbrev OccurrenceReadout
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target)
    (Value : Type uV) : Type _ :=
  Occurrence history → Value

/- Structural chronology of step occurrences in one history.  This relation
   carries only precedence information and introduces no numerical rank. -/
inductive OccurrencePrecedes
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | earlier_last
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      (occurrence : Occurrence history) :
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier occurrence)
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrencePrecedes first second →
      OccurrencePrecedes
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

/- Immediate chronology of step occurrences.  It records that the second
   occurrence is the very next generated step after the first. -/
inductive OccurrenceNext
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} →
    {history : History Step a b} →
    Occurrence history →
    Occurrence history →
    Prop
  | previous_last
      {a b c d : State}
      {history : History Step a b}
      {previousStep : Step b c}
      {lastStep : Step c d} :
      OccurrenceNext
        (history := .extend (.extend history previousStep) lastStep)
        (.earlier (.last : Occurrence (.extend history previousStep)))
        .last
  | earlier_earlier
      {a b c : State}
      {history : History Step a b}
      {step : Step b c}
      {first second : Occurrence history} :
      OccurrenceNext first second →
      OccurrenceNext
        (history := .extend history step)
        (.earlier first)
        (.earlier second)

namespace OccurrenceNext

theorem toPrecedes
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (next : OccurrenceNext first second) :
    OccurrencePrecedes first second := by
  induction next with
  | previous_last => exact .earlier_last .last
  | earlier_earlier _ inductionHypothesis =>
      exact .earlier_earlier inductionHypothesis

end OccurrenceNext

namespace OccurrencePrecedes

theorem ne
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    {first second : Occurrence history}
    (precedes : OccurrencePrecedes first second) : first ≠ second := by
  induction precedes with
  | earlier_last _ =>
      intro equality
      cases equality
  | earlier_earlier _ inductionHypothesis =>
      intro equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

theorem trichotomy
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b}
    (first second : Occurrence history) :
    first = second ∨
      OccurrencePrecedes first second ∨
        OccurrencePrecedes second first := by
  induction first with
  | last =>
      cases second with
      | last => exact Or.inl rfl
      | earlier second =>
          exact Or.inr (Or.inr (.earlier_last second))
  | earlier first inductionHypothesis =>
      cases second with
      | last =>
          exact Or.inr (Or.inl (.earlier_last first))
      | earlier second =>
          rcases inductionHypothesis second with
            equality | precedes | follows
          · exact Or.inl (congrArg Occurrence.earlier equality)
          · exact Or.inr (Or.inl (.earlier_earlier precedes))
          · exact Or.inr (Or.inr (.earlier_earlier follows))

end OccurrencePrecedes

/- An exactly-one history is characterized structurally, before any numerical
   length is available: it is one extension of the root history. -/
inductive ExactlyOne
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State} :
    History Step source target → Type _
  | single (step : Step source target) :
      ExactlyOne (.extend .root step)

structure LocatedStep
    {State : Type uA}
    (Step : State → State → Type uB) where
  source : State
  target : State
  step : Step source target

def Occurrence.locatedStep
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    {history : History Step a b} :
    Occurrence history → LocatedStep Step
  | .last (step := step) => ⟨_, _, step⟩
  | .earlier occurrence => occurrence.locatedStep

def Occurrence.gapAt
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (occurrence : Occurrence history) :
    Step occurrence.locatedStep.source occurrence.locatedStep.target :=
  occurrence.locatedStep.step

namespace ExactlyOne

def step
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Step source target :=
  match one with
  | .single step => step

def canonicalOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history) : Occurrence history :=
  match one with
  | .single _ => .last

theorem occurrence_unique
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence = one.canonicalOccurrence := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_source
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.source = source := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

theorem locatedStep_target
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    {history : History Step source target}
    (one : ExactlyOne history)
    (occurrence : Occurrence history) :
    occurrence.locatedStep.target = target := by
  cases one with
  | single step =>
      cases occurrence with
      | last => rfl
      | earlier impossible => cases impossible

end ExactlyOne

def embedLeftOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    Occurrence (append firstHistory continuation) :=
  match continuation with
  | .root => occurrence
  | .extend continuation _ =>
      .earlier (embedLeftOccurrence occurrence continuation)

theorem embedLeftOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (continuation : History Step b c) :
    Function.Injective
      (fun occurrence : Occurrence firstHistory =>
        embedLeftOccurrence occurrence continuation) := by
  induction continuation with
  | root =>
      intro first second equality
      exact equality
  | extend continuation step inductionHypothesis =>
      intro first second equality
      exact inductionHypothesis (Occurrence.earlier.inj equality)

def embedRightOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Occurrence continuation → Occurrence (append firstHistory continuation)
  | @Occurrence.last _ _ _ _ _ history step =>
      (.last : Occurrence (.extend (append firstHistory history) step))
  | @Occurrence.earlier _ _ _ _ _ history step occurrence =>
      .earlier (embedRightOccurrence firstHistory occurrence)

theorem leftRightDisjoint
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (oldOccurrence : Occurrence firstHistory)
    {continuation : History Step b c}
    (newOccurrence : Occurrence continuation) :
    embedLeftOccurrence oldOccurrence continuation ≠
      embedRightOccurrence firstHistory newOccurrence := by
  induction newOccurrence with
  | last =>
      intro equality
      cases equality
  | earlier occurrence ih =>
      intro equality
      exact ih (Occurrence.earlier.inj equality)

def splitAppendOccurrenceAux
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation
  | .root, occurrence =>
      .inl occurrence
  | .extend previous _step, occurrence =>
      match occurrence with
      | .last => .inr .last
      | .earlier earlier =>
          match splitAppendOccurrenceAux firstHistory previous earlier with
          | .inl old => .inl old
          | .inr new => .inr (.earlier new)

def splitAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    {continuation : History Step b c} :
    Occurrence (append firstHistory continuation) →
      Occurrence firstHistory ⊕ Occurrence continuation :=
  splitAppendOccurrenceAux firstHistory continuation

def classifyAppendOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b) :
    (continuation : History Step b c) →
    (occurrence : Occurrence (append firstHistory continuation)) →
    (Σ old : Occurrence firstHistory,
      PLift (embedLeftOccurrence old continuation = occurrence)) ⊕
      (Σ new : Occurrence continuation,
        PLift (embedRightOccurrence firstHistory new = occurrence))
  | .root, occurrence => .inl ⟨occurrence, ⟨rfl⟩⟩
  | .extend continuation step, occurrence =>
      match occurrence with
      | .last =>
          .inr ⟨(.last : Occurrence (.extend continuation step)), ⟨rfl⟩⟩
      | .earlier occurrence =>
          match classifyAppendOccurrence firstHistory continuation occurrence with
          | .inl ⟨old, reconstruction⟩ =>
              .inl ⟨old,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩
          | .inr ⟨new, reconstruction⟩ =>
              .inr ⟨Occurrence.earlier new,
                ⟨congrArg Occurrence.earlier reconstruction.down⟩⟩

theorem embedRightOccurrence_injective
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c} :
    Function.Injective (embedRightOccurrence firstHistory :
      Occurrence continuation → Occurrence (append firstHistory continuation)) := by
  intro first
  induction first with
  | last =>
      intro second equality
      cases second with
      | last => rfl
      | earlier earlier => cases equality
  | earlier first inductionHypothesis =>
      intro second equality
      cases second with
      | last => cases equality
      | earlier second =>
          exact congrArg Occurrence.earlier
            (inductionHypothesis (Occurrence.earlier.inj equality))

theorem locatedStep_embedLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    {firstHistory : History Step a b}
    (occurrence : Occurrence firstHistory)
    (continuation : History Step b c) :
    (embedLeftOccurrence occurrence continuation).locatedStep =
      occurrence.locatedStep := by
  induction continuation with
  | root => rfl
  | extend continuation step inductionHypothesis =>
      exact inductionHypothesis

theorem locatedStep_embedRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c}
    (occurrence : Occurrence continuation) :
    (embedRightOccurrence firstHistory occurrence).locatedStep =
      occurrence.locatedStep := by
  induction occurrence with
  | last => rfl
  | earlier occurrence inductionHypothesis =>
      exact inductionHypothesis
inductive Vertex
    {State : Type uA}
    {Step : State → State → Type uB} :
    {a b : State} → History Step a b → Type _
  | root : Vertex (.root : History Step a a)
  | earlier : Vertex history → Vertex (.extend history step)
  | final : Vertex (.extend history step)

def initialVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend previous _ => .earlier (initialVertex previous)

def finalVertex
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : Vertex history :=
  match history with
  | .root => .root
  | .extend _ _ => .final

def vertexAppendLeft
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    {firstHistory : History Step source middle}
    (vertex : Vertex firstHistory)
    (continuation : History Step middle target) :
    Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => vertex
  | .extend previous _ =>
      .earlier (vertexAppendLeft vertex previous)

def vertexAppendRight
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    {continuation : History Step middle target} :
    Vertex continuation → Vertex (append firstHistory continuation) :=
  match continuation with
  | .root => fun _ => finalVertex firstHistory
  | .extend _previous _ => fun vertex =>
      match vertex with
      | .earlier previousVertex =>
          .earlier (vertexAppendRight firstHistory previousVertex)
      | .final => .final

def vertex_append_left := @vertexAppendLeft

def vertex_append_right := @vertexAppendRight

structure Positive
    {State : Type uA}
    (Step : State → State → Type uB)
    (a b : State) where
  predecessor : State
  priorHistory : History Step a predecessor
  lastStep : Step predecessor b

def Positive.toHistory
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : History Step a b :=
  .extend positive.priorHistory positive.lastStep

def Positive.lastOccurrence
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (positive : Positive Step a b) : Occurrence positive.toHistory :=
  .last

inductive View
    {State : Type uA}
    {Step : State → State → Type uB}
    {a : State} : {b : State} → History Step a b → Type _
  | root : View (.root : History Step a a)
  | positive {b : State} (path : Positive Step a b) : View path.toHistory

def view
    {State : Type uA}
    {Step : State → State → Type uB}
    {a b : State}
    (history : History Step a b) : View history := by
  cases history with
  | root => exact .root
  | extend priorHistory step =>
      exact .positive ⟨_, priorHistory, step⟩

def rootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source target : State}
    (history : History Step source target) :
    (PLift (target = source) ×
      PLift (HEq history (.root : History Step source source))) ⊕
      (Σ positive : History.Positive Step source target,
        PLift (history = positive.toHistory)) :=
  match history with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

def appendRootOrPositive
    {State : Type uA}
    {Step : State → State → Type uB}
    {source middle target : State}
    (firstHistory : History Step source middle)
    (continuation : History Step middle target) :
    (PLift (target = middle) ×
      PLift (HEq (append firstHistory continuation) firstHistory)) ⊕
      (Σ positive : History.Positive Step middle target,
        PLift (continuation = positive.toHistory)) :=
  match continuation with
  | .root => .inl ⟨⟨rfl⟩, ⟨HEq.rfl⟩⟩
  | .extend priorHistory step =>
      .inr ⟨⟨_, priorHistory, step⟩, ⟨rfl⟩⟩

end History


end RelationalFoundations
