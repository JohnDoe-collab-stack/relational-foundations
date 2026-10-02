import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalFoundationBridge
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileFiniteCarrier
import RelationalPerimeter.Computation.ConstitutiveSearch.ProducedOutputImage
import RelationalPerimeter.Computation.ConstitutiveSearch.SemanticImage
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

/-!
# Local output production without a convergence premise

An opening forms actual generated children of the received causal state.
The action searches for the flip relation at the selected variable; failure
keeps the input, and success applies the relation it found. All outputs live
in the full parent-continuation codomain. No finite code substitutes for that
codomain. Acceptance preservation is separate from output computation.

This extension does not alter the previously audited convergent executor.
Failure of this particular search is not impossibility of other transports.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.VariableExecution
open SAT RelationalExtensive Extensive StrongPerimetralTurning

structure Opening (source : CausalConstitutiveState) where
  selected : Var
  fresh : StructuralDecisionsAvoid selected source.operationalState.context.decisions
  input : (value : Bool) → GeneratedStructuralBranchContinuation
    (source.operationalState.child selected value fresh)

def Opening.next {source : CausalConstitutiveState} (opening : Opening source) :
    CausalConstitutiveState :=
  { constitutedHistory := appendGenerated source.constitutedHistory
      (generate source.constitutedHistory.endpoint)
    rootFormula := source.rootFormula
    operationalState := source.operationalState.child opening.selected true opening.fresh
    assignment := (opening.input true).val
    searchSeed := opening.selected
    decisions := {var := opening.selected, value := true} :: source.decisions
    provenance := opening.selected :: source.provenance
    provenanceExact := congrArg (List.cons opening.selected) source.provenanceExact }

structure Occurrence {source : CausalConstitutiveState} (opening : Opening source) where
  value : Bool
  context : GeneratedStructuralBranchContext source.rootFormula
  formation : GeneratedChildFormation source.operationalState opening.selected value
    opening.fresh context

def occurrence {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) : Occurrence opening :=
  ⟨value, source.operationalState.child opening.selected value opening.fresh, .formed⟩

theorem occurrence_roundTrip {source : CausalConstitutiveState}
    {opening : Opening source} (formed : Occurrence opening) :
    occurrence opening formed.value = formed := by
  rcases formed with ⟨value, context, formation⟩
  cases formation
  rfl

/-- The target relation carries the actual free step as well as its exact state. -/
structure NextFormation {source : CausalConstitutiveState}
    (opening : Opening source) (target : CausalConstitutiveState) where
  step : GeneratedStep source.constitutedHistory.endpoint target.constitutedHistory.endpoint
  exactState : target = opening.next

def openingStage {source : CausalConstitutiveState} (opening : Opening source) :
    RelationalOpeningStage CausalConstitutiveState source opening.next :=
  { Role := Opening source
    Position := Bool
    Occurrence := Occurrence opening
    Provenance := CausalConstitutiveState
    SourceRelation := fun state _ => PLift (state = source)
    FormationRelation := fun role formed => GeneratedChildFormation source.operationalState
      role.selected formed.value role.fresh formed.context
    TargetRelation := NextFormation
    ProvenanceRelation := fun state role formed =>
      PLift (state = source) × GeneratedChildFormation source.operationalState
        role.selected formed.value role.fresh formed.context
    role := opening
    provenance := source
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨(generate source.constitutedHistory.endpoint).2, rfl⟩
    positionDecEq := inferInstance
    positionFrontier := [false, true]
    positionComplete := fun value => by
      cases value with
      | false => exact .head _
      | true => exact .tail _ (.head _)
    positionNodup := by decide
    realize := occurrence opening
    classify := Occurrence.value
    realize_classify := occurrence_roundTrip
    classify_realize := fun _ => rfl
    formationAgreement := fun _ => .formed
    provenanceAgreement := fun _ => ⟨⟨rfl⟩, .formed⟩ }

abbrev Identity {source : CausalConstitutiveState} (opening : Opening source) :=
  RelationallyConstitutedOccurrence (openingStage opening)

def identity {source : CausalConstitutiveState} (opening : Opening source)
    (value : Bool) : Identity opening :=
  relationallyConstitutedOccurrence (openingStage opening) value

def sourceCarrier {source : CausalConstitutiveState} (opening : Opening source) :
    FiniteCarrier :=
  { Identity := Identity opening
    decEq := relationallyConstitutedOccurrenceDecEq (openingStage opening)
    frontier := relationallyConstitutedOccurrenceFrontier (openingStage opening)
    complete := relationallyConstitutedOccurrenceFrontier_complete (openingStage opening)
    nodup := relationallyConstitutedOccurrenceFrontier_nodup (openingStage opening) }

def Payload {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) :=
  GeneratedStructuralBranchContinuation formed.realized.context

def castContinuation {formula : Cnf}
    {left right : GeneratedStructuralBranchContext formula} (same : left = right)
    (payload : GeneratedStructuralBranchContinuation left) :
    GeneratedStructuralBranchContinuation right := same ▸ payload

theorem castContinuation_accept {formula : Cnf}
    {left right : GeneratedStructuralBranchContext formula} (same : left = right)
    (payload : GeneratedStructuralBranchContinuation left)
    (accepted : GeneratedStructuralBranchAccept left payload) :
    GeneratedStructuralBranchAccept right (castContinuation same payload) := by
  cases same
  exact accepted

/-- Eliminate this occurrence's formation to recover the exact child input. -/
def toChild {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) :
    GeneratedStructuralBranchContinuation
      (source.operationalState.child opening.selected formed.realized.value opening.fresh) := by
  have exactChild := formed.formationWitness.down
  exact castContinuation exactChild payload

def canonical {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) : Payload formed := by
  have exactChild := formed.formationWitness.down
  exact castContinuation exactChild.symm (opening.input formed.realized.value)

theorem canonical_identity {source : CausalConstitutiveState} (opening : Opening source) (value : Bool) :
    canonical (identity opening value) = opening.input value := rfl

def action {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) :
    GeneratedStructuralBranchContinuation source.operationalState :=
  let split := generatedStructuralSplit source.operationalState opening.selected opening.fresh
  match value : formed.realized.value with
  | true => split.merge (.inr (value ▸ toChild formed payload))
  | false =>
      let left := value ▸ toChild formed payload
      match tryEndogenousFlipCandidate source.operationalState opening.selected with
      | none => split.merge (.inl left)
      | some found => split.merge (.inr (found.relation.mapContinuation left))

def produced {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) := action formed (canonical formed)

inductive ActionTrace {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) :
    GeneratedStructuralBranchContinuation source.operationalState → Type where
  | executed : ActionTrace formed payload (action formed payload)

structure LocalProduction {source : CausalConstitutiveState} (opening : Opening source) where
  leftOutput : GeneratedStructuralBranchContinuation source.operationalState
  rightOutput : GeneratedStructuralBranchContinuation source.operationalState
  leftTrace : ActionTrace (identity opening false) (canonical (identity opening false)) leftOutput
  rightTrace : ActionTrace (identity opening true) (canonical (identity opening true)) rightOutput

def executeOpening {source : CausalConstitutiveState} (opening : Opening source) :
    LocalProduction opening :=
  ⟨produced (identity opening false), produced (identity opening true), .executed, .executed⟩

theorem ActionTrace.output_exact {source : CausalConstitutiveState} {opening : Opening source}
    {formed : Identity opening} {payload : Payload formed}
    {output : GeneratedStructuralBranchContinuation source.operationalState}
    (trace : ActionTrace formed payload output) : output = action formed payload := by
  cases trace
  rfl

def LocalProduction.output {source : CausalConstitutiveState} {opening : Opening source}
    (headProduction : LocalProduction opening) (formed : Identity opening) :
    GeneratedStructuralBranchContinuation source.operationalState :=
  match formed.position with
  | false => headProduction.leftOutput
  | true => headProduction.rightOutput

theorem LocalProduction.output_exact {source : CausalConstitutiveState} {opening : Opening source}
    (headProduction : LocalProduction opening) (formed : Identity opening) :
    headProduction.output formed = produced formed := by
  have both : ∀ value : Bool,
      headProduction.output (identity opening value) = produced (identity opening value) := by
    intro value
    cases value
    · exact headProduction.leftTrace.output_exact
    · exact headProduction.rightTrace.output_exact
  have exactFormed := relationallyConstitutedOccurrence_roundTrip formed
  exact exactFormed ▸ both formed.position

theorem next_assignment_exact {source : CausalConstitutiveState} (opening : Opening source) :
    opening.next.assignment = (executeOpening opening).rightOutput.val := rfl

/-- A local production exists before its dependent tail. -/
inductive ProductionHistory : (source : CausalConstitutiveState) → Nat → Type 1 where
  | nil (source : CausalConstitutiveState) : ProductionHistory source 0
  | step {source : CausalConstitutiveState} {count : Nat}
      (opening : Opening source) (headProduction : LocalProduction opening)
      (tail : ProductionHistory opening.next count) : ProductionHistory source (count + 1)

def ProductionHistory.roles : {source : CausalConstitutiveState} → {count : Nat} →
    ProductionHistory source count → DependentRelationalRoleHistory CausalConstitutiveState source count
  | _, _, .nil source => .nil source
  | _, _, .step opening _ tail => .step (openingStage opening) tail.roles

def ProductionHistory.Target : {source : CausalConstitutiveState} → {count : Nat} →
    ProductionHistory source count → Type
  | _, _, .nil _ => Unit
  | source, _, .step _ _ tail =>
      GeneratedStructuralBranchContinuation source.operationalState × tail.Target

/-- Interpretation reads the already-produced local outputs. It performs no new search. -/
def ProductionHistory.output : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
      RelationalOccurrenceProfile history.roles → history.Target
  | _, _, .nil _, _ => ()
  | _, _, .step _ headProduction tail, profile =>
      (headProduction.output profile.1, tail.output profile.2)

theorem ProductionHistory.head_independent {source : CausalConstitutiveState}
    {count : Nat} (opening : Opening source) (headProduction : LocalProduction opening)
    (leftTail rightTail : ProductionHistory opening.next count)
    (formed : Identity opening)
    (leftProfile : RelationalOccurrenceProfile leftTail.roles)
    (rightProfile : RelationalOccurrenceProfile rightTail.roles) :
    ((ProductionHistory.step opening headProduction leftTail).output (formed, leftProfile)).1 =
      ((ProductionHistory.step opening headProduction rightTail).output (formed, rightProfile)).1 := rfl

def Accept {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) : Prop :=
  GeneratedStructuralBranchAccept formed.realized.context payload

theorem toChild_accept {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) (accepted : Accept formed payload) :
    GeneratedStructuralBranchAccept
      (source.operationalState.child opening.selected formed.realized.value opening.fresh)
      (toChild formed payload) := by
  exact castContinuation_accept formed.formationWitness.down payload accepted

theorem canonical_action_preserves {source : CausalConstitutiveState}
    (opening : Opening source) (value : Bool)
    (payload : Payload (identity opening value))
    (accepted : Accept (identity opening value) payload) :
    GeneratedStructuralBranchAccept source.operationalState
      (action (identity opening value) payload) := by
  cases value with
  | true =>
      exact (generatedStructuralSplit source.operationalState opening.selected opening.fresh).mergePreservesAccept
        (.inr payload) accepted
  | false =>
      change GeneratedStructuralBranchAccept source.operationalState
        (match tryEndogenousFlipCandidate source.operationalState opening.selected with
        | none => (generatedStructuralSplit source.operationalState opening.selected opening.fresh).merge (.inl payload)
        | some found => (generatedStructuralSplit source.operationalState opening.selected opening.fresh).merge
          (.inr (found.relation.mapContinuation payload)))
      split
      next =>
        exact (generatedStructuralSplit source.operationalState opening.selected opening.fresh).mergePreservesAccept
          (.inl payload) accepted
      next found _ =>
        exact (generatedStructuralSplit source.operationalState opening.selected opening.fresh).mergePreservesAccept
          (.inr (found.relation.mapContinuation payload))
            (found.relation.mapContinuation_accept _ accepted)

/-- Uses the searched relation's preservation, not equality of the canonical outputs. -/
theorem action_preserves {source : CausalConstitutiveState} {opening : Opening source}
    (formed : Identity opening) (payload : Payload formed) (accepted : Accept formed payload) :
    GeneratedStructuralBranchAccept source.operationalState (action formed payload) := by
  have general : ∀ formed : Identity opening, ∀ payload : Payload formed,
      Accept formed payload → GeneratedStructuralBranchAccept source.operationalState (action formed payload) := by
    intro current
    have exactCurrent := relationallyConstitutedOccurrence_roundTrip current
    exact exactCurrent ▸ (canonical_action_preserves opening current.position)
  exact general formed payload accepted

def reflect {source : CausalConstitutiveState} (opening : Opening source)
    (target : GeneratedStructuralBranchContinuation source.operationalState) :
    Sigma (fun formed : Identity opening => Payload formed) :=
  match (generatedStructuralSplit source.operationalState opening.selected opening.fresh).split target with
  | .inl payload => ⟨identity opening false, payload⟩
  | .inr payload => ⟨identity opening true, payload⟩

theorem reflect_accept {source : CausalConstitutiveState} (opening : Opening source)
    (target : GeneratedStructuralBranchContinuation source.operationalState)
    (accepted : GeneratedStructuralBranchAccept source.operationalState target) :
    Accept (reflect opening target).1 (reflect opening target).2 := by
  have valid := (generatedStructuralSplit source.operationalState opening.selected opening.fresh).splitPreservesAccept
    target accepted
  unfold reflect
  split <;> rename_i payload equation <;> rw [equation] at valid <;> exact valid

def description {source : CausalConstitutiveState} (opening : Opening source) :
    SemanticImage.Description :=
  { Source := Identity opening
    Payload := Payload
    Target := GeneratedStructuralBranchContinuation source.operationalState
    Accept := Accept
    TargetAccept := GeneratedStructuralBranchAccept source.operationalState
    action := action
    canonical := canonical
    produced := produced
    reflect := reflect opening
    SourceInvariant := identity opening false ≠ identity opening true }

theorem source_distinct {source : CausalConstitutiveState} (opening : Opening source) :
    identity opening false ≠ identity opening true := by
  intro same
  have impossible := congrArg (fun formed : Identity opening => formed.realized.value) same
  cases impossible

theorem admission {source : CausalConstitutiveState} (opening : Opening source) :
    SemanticImage.Admission (description opening) :=
  { invariant := source_distinct opening
    canonicalExact := fun _ => rfl
    preservation := action_preserves
    reflection := reflect_accept opening }

abbrev AdmittedOutput {source : CausalConstitutiveState} (opening : Opening source) :=
  SemanticImage.AdmittedImageValue (description opening)
    (fun value => ∃ formed : Identity opening, produced formed = value)

/-- Realization acts between image values and admitted values, not between
source identities and their regrouped image. Both return laws are explicit. -/
def admittedOutputTransport {source : CausalConstitutiveState} (opening : Opening source) :
    RelationalFoundations.ExactTransport (ProducedOutputImage.Value (sourceCarrier opening) produced)
      (AdmittedOutput opening) :=
  { forward := fun value => ⟨value.val, value.property, (admission opening).specification value.val⟩
    backward := fun value => ⟨value.value, value.produced⟩
    forwardBackward := fun _ => rfl
    backwardForward := fun _ => SemanticImage.AdmittedImageValue.eq_of_value_eq rfl }

def ofConvergentStage {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) : Opening source :=
  { selected := stage.selected
    fresh := stage.fresh
    input := fun value => match value with
      | false => stage.sourceContinuation
      | true => stage.outputContinuation }

theorem freshness_check_of_witness (selected : Var)
    (decisions : List StructuralBranchDecision) (fresh : StructuralDecisionsAvoid selected decisions) :
    structuralDecisionsAvoidCheck selected decisions = true := by
  induction decisions with
  | nil => rfl
  | cons head tail ih =>
      rw [structuralDecisionsAvoidCheck, if_neg fresh.1]
      exact ih fresh.2

/-- The old executed action, not only its width, is retained as a specialization. -/
theorem convergent_stage_output {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    produced (identity (ofConvergentStage stage) false) =
      produced (identity (ofConvergentStage stage) true) := by
  have found := tryEndogenousFlipCandidate_found_of_relation source.operationalState stage.selected
    (freshness_check_of_witness stage.selected _ stage.fresh) stage.relation
  unfold produced
  rw [canonical_identity, canonical_identity]
  dsimp only [action, ofConvergentStage, identity, relationallyConstitutedOccurrence,
    constituteRealizedOccurrence, openingStage, occurrence, toChild, castContinuation,
    RelationalOpeningStage.formationAt]
  split
  next equation => exact False.elim (found equation)
  next candidate _ =>
    have same : candidate.relation = stage.relation := by
      cases candidate.relation
      cases stage.relation
      rfl
    rw [same]
    exact congrArg (fun result =>
      (generatedStructuralSplit source.operationalState stage.selected stage.fresh).merge
        (.inr result)) stage.outputExact.symm

/-- A finite observable suffices only when it is faithful on the actual image. -/
def imageEquality {source : CausalConstitutiveState} (opening : Opening source)
    (query : Var)
    (faithful : ∀ p q : Identity opening,
      (produced p).val query = (produced q).val query → produced p = produced q) :
    DecidableEq (ProducedOutputImage.Value (sourceCarrier opening) produced) :=
  fun left right =>
    match decEq (left.val.val query) (right.val.val query) with
    | isTrue same => isTrue (Subtype.ext (by
        rcases left.property with ⟨p, pe⟩
        rcases right.property with ⟨q, qe⟩
        exact pe.symm.trans ((faithful p q (by rw [pe, qe]; exact same)).trans qe)))
    | isFalse different => isFalse (fun same =>
        different (congrArg (fun value => value.val.val query) same))

namespace MixedExample

def formula : Cnf :=
  [[.positive 0, .positive 1, .positive 2],
   [.negative 0, .positive 1, .positive 2]]

def initialAssignment : Assignment
  | 2 => true
  | _ => false

def initialState : CausalConstitutiveState :=
  { constitutedHistory := perimeterDeployment Example.examplePresentation
    rootFormula := formula
    operationalState := GeneratedStructuralBranchContext.root formula
    assignment := initialAssignment
    searchSeed := 0
    decisions := []
    provenance := []
    provenanceExact := rfl }

def first : Opening initialState :=
  { selected := 0
    fresh := True.intro
    input := fun value => match value with
      | false => ⟨initialState.assignment, ⟨rfl, True.intro⟩⟩
      | true => ⟨Assignment.flipAt 0 initialState.assignment, ⟨rfl, True.intro⟩⟩ }

/-- This state receives the first produced assignment, not an independent seed. -/
def second : Opening first.next :=
  { selected := 1
    fresh := ⟨by decide, True.intro⟩
    input := fun value => match value with
      | false => ⟨first.next.assignment, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩
      | true => ⟨Assignment.flipAt 1 first.next.assignment, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩ }

def selectFresh {formula : Cnf} (state : GeneratedStructuralBranchContext formula) : Option Var :=
  (runCandidateExtraction state).candidates.find? (fun selected =>
    structuralDecisionsAvoidCheck selected state.context.decisions)

theorem first_selection : selectFresh initialState.operationalState = some first.selected := rfl
theorem second_selection : selectFresh first.next.operationalState = some second.selected := rfl

theorem first_discovery :
    (runEndogenousFlipDiscovery initialState.operationalState).outcome.discovered?.isSome = true := rfl

theorem second_discovery :
    (runEndogenousFlipDiscovery first.next.operationalState).outcome.discovered? = none := rfl

theorem first_action_output : produced (identity first false) = produced (identity first true) := rfl

theorem next_assignment_is_produced :
    first.next.assignment = (produced (identity first false)).val := rfl

theorem second_outputs_distinct : produced (identity second false) ≠ produced (identity second true) := by
  intro same
  have impossible := congrArg (fun value => value.val 1) same
  cases impossible

/-- These are canonical inputs, not hypotheses of satisfiability. -/
theorem first_inputs_viable (value : Bool) : Accept (identity first value) (canonical (identity first value)) := by
  cases value <;> exact .cons rfl .nil

theorem second_inputs_viable (value : Bool) : Accept (identity second value) (canonical (identity second value)) := by
  cases value with
  | false => exact .cons rfl .nil
  | true => exact .nil

theorem first_converges (p q : Identity first) : produced p = produced q := by
  have pe := relationallyConstitutedOccurrence_roundTrip p
  have qe := relationallyConstitutedOccurrence_roundTrip q
  rw [← pe, ← qe]
  cases p.position <;> cases q.position <;> rfl

theorem second_observable_faithful (p q : Identity second)
    (same : (produced p).val 1 = (produced q).val 1) : produced p = produced q := by
  have canonicalFaithful : ∀ b c : Bool,
      (produced (identity second b)).val 1 = (produced (identity second c)).val 1 →
      produced (identity second b) = produced (identity second c) := by
    intro b c equal
    cases b <;> cases c
    · rfl
    · cases equal
    · cases equal
    · rfl
  have pe := relationallyConstitutedOccurrence_roundTrip p
  have qe := relationallyConstitutedOccurrence_roundTrip q
  rw [← pe, ← qe] at same ⊢
  exact canonicalFaithful p.position q.position same

def firstRegime := ProducedOutputImage.imageRegime (sourceCarrier first) produced
  (imageEquality first 0 (fun p q _ => first_converges p q))

def secondRegime := ProducedOutputImage.imageRegime (sourceCarrier second) produced
  (imageEquality second 1 second_observable_faithful)

theorem first_width : firstRegime.frontier.length = 1 :=
  (ProducedOutputImage.image_width_one_iff_converges (sourceCarrier first) produced
    (imageEquality first 0 (fun p q _ => first_converges p q))
    (identity first false)).mpr first_converges

theorem second_width : secondRegime.frontier.length = 2 := rfl

def history : DependentRelationalRoleHistory CausalConstitutiveState initialState 2 :=
  .step (openingStage first) (.step (openingStage second) (.nil second.next))

def production : ProductionHistory initialState 2 :=
  .step first (executeOpening first) (.step second (executeOpening second) (.nil second.next))

theorem production_roles_exact : production.roles = history := rfl

theorem production_transmits_output :
    first.next.assignment = (executeOpening first).leftOutput.val ∧
      first.next.assignment = (executeOpening first).rightOutput.val := ⟨rfl, rfl⟩

def profiles := relationalProfileFiniteCarrier history

def mixedOutput (profile : profiles.Identity) :=
  let outputs := production.output profile
  (outputs.1, outputs.2.1)

theorem mixedOutput_exact (profile : profiles.Identity) :
    mixedOutput profile = (produced profile.1, produced profile.2.1) :=
  Prod.ext ((executeOpening first).output_exact profile.1)
    ((executeOpening second).output_exact profile.2.1)

theorem mixed_observable_faithful (p q : profiles.Identity)
    (same : (mixedOutput p).2.val 1 = (mixedOutput q).2.val 1) : mixedOutput p = mixedOutput q := by
  rw [mixedOutput_exact p, mixedOutput_exact q] at same ⊢
  exact Prod.ext (first_converges p.1 q.1) (second_observable_faithful p.2.1 q.2.1 same)

def mixedImageEquality : DecidableEq (ProducedOutputImage.Value profiles mixedOutput) :=
  fun left right =>
    match decEq (left.val.2.val 1) (right.val.2.val 1) with
    | isTrue same => isTrue (Subtype.ext (by
        rcases left.property with ⟨p, pe⟩
        rcases right.property with ⟨q, qe⟩
        exact pe.symm.trans ((mixed_observable_faithful p q (by rw [pe, qe]; exact same)).trans qe)))
    | isFalse different => isFalse (fun same =>
        different (congrArg (fun value => value.val.2.val 1) same))

def mixedRegime := ProducedOutputImage.imageRegime profiles mixedOutput mixedImageEquality

theorem profile_width : profiles.frontier.length = 4 := rfl
theorem mixed_width : mixedRegime.frontier.length = 2 := rfl

theorem mixed_fibres (p q : profiles.Identity) :
    mixedRegime.carry p = mixedRegime.carry q ↔ mixedOutput p = mixedOutput q :=
  ProducedOutputImage.image_carry_fibres profiles mixedOutput mixedImageEquality p q

theorem mixed_grouping (secondValue : Bool) :
    mixedRegime.carry (identity first false, identity second secondValue, ()) =
      mixedRegime.carry (identity first true, identity second secondValue, ()) :=
  (mixed_fibres _ _).mpr (Prod.ext first_action_output rfl)

theorem mixed_separation (firstValue : Bool) :
    mixedRegime.carry (identity first firstValue, identity second false, ()) ≠
      mixedRegime.carry (identity first firstValue, identity second true, ()) := by
  intro same
  exact second_outputs_distinct (congrArg Prod.snd ((mixed_fibres _ _).mp same))

/-- Convergence justifies the common tail for every first-stage occurrence. -/
theorem second_source_matches_each_first (formed : Identity first) :
    first.next.assignment = (produced formed).val :=
  next_assignment_is_produced.trans (congrArg Subtype.val
    (first_converges (identity first false) formed))

/-- Restore the final continuation through the actual first child formation.
The target is a full continuation of the initial problem, not a pair of labels. -/
def finalOutput (profile : profiles.Identity) :
    GeneratedStructuralBranchContinuation initialState.operationalState :=
  (generatedStructuralSplit initialState.operationalState first.selected first.fresh).merge
    (.inr (production.output profile).2.1)

theorem finalOutput_exact (profile : profiles.Identity) :
    finalOutput profile =
      (generatedStructuralSplit initialState.operationalState first.selected first.fresh).merge
        (.inr (produced profile.2.1)) :=
  congrArg (fun output =>
    (generatedStructuralSplit initialState.operationalState first.selected first.fresh).merge (.inr output))
      ((executeOpening second).output_exact profile.2.1)

theorem finalOutput_accept (profile : profiles.Identity) :
    GeneratedStructuralBranchAccept initialState.operationalState (finalOutput profile) := by
  have inputAccepted : Accept profile.2.1 (canonical profile.2.1) := by
    have same := relationallyConstitutedOccurrence_roundTrip profile.2.1
    exact same ▸ second_inputs_viable profile.2.1.position
  have outputAccepted := action_preserves profile.2.1 (canonical profile.2.1) inputAccepted
  rw [finalOutput_exact]
  exact (generatedStructuralSplit initialState.operationalState first.selected first.fresh).mergePreservesAccept
    (.inr (produced profile.2.1)) outputAccepted

theorem final_observable_faithful (p q : profiles.Identity)
    (same : (finalOutput p).val 1 = (finalOutput q).val 1) : finalOutput p = finalOutput q := by
  rw [finalOutput_exact p, finalOutput_exact q] at same ⊢
  have secondSame := second_observable_faithful p.2.1 q.2.1 same
  exact congrArg (fun output =>
    (generatedStructuralSplit initialState.operationalState first.selected first.fresh).merge
      (.inr output)) secondSame

def finalImageEquality : DecidableEq (ProducedOutputImage.Value profiles finalOutput) :=
  fun left right =>
    match decEq (left.val.val 1) (right.val.val 1) with
    | isTrue same => isTrue (Subtype.ext (by
        rcases left.property with ⟨p, pe⟩
        rcases right.property with ⟨q, qe⟩
        exact pe.symm.trans ((final_observable_faithful p q (by rw [pe, qe]; exact same)).trans qe)))
    | isFalse different => isFalse (fun same =>
        different (congrArg (fun value => value.val.val 1) same))

def finalRegime := ProducedOutputImage.imageRegime profiles finalOutput finalImageEquality

theorem final_width : finalRegime.frontier.length = 2 := rfl

theorem final_fibres (p q : profiles.Identity) :
    finalRegime.carry p = finalRegime.carry q ↔ finalOutput p = finalOutput q :=
  ProducedOutputImage.image_carry_fibres profiles finalOutput finalImageEquality p q

end MixedExample

end ConstitutiveSearch.EndogenousDecomposition.VariableExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.Opening.next
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.openingStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.toChild
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.action
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.executeOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.ActionTrace.output_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.LocalProduction.output_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.next_assignment_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.ProductionHistory.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.ProductionHistory.output
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.ProductionHistory.head_independent
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.action_preserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.reflect_accept
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.admission
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.admittedOutputTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.ofConvergentStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.convergent_stage_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.imageEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.first_selection
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_selection
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.first_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_discovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.next_assignment_is_produced
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_outputs_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.first_inputs_viable
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_inputs_viable
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.first_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.profile_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.mixed_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.mixedOutput_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.mixed_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.mixed_grouping
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.mixed_separation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.production_roles_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.production_transmits_output
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.second_source_matches_each_first
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.finalOutput_accept
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.final_observable_faithful
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.final_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.final_fibres
/- AXIOM_AUDIT_END -/
