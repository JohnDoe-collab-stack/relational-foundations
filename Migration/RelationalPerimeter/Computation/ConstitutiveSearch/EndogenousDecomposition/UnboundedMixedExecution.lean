import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.AdaptiveRelationalExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableOutputComposition

/-!
# An unbounded family of actually searched mixed productions

Each residual begins with a fresh tautological clause until the final
two-positive clause is reached. The existing flip search succeeds on those
prefixes and fails on the final selected variable. Neither a relation nor a
partition is supplied to the executed local action. Common-tail transmission
is proved from its outputs before the reference history is used.

The profiles remain witnessed occurrences of the relational role history.
Widths below concern the exact stored-output tuple; a cost bound for producing
the history or materializing its frontier is not asserted here.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed
open SAT StrongPerimetralTurning RelationalExtensive Extensive

def formula : Nat → Cnf
  | 0 => [[.positive 0, .positive 1]]
  | count + 1 => [.positive (count + 2), .negative (count + 2)] :: formula count

theorem formula_avoids : (count query : Nat) → count + 1 < query →
    Cnf.AvoidsVar query (formula count)
  | 0, query, larger =>
      ⟨⟨Nat.ne_of_lt (Nat.lt_trans (by decide) larger),
          ⟨Nat.ne_of_lt larger, True.intro⟩⟩, True.intro⟩
  | count + 1, query, larger =>
      ⟨⟨Nat.ne_of_lt larger, ⟨Nat.ne_of_lt larger, True.intro⟩⟩,
        formula_avoids count query (Nat.lt_trans (Nat.lt_succ_self _) larger)⟩

def DecisionsAbove (bound : Nat) : List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest => bound < decision.var ∧ DecisionsAbove bound rest

theorem above_fresh (bound selected : Nat) (before : selected ≤ bound) :
    (decisions : List StructuralBranchDecision) → DecisionsAbove bound decisions →
      StructuralDecisionsAvoid selected decisions
  | [], _ => True.intro
  | _ :: rest, higher =>
      ⟨Nat.ne_of_gt (Nat.lt_of_le_of_lt before higher.1),
        above_fresh bound selected before rest higher.2⟩

theorem above_lower (low high : Nat) (before : low ≤ high) :
    (decisions : List StructuralBranchDecision) → DecisionsAbove high decisions →
      DecisionsAbove low decisions
  | [], _ => True.intro
  | _ :: rest, higher =>
      ⟨Nat.lt_of_le_of_lt before higher.1, above_lower low high before rest higher.2⟩

structure Prepared (source : CausalConstitutiveState) (count : Nat) where
  arrival : GeneratedStructuralBranchContinuation source.operationalState
  assignmentExact : source.assignment = arrival.val
  formulaExact : source.operationalState.context.formula = formula count
  decisionsAbove : DecisionsAbove (count + 1) source.operationalState.context.decisions
  pendingFalse : ∀ query, query ≤ count + 1 → query ≠ 1 → arrival.val query = false
  anchorTrue : arrival.val 1 = true

def initialAssignment : Assignment := fun query => if query = 1 then true else false

def initialState (count : Nat) : CausalConstitutiveState :=
  { constitutedHistory := perimeterDeployment Example.examplePresentation
    rootFormula := formula count
    operationalState := GeneratedStructuralBranchContext.root (formula count)
    assignment := initialAssignment
    searchSeed := 0
    decisions := []
    provenance := []
    provenanceExact := rfl }

def initialPrepared (count : Nat) : Prepared (initialState count) count :=
  { arrival := ⟨initialAssignment, True.intro⟩
    assignmentExact := rfl
    formulaExact := rfl
    decisionsAbove := True.intro
    pendingFalse := fun query _ different => by
      change (if query = 1 then true else false) = false
      exact if_neg different
    anchorTrue := rfl }

def prefixOpening {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) : Opening source :=
  { selected := count + 2
    fresh := above_fresh _ _ (Nat.le_refl _) _ prepared.decisionsAbove
    input := Adaptive.childInput prepared.arrival _
      (above_fresh _ _ (Nat.le_refl _) _ prepared.decisionsAbove) }

theorem prefix_selected_from_state {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    Adaptive.chooseOpening source prepared.arrival = some (prefixOpening prepared) := by
  unfold Adaptive.chooseOpening runCandidateExtraction
  rw [prepared.formulaExact]
  change Adaptive.chooseFromCandidates source prepared.arrival ((count + 2) :: _) = _
  have checked : structuralDecisionsAvoidCheck (count + 2) source.operationalState.context.decisions = true :=
    freshness_check_of_witness _ _ (prefixOpening prepared).fresh
  rw [Adaptive.chooseFromCandidates, List.foldr_cons, dif_pos checked]
  rfl

theorem prefix_residual (count : Nat) (value : Bool) :
    branchResidual (formula (count + 1)) (count + 2) value = formula count := by
  have hit : Clause.containsLiteral (Literal.forValue (count + 2) value)
      [.positive (count + 2), .negative (count + 2)] = true := by
    cases value with
    | false =>
        change (if Literal.negative (count + 2) = Literal.positive (count + 2) then true
          else if Literal.negative (count + 2) = Literal.negative (count + 2) then true else false) = true
        rw [if_neg (by intro impossible; cases impossible), if_pos rfl]
    | true =>
        change (if Literal.positive (count + 2) = Literal.positive (count + 2) then true else _) = true
        rw [if_pos rfl]
  exact (branchResidual_cons_hit _ _ _ _ hit).trans
    (Cnf.branchResidual_eq_self (formula_avoids count (count + 2) (Nat.lt_succ_self _)) value)

def prefixRelation {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    GeneratedStructuralFlipAtRelation (count + 2)
      (source.operationalState.child (count + 2) false (prefixOpening prepared).fresh)
      (source.operationalState.child (count + 2) true (prefixOpening prepared).fresh) :=
  flipSymmetricSiblingRelation source.operationalState _ (prefixOpening prepared).fresh (by
    change FlipSymmetricAt source.operationalState.context.formula (count + 2)
    unfold FlipSymmetricAt
    rw [prepared.formulaExact, prefix_residual, prefix_residual]
    exact (Cnf.flipAt_eq_self (formula_avoids count (count + 2) (Nat.lt_succ_self _))).symm)

theorem prefix_search_succeeds {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    tryEndogenousFlipCandidate source.operationalState (count + 2) ≠ none :=
  tryEndogenousFlipCandidate_found_of_relation _ _
    (freshness_check_of_witness _ _ (prefixOpening prepared).fresh) (prefixRelation prepared)

theorem prefix_selected_false {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) : prepared.arrival.val (count + 2) = false :=
  prepared.pendingFalse _ (Nat.le_refl _) (Nat.ne_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ count)))

theorem prefix_input_false {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    ((prefixOpening prepared).input false).val = prepared.arrival.val := by
  change (Adaptive.childInput prepared.arrival _ _ false).val = _
  unfold Adaptive.childInput
  rw [dif_pos (prefix_selected_false prepared)]

theorem prefix_input_true {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    ((prefixOpening prepared).input true).val = Assignment.flipAt (count + 2) prepared.arrival.val := by
  change (Adaptive.childInput prepared.arrival _ _ true).val = _
  unfold Adaptive.childInput
  rw [dif_neg (by intro same; have impossible := (prefix_selected_false prepared).symm.trans same; cases impossible)]

theorem prefix_output_assignment {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (value : Bool) :
    (produced (identity (prefixOpening prepared) value)).val =
      Assignment.flipAt (count + 2) prepared.arrival.val := by
  cases value with
  | true => exact prefix_input_true prepared
  | false =>
      unfold produced
      rw [canonical_identity]
      dsimp only [action, identity, relationallyConstitutedOccurrence, constituteRealizedOccurrence,
        openingStage, occurrence, toChild, castContinuation, RelationalOpeningStage.formationAt]
      split
      next failed => exact False.elim (prefix_search_succeeds prepared failed)
      next found _ =>
        change Assignment.flipAt (count + 2) ((prefixOpening prepared).input false).val = _
        rw [prefix_input_false]

theorem prefix_converges {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (formed : Identity (prefixOpening prepared)) :
    (prefixOpening prepared).next.assignment = ((executeOpening (prefixOpening prepared)).output formed).val := by
  rw [(executeOpening (prefixOpening prepared)).output_exact]
  have exactFormed := relationallyConstitutedOccurrence_roundTrip formed
  rw [← exactFormed]
  exact (prefix_input_true prepared).trans (prefix_output_assignment prepared formed.position).symm

def nextPrepared {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) : Prepared (prefixOpening prepared).next count :=
  { arrival := (prefixOpening prepared).input true
    assignmentExact := rfl
    formulaExact := by
      change branchResidual source.operationalState.context.formula (count + 2) true = _
      rw [prepared.formulaExact]
      exact prefix_residual count true
    decisionsAbove := ⟨Nat.lt_succ_self _,
      above_lower _ _ (Nat.le_succ _) _ prepared.decisionsAbove⟩
    pendingFalse := fun query before different => by
      rw [prefix_input_true]
      have other : query ≠ count + 2 := Nat.ne_of_lt (Nat.lt_of_le_of_lt before (Nat.lt_succ_self _))
      exact (Assignment.flipAt_other _ _ _ other).trans
        (prepared.pendingFalse query (Nat.le_trans before (Nat.le_succ _)) different)
    anchorTrue := by
      rw [prefix_input_true]
      exact (Assignment.flipAt_other _ _ _ (Nat.ne_of_lt (Nat.succ_lt_succ (Nat.zero_lt_succ count)))).trans
        prepared.anchorTrue }

def terminalOpening {source : CausalConstitutiveState} (prepared : Prepared source 0) : Opening source :=
  { selected := 0
    fresh := above_fresh 1 0 (by decide) _ prepared.decisionsAbove
    input := Adaptive.childInput prepared.arrival _ (above_fresh 1 0 (by decide) _ prepared.decisionsAbove) }

theorem terminal_selected_from_state {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    Adaptive.chooseOpening source prepared.arrival = some (terminalOpening prepared) := by
  unfold Adaptive.chooseOpening runCandidateExtraction
  rw [prepared.formulaExact]
  change Adaptive.chooseFromCandidates source prepared.arrival (0 :: _) = _
  have checked : structuralDecisionsAvoidCheck 0 source.operationalState.context.decisions = true :=
    freshness_check_of_witness _ _ (terminalOpening prepared).fresh
  rw [Adaptive.chooseFromCandidates, List.foldr_cons, dif_pos checked]
  rfl

theorem terminal_search_fails {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    tryEndogenousFlipCandidate source.operationalState 0 = none :=
  tryEndogenousFlipCandidate_none_of_formula_mismatch _ _
    (freshness_check_of_witness _ _ (terminalOpening prepared).fresh) (by
      change branchResidual source.operationalState.context.formula 0 true ≠
        Cnf.flipAt 0 (branchResidual source.operationalState.context.formula 0 false)
      rw [prepared.formulaExact]
      intro same
      have lengths := congrArg List.length same
      cases lengths)

theorem terminal_false {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    (produced (identity (terminalOpening prepared) false)).val = prepared.arrival.val := by
  unfold produced
  rw [canonical_identity]
  dsimp only [action, identity, relationallyConstitutedOccurrence, constituteRealizedOccurrence,
    openingStage, occurrence, toChild, castContinuation, RelationalOpeningStage.formationAt]
  have failed : tryEndogenousFlipCandidate source.operationalState (terminalOpening prepared).selected = none :=
    terminal_search_fails prepared
  rw [failed]
  change (Adaptive.childInput prepared.arrival 0 _ false).val = _
  unfold Adaptive.childInput
  rw [dif_pos (prepared.pendingFalse 0 (by decide) (by decide))]

theorem terminal_true {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    (produced (identity (terminalOpening prepared) true)).val = Assignment.flipAt 0 prepared.arrival.val := by
  change (Adaptive.childInput prepared.arrival 0 _ true).val = _
  unfold Adaptive.childInput
  rw [dif_neg (by
    intro same
    have impossible := (prepared.pendingFalse 0 (by decide) (by decide)).symm.trans same
    cases impossible)]

theorem terminal_distinct {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    produced (identity (terminalOpening prepared) false) ≠ produced (identity (terminalOpening prepared) true) := by
  intro same
  have observed := congrArg (fun output => output.val 0) same
  rw [terminal_false, terminal_true, Assignment.flipAt_selected,
    prepared.pendingFalse 0 (by decide) (by decide)] at observed
  cases observed

def prefixEquality {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    DecidableEq (localImage (executeOpening (prefixOpening prepared))) :=
  ProducedOutputImage.decEq (sourceCarrier (prefixOpening prepared)) _ (fun p q =>
    Subtype.ext ((prefix_converges prepared p).symm.trans (prefix_converges prepared q)))

theorem prefix_width {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    (localRegime (executeOpening (prefixOpening prepared)) (prefixEquality prepared)).frontier.length = 1 :=
  (ProducedOutputImage.image_width_one_iff_converges _ _ _ (identity (prefixOpening prepared) false)).mpr
    (fun p q => Subtype.ext ((prefix_converges prepared p).symm.trans (prefix_converges prepared q)))

theorem terminal_observable_faithful {source : CausalConstitutiveState} (prepared : Prepared source 0)
    (p q : Identity (terminalOpening prepared))
    (same : ((executeOpening (terminalOpening prepared)).output p).val 0 =
      ((executeOpening (terminalOpening prepared)).output q).val 0) :
    (executeOpening (terminalOpening prepared)).output p = (executeOpening (terminalOpening prepared)).output q := by
  have faithful : ∀ b c : Bool,
      (produced (identity (terminalOpening prepared) b)).val 0 =
        (produced (identity (terminalOpening prepared) c)).val 0 →
      produced (identity (terminalOpening prepared) b) = produced (identity (terminalOpening prepared) c) := by
    intro b c observed
    cases b <;> cases c
    · rfl
    · rw [terminal_false, terminal_true, Assignment.flipAt_selected,
        prepared.pendingFalse 0 (by decide) (by decide)] at observed
      cases observed
    · rw [terminal_false, terminal_true, Assignment.flipAt_selected,
        prepared.pendingFalse 0 (by decide) (by decide)] at observed
      cases observed
    · rfl
  rw [(executeOpening _).output_exact, (executeOpening _).output_exact] at same ⊢
  have pe := relationallyConstitutedOccurrence_roundTrip p
  have qe := relationallyConstitutedOccurrence_roundTrip q
  rw [← pe, ← qe] at same ⊢
  exact faithful p.position q.position same

def terminalEquality {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    DecidableEq (localImage (executeOpening (terminalOpening prepared))) :=
  fun left right => match decEq (left.val.val 0) (right.val.val 0) with
  | isTrue same => isTrue (Subtype.ext (by
      rcases left.property with ⟨p, pe⟩
      rcases right.property with ⟨q, qe⟩
      exact pe.symm.trans ((terminal_observable_faithful prepared p q (by rw [pe, qe]; exact same)).trans qe)))
  | isFalse different => isFalse (fun same => different (congrArg (fun value => value.val.val 0) same))

theorem terminal_width {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    (localRegime (executeOpening (terminalOpening prepared)) (terminalEquality prepared)).frontier.length = 2 := by
  rcases local_width_one_or_two (executeOpening (terminalOpening prepared)) (terminalEquality prepared) with one | two
  · have equal := (ProducedOutputImage.image_width_one_iff_converges _ _ _
      (identity (terminalOpening prepared) false)).mp one (identity (terminalOpening prepared) false)
        (identity (terminalOpening prepared) true)
    exact False.elim (terminal_distinct prepared equal)
  · exact two

structure Production (source : CausalConstitutiveState) (count : Nat) where
  history : ProductionHistory source (count + 1)
  comparisons : ImageComparisons history
  transmission : CommonTailAgreement history

def selectedOpening {source : CausalConstitutiveState}
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (expected : Opening source) (selected : Adaptive.chooseOpening source arrival = some expected) : Opening source :=
  (Adaptive.chooseOpening source arrival).get (by rw [selected]; rfl)

theorem selectedOpening_exact {source : CausalConstitutiveState}
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (expected : Opening source) (selected : Adaptive.chooseOpening source arrival = some expected) :
    selectedOpening arrival expected selected = expected := Option.get_of_eq_some _ selected

/-- Only the proof-index is transported. The payload is the local action
actually executed at the opening extracted from the received syntax. -/
def openingExecutionTransport {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) : RelationalFoundations.ExactTransport (LocalProduction left) (LocalProduction right) :=
  RelationalFoundations.ExactTransport.ofEquality (congrArg LocalProduction same)

theorem openingExecutionTransport_exact {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) :
    (openingExecutionTransport same).forward (executeOpening left) = executeOpening right := by
  cases same
  rfl

def executeSelected {source : CausalConstitutiveState}
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (expected : Opening source) (selected : Adaptive.chooseOpening source arrival = some expected) :
    LocalProduction expected :=
  (openingExecutionTransport (selectedOpening_exact arrival expected selected)).forward
    (executeOpening (selectedOpening arrival expected selected))

theorem executeSelected_exact {source : CausalConstitutiveState}
    (arrival : GeneratedStructuralBranchContinuation source.operationalState)
    (expected : Opening source) (selected : Adaptive.chooseOpening source arrival = some expected) :
    executeSelected arrival expected selected = executeOpening expected :=
  openingExecutionTransport_exact (selectedOpening_exact arrival expected selected)

def terminalSelected {source : CausalConstitutiveState} (prepared : Prepared source 0) :=
  executeSelected prepared.arrival (terminalOpening prepared) (terminal_selected_from_state prepared)

def prefixSelected {source : CausalConstitutiveState} {count : Nat} (prepared : Prepared source (count + 1)) :=
  executeSelected prepared.arrival (prefixOpening prepared) (prefix_selected_from_state prepared)

theorem terminalSelected_exact {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    terminalSelected prepared = executeOpening (terminalOpening prepared) := executeSelected_exact _ _ _

theorem prefixSelected_exact {source : CausalConstitutiveState} {count : Nat} (prepared : Prepared source (count + 1)) :
    prefixSelected prepared = executeOpening (prefixOpening prepared) := executeSelected_exact _ _ _

def productionImageEquality {source : CausalConstitutiveState} {opening : Opening source}
    {left right : LocalProduction opening} (same : left = right) (equality : DecidableEq (localImage left)) :
    DecidableEq (localImage right) :=
  (RelationalFoundations.ExactTransport.ofEquality (congrArg (fun head => DecidableEq (localImage head)) same)).forward equality

theorem productionImageWidth {source : CausalConstitutiveState} {opening : Opening source}
    {left right : LocalProduction opening} (same : left = right) (equality : DecidableEq (localImage left)) :
    (localRegime right (productionImageEquality same equality)).frontier.length =
      (localRegime left equality).frontier.length := by
  cases same
  rfl

theorem selectedPrefixTransmits {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (formed : Identity (prefixOpening prepared)) :
    (prefixOpening prepared).next.assignment = ((prefixSelected prepared).output formed).val := by
  rw [(prefixSelected prepared).output_exact, ← (executeOpening (prefixOpening prepared)).output_exact]
  exact prefix_converges prepared formed

theorem actualPrefixTransmits {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (head : LocalProduction (prefixOpening prepared))
    (formed : Identity (prefixOpening prepared)) :
    (prefixOpening prepared).next.assignment = (head.output formed).val := by
  rw [head.output_exact, ← (prefixSelected prepared).output_exact]
  exact selectedPrefixTransmits prepared formed

abbrev selectedTerminalEquality {source : CausalConstitutiveState} (prepared : Prepared source 0) :=
  productionImageEquality (terminalSelected_exact prepared).symm (terminalEquality prepared)

abbrev selectedPrefixEquality {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :=
  productionImageEquality (prefixSelected_exact prepared).symm (prefixEquality prepared)

theorem selectedTerminalWidth {source : CausalConstitutiveState} (prepared : Prepared source 0) :
    (localRegime (terminalSelected prepared) (selectedTerminalEquality prepared)).frontier.length = 2 :=
  (productionImageWidth (terminalSelected_exact prepared).symm _).trans (terminal_width prepared)

theorem selectedPrefixWidth {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) :
    (localRegime (prefixSelected prepared) (selectedPrefixEquality prepared)).frontier.length = 1 :=
  (productionImageWidth (prefixSelected_exact prepared).symm _).trans (prefix_width prepared)

/-- One producer forms the head and its data before recursing on the next
state. Its common future is justified by the actual prefix outputs. -/
def build : (count : Nat) → {source : CausalConstitutiveState} → Prepared source count → Production source count
  | 0, _, prepared =>
      { history := .step (terminalOpening prepared) (terminalSelected prepared) (.nil _)
        comparisons := .step (selectedTerminalEquality prepared) .nil
        transmission := .terminal _ _ }
  | count + 1, _, prepared =>
      let opening := prefixOpening prepared
      let head := prefixSelected prepared
      let tail := build count (nextPrepared prepared)
      { history := .step opening head tail.history
        comparisons := .step (selectedPrefixEquality prepared) tail.comparisons
        transmission := .step (selectedPrefixTransmits prepared) tail.transmission }

def production (count : Nat) : Production (initialState count) count := build count (initialPrepared count)

theorem mixed_width : (count : Nat) → {source : CausalConstitutiveState} → (prepared : Prepared source count) →
    widthProduct (build count prepared).comparisons = 2
  | 0, _, prepared => by
      dsimp only [build, widthProduct]
      exact (congrArg (fun width => width * 1) (selectedTerminalWidth prepared)).trans (Nat.mul_one 2)
  | count + 1, _, prepared => by
      dsimp only [build, widthProduct]
      exact (congrArg (fun width => width * _) (selectedPrefixWidth prepared)).trans
        ((Nat.one_mul _).trans (mixed_width count (nextPrepared prepared)))

theorem produced_width (count : Nat) :
    (composedRegime (production count).comparisons).frontier.length = 2 :=
  (composed_width_product (production count).comparisons).trans (mixed_width count (initialPrepared count))

theorem one_separating_step : (count : Nat) → {source : CausalConstitutiveState} → (prepared : Prepared source count) →
    separatingCount (build count prepared).comparisons = 1
  | 0, _, prepared => by
      dsimp only [build, separatingCount]
      change (if (localRegime _ (selectedTerminalEquality prepared)).frontier.length = 2 then 0 + 1 else 0) = 1
      rw [selectedTerminalWidth, if_pos rfl]
  | count + 1, _, prepared => by
      dsimp only [build, separatingCount]
      change (if (localRegime _ (selectedPrefixEquality prepared)).frontier.length = 2 then _ else _) = 1
      rw [selectedPrefixWidth, if_neg (by decide)]
      exact one_separating_step count (nextPrepared prepared)

theorem history_source_width : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
    (relationalProfileFiniteCarrier history.roles).frontier.length = 2 ^ count
  | _, _, .nil _ => rfl
  | _, count + 1, .step opening _ tail =>
      (productFrontier_length (relationallyConstitutedOccurrenceFrontier (openingStage opening))
        (relationalProfileFrontier tail.roles)).trans
        ((congrArg (Nat.mul 2) (history_source_width tail)).trans
          ((Nat.mul_comm _ _).trans (Nat.pow_succ 2 count).symm))

theorem constituted_width (count : Nat) :
    (relationalProfileFiniteCarrier (production count).history.roles).frontier.length = 2 ^ (count + 1) :=
  history_source_width _

def recordedStages : {source : CausalConstitutiveState} → {count : Nat} → ProductionHistory source count → Nat
  | _, _, .nil _ => 0
  | _, _, .step _ _ tail => recordedStages tail + 1

theorem recordedStages_exact : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) → recordedStages history = count
  | _, _, .nil _ => rfl
  | _, _, .step _ _ tail => congrArg Nat.succ (recordedStages_exact tail)

theorem arbitrarily_many_executed_stages (bound : Nat) :
    bound < recordedStages (production bound).history := by
  rw [recordedStages_exact]
  exact Nat.lt_succ_self bound

theorem formula_satisfied (assignment : Assignment) (anchor : assignment 1 = true) :
    (count : Nat) → Satisfies assignment (formula count)
  | 0 => .cons (by
      change (assignment 0 || (assignment 1 || false)) = true
      rw [anchor]
      cases assignment 0 <;> rfl) .nil
  | count + 1 => .cons (by
      change (assignment (count + 2) || (!(assignment (count + 2)) || false)) = true
      cases assignment (count + 2) <;> rfl) (formula_satisfied assignment anchor count)

theorem prefix_inputs_accepted {source : CausalConstitutiveState} {count : Nat}
    (prepared : Prepared source (count + 1)) (value : Bool) :
    Accept (identity (prefixOpening prepared) value) (canonical (identity (prefixOpening prepared) value)) := by
  change Satisfies ((prefixOpening prepared).input value).val
    (branchResidual source.operationalState.context.formula (count + 2) value)
  rw [prepared.formulaExact, prefix_residual]
  cases value with
  | false =>
      rw [prefix_input_false]
      exact formula_satisfied _ prepared.anchorTrue count
  | true =>
      rw [prefix_input_true]
      exact formula_satisfied _
        ((Assignment.flipAt_other _ _ _ (Nat.ne_of_lt (Nat.succ_lt_succ (Nat.zero_lt_succ count)))).trans
          prepared.anchorTrue) count

theorem terminal_inputs_accepted {source : CausalConstitutiveState} (prepared : Prepared source 0) (value : Bool) :
    Accept (identity (terminalOpening prepared) value) (canonical (identity (terminalOpening prepared) value)) := by
  change Satisfies ((terminalOpening prepared).input value).val
    (branchResidual source.operationalState.context.formula 0 value)
  rw [prepared.formulaExact]
  cases value with
  | false =>
      have inputSame : ((terminalOpening prepared).input false).val = prepared.arrival.val := by
        change (Adaptive.childInput prepared.arrival 0 _ false).val = _
        unfold Adaptive.childInput
        rw [dif_pos (prepared.pendingFalse 0 (by decide) (by decide))]
      change Satisfies _ (formula 0)
      rw [inputSame]
      exact formula_satisfied _ prepared.anchorTrue 0
  | true => exact .nil

def AcceptedStoredTuple : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) → history.Target → Prop
  | _, _, .nil _, _ => True
  | source, _, .step _ _ tail, value =>
      GeneratedStructuralBranchAccept source.operationalState value.1 ∧ AcceptedStoredTuple tail value.2

theorem produced_tuple_accepted : (count : Nat) → {source : CausalConstitutiveState} →
    (prepared : Prepared source count) → (profile : RelationalOccurrenceProfile (build count prepared).history.roles) →
    AcceptedStoredTuple (build count prepared).history ((build count prepared).history.output profile)
  | 0, _, prepared, profile => by
      constructor
      · change GeneratedStructuralBranchAccept _ ((terminalSelected prepared).output profile.1)
        rw [(terminalSelected prepared).output_exact]
        apply action_preserves
        have exactFormed := relationallyConstitutedOccurrence_roundTrip profile.1
        rw [← exactFormed]
        exact terminal_inputs_accepted prepared _
      · exact True.intro
  | count + 1, _, prepared, profile => by
      constructor
      · change GeneratedStructuralBranchAccept _ ((prefixSelected prepared).output profile.1)
        rw [(prefixSelected prepared).output_exact]
        apply action_preserves
        have exactFormed := relationallyConstitutedOccurrence_roundTrip profile.1
        rw [← exactFormed]
        exact prefix_inputs_accepted prepared _
      · exact produced_tuple_accepted count (nextPrepared prepared) profile.2

theorem image_values_accepted (count : Nat) (value : OutputImage (production count).history) :
    AcceptedStoredTuple (production count).history value.val := by
  rcases value.property with ⟨profile, same⟩
  rw [← same]
  exact produced_tuple_accepted count (initialPrepared count) profile

theorem family_has_both_behaviours (count : Nat) :
    (localRegime (prefixSelected (initialPrepared (count + 1)))
      (selectedPrefixEquality (initialPrepared (count + 1)))).frontier.length = 1 ∧
    separatingCount (production (count + 1)).comparisons = 1 :=
  ⟨selectedPrefixWidth _, one_separating_step _ _⟩

theorem openingExecutionTransport_round_trip {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) (head : LocalProduction left) :
    (openingExecutionTransport same).backward ((openingExecutionTransport same).forward head) = head :=
  (openingExecutionTransport same).forwardBackward head

theorem openingExecutionTransport_return {source : CausalConstitutiveState} {left right : Opening source}
    (same : left = right) (head : LocalProduction right) :
    (openingExecutionTransport same).forward ((openingExecutionTransport same).backward head) = head :=
  (openingExecutionTransport same).backwardForward head

end ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.formula
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.formula_avoids
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.above_fresh
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.above_lower
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefixOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_selected_from_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_residual
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefixRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_search_succeeds
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_selected_false
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_input_false
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_input_true
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_output_assignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_converges
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.nextPrepared
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminalOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_selected_from_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_search_fails
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_false
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_true
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefixEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_observable_faithful
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminalEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.build
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.selectedOpening
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.selectedOpening_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.openingExecutionTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.openingExecutionTransport_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.executeSelected
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.executeSelected_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.productionImageEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.productionImageWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.selectedPrefixTransmits
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.actualPrefixTransmits
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.selectedTerminalWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.selectedPrefixWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.production
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.mixed_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.produced_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.one_separating_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.history_source_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.constituted_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.recordedStages
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.recordedStages_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.arbitrarily_many_executed_stages
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.formula_satisfied
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.prefix_inputs_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.terminal_inputs_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.AcceptedStoredTuple
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.produced_tuple_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.image_values_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.family_has_both_behaviours
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.openingExecutionTransport_round_trip
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.openingExecutionTransport_return
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.UnboundedMixed.initialPrepared
/- AXIOM_AUDIT_END -/
