import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableRelationalExecution

/-!
# Exact composition of stored local output images

The source is the constituted profile carrier of the production history.
Each local image reads the output stored by its executed action trace. The
composed obligation realizes the entire tuple of these outputs, with both
return laws. Neither a partition nor a convergence premise is supplied.

This tuple interpretation is not a theorem that every alternative may use
the reference trajectory's tail. Common-tail transmission is a separate
agreement below. It is closed for the mixed example, whose separating step
is terminal. No claim about arbitrary adaptive trees or total runtime is made.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.VariableExecution
open SAT RelationalExtensive Extensive

def localImage {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) :=
  ProducedOutputImage.Value (sourceCarrier opening) head.output

/-- Equality on actual image values, not on the full function codomain. -/
inductive ImageComparisons : {source : CausalConstitutiveState} → {count : Nat} →
    ProductionHistory source count → Type 1 where
  | nil {source : CausalConstitutiveState} : ImageComparisons (.nil source)
  | step {source : CausalConstitutiveState} {count : Nat}
      {opening : Opening source} {head : LocalProduction opening}
      {tail : ProductionHistory opening.next count}
      (equality : DecidableEq (localImage head)) (rest : ImageComparisons tail) :
      ImageComparisons (.step opening head tail)

def localRegime {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (equality : DecidableEq (localImage head)) :=
  ProducedOutputImage.imageRegime (sourceCarrier opening) head.output equality

def ProductImage : {source : CausalConstitutiveState} → {count : Nat} →
    ProductionHistory source count → Type
  | _, _, .nil _ => Unit
  | _, _, .step _ head tail => localImage head × ProductImage tail

def productCarry : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
    RelationalOccurrenceProfile history.roles → ProductImage history
  | _, _, .nil _, _ => ()
  | _, _, .step opening head tail, profile =>
      (ProducedOutputImage.carry (sourceCarrier opening) head.output profile.1,
        productCarry tail profile.2)

def productValue : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) → ProductImage history → history.Target
  | _, _, .nil _, _ => ()
  | _, _, .step _ _ tail, value => (value.1.val, productValue tail value.2)

theorem productValue_carry : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
    (profile : RelationalOccurrenceProfile history.roles) →
    productValue history (productCarry history profile) = history.output profile
  | _, _, .nil _, _ => rfl
  | _, _, .step _ _ tail, profile => Prod.ext rfl (productValue_carry tail profile.2)

theorem productValue_injective : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
    (left right : ProductImage history) →
    productValue history left = productValue history right → left = right
  | _, _, .nil _, left, right, _ => by cases left; cases right; rfl
  | _, _, .step _ _ tail, left, right, same =>
      Prod.ext (Subtype.ext (congrArg Prod.fst same))
        (productValue_injective tail left.2 right.2 (congrArg Prod.snd same))

theorem productCarry_surjective : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) →
    (value : ProductImage history) → ∃ profile, productCarry history profile = value
  | _, _, .nil _, value => by cases value; exact ⟨(), rfl⟩
  | _, _, .step _ _ tail, value => by
      rcases value.1.property with ⟨formed, exactHead⟩
      rcases productCarry_surjective tail value.2 with ⟨profile, exactTail⟩
      exact ⟨(formed, profile), Prod.ext (Subtype.ext exactHead) exactTail⟩

def OutputImage {source : CausalConstitutiveState} {count : Nat}
    (history : ProductionHistory source count) :=
  ProducedOutputImage.Value (relationalProfileFiniteCarrier history.roles) history.output

def toOutputImage {source : CausalConstitutiveState} {count : Nat}
    (history : ProductionHistory source count) (value : ProductImage history) : OutputImage history :=
  ⟨productValue history value, by
    rcases productCarry_surjective history value with ⟨profile, exactValue⟩
    exact ⟨profile, (productValue_carry history profile).symm.trans
      (congrArg (productValue history) exactValue)⟩⟩

/-- Read the target tuple itself; no source is selected from image membership. -/
def fromOutputImage : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) → OutputImage history → ProductImage history
  | _, _, .nil _, _ => ()
  | _, _, .step _ _ tail, value =>
      (⟨value.val.1, by
        rcases value.property with ⟨profile, exactValue⟩
        exact ⟨profile.1, congrArg Prod.fst exactValue⟩⟩,
       fromOutputImage tail ⟨value.val.2, by
        rcases value.property with ⟨profile, exactValue⟩
        exact ⟨profile.2, congrArg Prod.snd exactValue⟩⟩)

theorem fromOutputImage_value : {source : CausalConstitutiveState} → {count : Nat} →
    (history : ProductionHistory source count) → (value : OutputImage history) →
    productValue history (fromOutputImage history value) = value.val
  | _, _, .nil _, value => by cases value.val; rfl
  | _, _, .step _ _ tail, value =>
      Prod.ext rfl (fromOutputImage_value tail _)

def outputTransport {source : CausalConstitutiveState} {count : Nat}
    (history : ProductionHistory source count) :
    RelationalFoundations.ExactTransport (ProductImage history) (OutputImage history) :=
  { forward := toOutputImage history
    backward := fromOutputImage history
    forwardBackward := fun value => productValue_injective history _ _
      (fromOutputImage_value history (toOutputImage history value))
    backwardForward := fun value => Subtype.ext (fromOutputImage_value history value) }

def imageFrontier : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → ImageComparisons history → List (ProductImage history)
  | _, _, _, .nil => [()]
  | _, _, _, .step equality rest =>
      productFrontier (localRegime _ equality).frontier (imageFrontier rest)

def productEquality : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → ImageComparisons history → DecidableEq (ProductImage history)
  | _, _, _, .nil => fun left right => by cases left; cases right; exact isTrue rfl
  | _, _, _, .step equality rest => fun left right =>
      match equality left.1 right.1 with
      | isFalse different => isFalse (fun same => different (congrArg Prod.fst same))
      | isTrue sameHead => match productEquality rest left.2 right.2 with
          | isFalse different => isFalse (fun same => different (congrArg Prod.snd same))
          | isTrue sameTail => isTrue (Prod.ext sameHead sameTail)

theorem imageFrontier_complete : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → (comparisons : ImageComparisons history) →
    (value : ProductImage history) → value ∈ imageFrontier comparisons
  | _, _, _, .nil, value => by cases value; exact .head _
  | _, _, _, .step equality rest, value =>
      productFrontier_complete ((localRegime _ equality).complete value.1)
        (imageFrontier_complete rest value.2)

theorem imageFrontier_nodup : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → (comparisons : ImageComparisons history) →
    (imageFrontier comparisons).Nodup
  | _, _, _, .nil => .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, .step equality rest => by
      letI := equality
      letI := productEquality rest
      exact productFrontier_nodup (localRegime _ equality).nodup (imageFrontier_nodup rest)

def composedRegime {source : CausalConstitutiveState} {count : Nat}
    {history : ProductionHistory source count} (comparisons : ImageComparisons history) :
    ObligationRegime (relationalProfileFiniteCarrier history.roles) :=
  { Obligation := ProductImage history
    decEq := productEquality comparisons
    frontier := imageFrontier comparisons
    complete := imageFrontier_complete comparisons
    nodup := imageFrontier_nodup comparisons
    carry := productCarry history
    carry_surjective := productCarry_surjective history }

theorem composed_fibres {source : CausalConstitutiveState} {count : Nat}
    {history : ProductionHistory source count} (comparisons : ImageComparisons history)
    (left right : RelationalOccurrenceProfile history.roles) :
    (composedRegime comparisons).carry left = (composedRegime comparisons).carry right ↔
      history.output left = history.output right := by
  constructor
  · intro same
    exact (productValue_carry history left).symm.trans
      ((congrArg (productValue history) same).trans (productValue_carry history right))
  · intro same
    apply productValue_injective history
    exact (productValue_carry history left).trans (same.trans (productValue_carry history right).symm)

def widthProduct : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → ImageComparisons history → Nat
  | _, _, _, .nil => 1
  | _, _, _, .step equality rest => (localRegime _ equality).frontier.length * widthProduct rest

theorem composed_width_product : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → (comparisons : ImageComparisons history) →
    (composedRegime comparisons).frontier.length = widthProduct comparisons
  | _, _, _, .nil => rfl
  | _, _, _, .step equality rest => by
      change (productFrontier _ (imageFrontier rest)).length = _
      exact (productFrontier_length (localRegime _ equality).frontier (imageFrontier rest)).trans
        (congrArg (fun width => (localRegime _ equality).frontier.length * width)
          (composed_width_product rest))

theorem deduplicate_pair_width {Value : Type} (equality : DecidableEq Value)
    (left right : Value) :
    (deduplicate equality [left, right]).length = 1 ∨
      (deduplicate equality [left, right]).length = 2 := by
  change (if containsWith equality left [right] then [right] else [left, right]).length = 1 ∨
    (if containsWith equality left [right] then [right] else [left, right]).length = 2
  cases equation : containsWith equality left [right] with
  | true =>
      left
      rfl
  | false =>
      right
      rfl

theorem local_width_one_or_two {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (equality : DecidableEq (localImage head)) :
    (localRegime head equality).frontier.length = 1 ∨
      (localRegime head equality).frontier.length = 2 :=
  deduplicate_pair_width equality _ _

/-- A readout of computed local images, never a supplied partition control. -/
def separatingCount : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → ImageComparisons history → Nat
  | _, _, _, .nil => 0
  | _, _, _, .step equality rest =>
      if (localRegime _ equality).frontier.length = 2 then separatingCount rest + 1
      else separatingCount rest

theorem widthProduct_pow : {source : CausalConstitutiveState} → {count : Nat} →
    {history : ProductionHistory source count} → (comparisons : ImageComparisons history) →
    widthProduct comparisons = 2 ^ separatingCount comparisons
  | _, _, _, .nil => rfl
  | _, _, _, .step equality rest => by
      rcases local_width_one_or_two _ equality with one | two
      · change (localRegime _ equality).frontier.length * widthProduct rest =
          2 ^ (if (localRegime _ equality).frontier.length = 2 then _ else _)
        rw [one]
        change 1 * widthProduct rest = 2 ^ separatingCount rest
        exact (Nat.one_mul _).trans (widthProduct_pow rest)
      · change (localRegime _ equality).frontier.length * widthProduct rest =
          2 ^ (if (localRegime _ equality).frontier.length = 2 then _ else _)
        rw [two]
        change 2 * widthProduct rest = 2 ^ (separatingCount rest + 1)
        exact (congrArg (Nat.mul 2) (widthProduct_pow rest)).trans
          ((Nat.mul_comm _ _).trans (Nat.pow_succ 2 _).symm)

theorem composed_width_pow {source : CausalConstitutiveState} {count : Nat}
    {history : ProductionHistory source count} (comparisons : ImageComparisons history) :
    (composedRegime comparisons).frontier.length = 2 ^ separatingCount comparisons :=
  (composed_width_product comparisons).trans (widthProduct_pow comparisons)

/-- Agreement about actual stored outputs required before a nonterminal
opening may transmit all its alternatives to its reference trajectory. -/
inductive CommonTailAgreement : {source : CausalConstitutiveState} → {count : Nat} →
    ProductionHistory source count → Type 1 where
  | nil {source : CausalConstitutiveState} : CommonTailAgreement (.nil source)
  | terminal {source : CausalConstitutiveState}
      (opening : Opening source) (head : LocalProduction opening) :
      CommonTailAgreement (.step opening head (.nil opening.next))
  | step {source : CausalConstitutiveState} {count : Nat}
      {opening : Opening source} {head : LocalProduction opening}
      {tail : ProductionHistory opening.next (count + 1)}
      (transmits : ∀ formed, opening.next.assignment = (head.output formed).val)
      (rest : CommonTailAgreement tail) : CommonTailAgreement (.step opening head tail)

/-- Form the next assignment from this occurrence's stored action output.
The reference child's other fields remain fixed; using it as a common future
requires the exactness proof, rather than just an index on a history. -/
def transmittedState {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening) : CausalConstitutiveState :=
  { opening.next with assignment := (head.output formed).val }

theorem transmittedState_exact {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening)
    (agreement : opening.next.assignment = (head.output formed).val) :
    transmittedState head formed = opening.next := by
  unfold transmittedState
  rw [← agreement]

/-- Exact transport of the tail between its reference input state and the
state whose assignment was actually produced. Its two return laws come from
the proved equality of those states; a differing output cannot supply it. -/
def tailStateTransport {source : CausalConstitutiveState} {opening : Opening source}
    (head : LocalProduction opening) (formed : Identity opening)
    (agreement : opening.next.assignment = (head.output formed).val) (count : Nat) :
    RelationalFoundations.ExactTransport (ProductionHistory opening.next count)
      (ProductionHistory (transmittedState head formed) count) :=
  RelationalFoundations.ExactTransport.ofEquality (congrArg (fun state => ProductionHistory state count)
    (transmittedState_exact head formed agreement).symm)

def resumeCommonTail {source : CausalConstitutiveState} {count : Nat}
    {opening : Opening source} {head : LocalProduction opening}
    (tail : ProductionHistory opening.next count)
    (transmits : ∀ formed, opening.next.assignment = (head.output formed).val)
    (formed : Identity opening) : ProductionHistory (transmittedState head formed) count :=
  (tailStateTransport head formed (transmits formed) _).forward tail

theorem resumed_tail_returns {source : CausalConstitutiveState} {count : Nat}
    {opening : Opening source} {head : LocalProduction opening}
    (tail : ProductionHistory opening.next count)
    (transmits : ∀ formed, opening.next.assignment = (head.output formed).val)
    (formed : Identity opening) :
    (tailStateTransport head formed (transmits formed) _).backward
      (resumeCommonTail tail transmits formed) = tail :=
  (tailStateTransport head formed (transmits formed) _).forwardBackward tail

namespace MixedExample

def firstStoredEquality : DecidableEq (localImage (executeOpening first)) :=
  ProducedOutputImage.decEq (sourceCarrier first) (executeOpening first).output
    (fun p q => ((executeOpening first).output_exact p).trans
      ((first_converges p q).trans ((executeOpening first).output_exact q).symm))

def secondStoredEquality : DecidableEq (localImage (executeOpening second)) :=
  fun left right => match decEq (left.val.val 1) (right.val.val 1) with
  | isTrue same => isTrue (Subtype.ext (by
      rcases left.property with ⟨p, pe⟩
      rcases right.property with ⟨q, qe⟩
      have observed : (produced p).val 1 = (produced q).val 1 := by
        rw [← (executeOpening second).output_exact p, ← (executeOpening second).output_exact q,
          pe, qe]
        exact same
      exact pe.symm.trans (((executeOpening second).output_exact p).trans
        ((second_observable_faithful p q observed).trans
          (((executeOpening second).output_exact q).symm.trans qe)))))
  | isFalse different => isFalse (fun same => different (congrArg (fun value => value.val.val 1) same))

def comparisons : ImageComparisons production := .step firstStoredEquality (.step secondStoredEquality .nil)

def common_tail_agreement : CommonTailAgreement production :=
  .step (fun formed => (second_source_matches_each_first formed).trans
    (congrArg Subtype.val ((executeOpening first).output_exact formed).symm))
    (.terminal second (executeOpening second))

theorem first_transmits (formed : Identity first) :
    first.next.assignment = ((executeOpening first).output formed).val :=
  (second_source_matches_each_first formed).trans
    (congrArg Subtype.val ((executeOpening first).output_exact formed).symm)

def resumedSecond (formed : Identity first) :
    ProductionHistory (transmittedState (executeOpening first) formed) 1 :=
  resumeCommonTail (.step second (executeOpening second) (.nil second.next)) first_transmits formed

theorem resumed_second_returns (formed : Identity first) :
    (tailStateTransport (executeOpening first) formed (first_transmits formed) 1).backward
      (resumedSecond formed) = .step second (executeOpening second) (.nil second.next) :=
  resumed_tail_returns _ first_transmits formed

theorem composed_width : (composedRegime comparisons).frontier.length = 2 := rfl

theorem one_separating_step : separatingCount comparisons = 1 := rfl

/-- The separating terminal output cannot silently feed the same reference
future: the assignment at variable 1 already prevents that state agreement. -/
theorem separating_output_rejects_common_future :
    transmittedState (executeOpening second) (identity second false) ≠ second.next := by
  intro same
  have impossible := congrArg (fun state => state.assignment 1) same
  cases impossible

theorem composed_fibres_exact (p q : profiles.Identity) :
    (composedRegime comparisons).carry p = (composedRegime comparisons).carry q ↔
      production.output p = production.output q := composed_fibres comparisons p q

/-- In this example the justified common future gives the same fibres as the
full SAT continuation, not merely the ledger of intermediate output values. -/
theorem stored_outputs_iff_final (p q : profiles.Identity) :
    production.output p = production.output q ↔ finalOutput p = finalOutput q := by
  constructor
  · intro same
    exact congrArg (fun outputs : production.Target =>
      (generatedStructuralSplit initialState.operationalState first.selected first.fresh).merge
        (.inr outputs.2.1)) same
  · intro same
    have observed := congrArg (fun output => output.val 1) same
    rw [finalOutput_exact p, finalOutput_exact q] at observed
    have secondSame := second_observable_faithful p.2.1 q.2.1 observed
    change ((executeOpening first).output p.1, (executeOpening second).output p.2.1, ()) =
      ((executeOpening first).output q.1, (executeOpening second).output q.2.1, ())
    exact Prod.ext
      (((executeOpening first).output_exact p.1).trans
        ((first_converges p.1 q.1).trans ((executeOpening first).output_exact q.1).symm))
      (Prod.ext (((executeOpening second).output_exact p.2.1).trans
        (secondSame.trans ((executeOpening second).output_exact q.2.1).symm)) rfl)

theorem composed_final_fibres (p q : profiles.Identity) :
    (composedRegime comparisons).carry p = (composedRegime comparisons).carry q ↔
      finalOutput p = finalOutput q :=
  (composed_fibres_exact p q).trans (stored_outputs_iff_final p q)

end MixedExample
end ConstitutiveSearch.EndogenousDecomposition.VariableExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.productValue_carry
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.productValue_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.productCarry_surjective
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.fromOutputImage
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.outputTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.productEquality
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.imageFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.imageFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.composedRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.composed_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.composed_width_product
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.local_width_one_or_two
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.separatingCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.widthProduct_pow
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.composed_width_pow
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.CommonTailAgreement
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.transmittedState
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.transmittedState_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.tailStateTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.resumeCommonTail
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.resumed_tail_returns
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.comparisons
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.common_tail_agreement
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.first_transmits
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.resumedSecond
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.resumed_second_returns
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.composed_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.one_separating_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.separating_output_rejects_common_future
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.composed_fibres_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.stored_outputs_iff_final
#print axioms ConstitutiveSearch.EndogenousDecomposition.VariableExecution.MixedExample.composed_final_fibres
/- AXIOM_AUDIT_END -/
