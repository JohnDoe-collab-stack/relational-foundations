import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

/-!
# Constructive finite carriers, obligation regimes, and exact addressing

This module is deliberately independent of the SAT instance, role histories,
programs, and quantitative benchmark files. It proves the finite theorem that
will later be instantiated on the carrier derived from relational roles:

* a surjective obligation regime preserves source identities separately iff it
  has full source width;
* the same condition is equivalent to exact separately-addressable capacity,
  with addressing forced to factor through the regime's obligations.
-/

namespace ConstitutiveSearch
namespace Extensive

/-- Remove the first occurrence of a value using constructive decidable equality. -/
def removeFirst {α : Type} [DecidableEq α] (target : α) : List α → List α
  | [] => []
  | head :: tail =>
      if target = head then tail else head :: removeFirst target tail

/-- Removing another value preserves membership. -/
theorem removeFirst_preserves_other
    {α : Type} [DecidableEq α]
    (target value : α)
    (different : value ≠ target) :
    ∀ {values : List α}, value ∈ values → value ∈ removeFirst target values
  | _ :: tail, .head _ => by
      unfold removeFirst
      split
      next same => exact False.elim (different same.symm)
      next _ => exact .head _
  | head :: _, .tail _ prior => by
      unfold removeFirst
      split
      next same =>
        cases same
        exact prior
      next _ =>
        exact .tail _ (removeFirst_preserves_other target value different prior)

/-- Removing a value known to occur decreases length by exactly one. -/
theorem removeFirst_length_of_mem
    {α : Type} [DecidableEq α]
    (target : α) :
    ∀ {values : List α}, target ∈ values →
      (removeFirst target values).length + 1 = values.length
  | _ :: _, .head _ => by
      unfold removeFirst
      split
      · rfl
      · contradiction
  | head :: tail, .tail _ prior => by
      unfold removeFirst
      split
      · rfl
      · change (removeFirst target tail).length + 1 + 1 = tail.length + 1
        exact congrArg (fun length => length + 1)
          (removeFirst_length_of_mem target prior)

/-- Constructive duplicate-free subset bound for arbitrary decidable carriers. -/
theorem nodup_length_le_of_subset
    {α : Type} [DecidableEq α] :
    ∀ {left right : List α},
      left.Nodup → (left ⊆ right) → left.length ≤ right.length
  | [], _, .nil, _ => Nat.zero_le _
  | head :: tail, right, .cons headFresh tailNodup, contained => by
      have headMember : head ∈ right := contained (.head _)
      have tailContained : tail ⊆ removeFirst head right := by
        intro value valueMember
        exact removeFirst_preserves_other head value
          (fun same => headFresh value valueMember same.symm)
          (contained (.tail _ valueMember))
      have tailBound : tail.length ≤ (removeFirst head right).length :=
        nodup_length_le_of_subset tailNodup tailContained
      calc
        tail.length + 1 ≤ (removeFirst head right).length + 1 :=
          Nat.succ_le_succ tailBound
        _ = right.length := removeFirst_length_of_mem head headMember

/-- Descending constructive enumeration of naturals strictly below a bound. -/
def naturalsBelow : Nat → List Nat
  | 0 => []
  | bound + 1 => bound :: naturalsBelow bound

theorem naturalsBelow_complete (value : Nat) :
    ∀ {bound : Nat}, value < bound → value ∈ naturalsBelow bound
  | 0, before => False.elim (Nat.not_lt_zero value before)
  | _bound + 1, before =>
      match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with
      | .inl below => .tail _ (naturalsBelow_complete value below)
      | .inr same => same.symm ▸ .head _

theorem naturalsBelow_length :
    ∀ bound : Nat, (naturalsBelow bound).length = bound
  | 0 => rfl
  | bound + 1 => congrArg Nat.succ (naturalsBelow_length bound)

/-- Constructive length preservation for list maps. -/
theorem length_map {α β : Type} (map : α → β) :
    ∀ values : List α, (values.map map).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (length_map map tail)

/-- Constructively transport membership through a list map. -/
theorem mem_map {α β : Type} (map : α → β) {value : α} :
    ∀ {values : List α}, value ∈ values → map value ∈ values.map map
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (mem_map map prior)

/-- Recover a source witness from membership in a mapped list. -/
theorem mem_map_preimage {α β : Type} (map : α → β) {target : β} :
    ∀ {values : List α}, target ∈ values.map map →
      ∃ source, source ∈ values ∧ map source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, sourceMember, sourceExact⟩ := mem_map_preimage map prior
      ⟨source, .tail _ sourceMember, sourceExact⟩

/-- Injective maps preserve duplicate-freeness constructively. -/
theorem nodup_map
    {α β : Type}
    (map : α → β)
    (injective : Function.Injective map) :
    ∀ {values : List α}, values.Nodup → (values.map map).Nodup
  | [], .nil => .nil
  | _head :: _, .cons headFresh tailNodup =>
      .cons
        (fun _mapped mappedMember same =>
          let ⟨source, sourceMember, sourceExact⟩ :=
            mem_map_preimage map mappedMember
          headFresh source sourceMember
            (injective (Eq.trans same sourceExact.symm)))
        (nodup_map map injective tailNodup)

/-- A finite carrier whose enumeration is complete and duplicate-free. -/
structure FiniteCarrier where
  Identity : Type
  decEq : DecidableEq Identity
  frontier : List Identity
  complete : (identity : Identity) → identity ∈ frontier
  nodup : frontier.Nodup

namespace FiniteCarrier

/-- Width is read from the complete duplicate-free frontier. -/
def width (carrier : FiniteCarrier) : Nat :=
  carrier.frontier.length

end FiniteCarrier

/-- A surjective operational regime over already constituted source identities. -/
structure ObligationRegime (source : FiniteCarrier) where
  Obligation : Type
  decEq : DecidableEq Obligation
  frontier : List Obligation
  complete : (obligation : Obligation) → obligation ∈ frontier
  nodup : frontier.Nodup
  carry : source.Identity → Obligation
  carry_surjective :
    (obligation : Obligation) → ∃ identity, carry identity = obligation

namespace ObligationRegime

/-- The finite carrier of obligations induced by a regime. -/
def asFiniteCarrier
    {source : FiniteCarrier}
    (regime : ObligationRegime source) : FiniteCarrier :=
  { Identity := regime.Obligation
    decEq := regime.decEq
    frontier := regime.frontier
    complete := regime.complete
    nodup := regime.nodup }

/-- The regime has full extensive width exactly when it has source width. -/
def HasFullExtensiveWidth
    {source : FiniteCarrier}
    (regime : ObligationRegime source) : Prop :=
  regime.frontier.length = source.frontier.length

end ObligationRegime

/--
The identity regime is a positive witness that the full-width side is
inhabited for every finite source.  It does not reconstruct identities from a
cardinality: it carries each already constituted identity as itself.
-/
def identityObligationRegime
    (source : FiniteCarrier) : ObligationRegime source :=
  { Obligation := source.Identity
    decEq := source.decEq
    frontier := source.frontier
    complete := source.complete
    nodup := source.nodup
    carry := id
    carry_surjective := fun identity => ⟨identity, rfl⟩ }

/-- The identity regime has exactly the source width. -/
theorem identityObligationRegime_fullWidth
    (source : FiniteCarrier) :
    (identityObligationRegime source).HasFullExtensiveWidth :=
  rfl

/-- The regime carries distinct constituted identities to distinct obligations. -/
def PreservesIdentitiesSeparately
    {source : FiniteCarrier}
    (regime : ObligationRegime source) : Prop :=
  Function.Injective regime.carry

/-- The identity regime preserves constituted identities definitionally. -/
theorem identityObligationRegime_preserves
    (source : FiniteCarrier) :
    PreservesIdentitiesSeparately (identityObligationRegime source) := by
  intro left right same
  exact same

/-- Surjectivity alone bounds obligation width by source width. -/
theorem regime_width_le_source_width
    {source : FiniteCarrier}
    (regime : ObligationRegime source) :
    regime.frontier.length ≤ source.frontier.length := by
  letI : DecidableEq source.Identity := source.decEq
  letI : DecidableEq regime.Obligation := regime.decEq
  let image := source.frontier.map regime.carry
  have targetContained : regime.frontier ⊆ image := by
    intro obligation _member
    rcases regime.carry_surjective obligation with ⟨identity, carried⟩
    have sourceMember := source.complete identity
    have imageMember : regime.carry identity ∈ image :=
      mem_map regime.carry sourceMember
    exact carried ▸ imageMember
  have bound := nodup_length_le_of_subset regime.nodup targetContained
  rw [length_map regime.carry source.frontier] at bound
  exact bound

/-- Injective carrying bounds source width by obligation width. -/
theorem source_width_le_regime_width_of_preserves
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (preserves : PreservesIdentitiesSeparately regime) :
    source.frontier.length ≤ regime.frontier.length := by
  letI : DecidableEq source.Identity := source.decEq
  letI : DecidableEq regime.Obligation := regime.decEq
  let image := source.frontier.map regime.carry
  have imageNodup : image.Nodup :=
    nodup_map
      regime.carry
      (fun {_left _right} same => preserves same)
      source.nodup
  have imageContained : image ⊆ regime.frontier := by
    intro obligation _member
    exact regime.complete obligation
  have bound := nodup_length_le_of_subset imageNodup imageContained
  rw [length_map regime.carry source.frontier] at bound
  exact bound

/-- Separate preservation gives exact full width. -/
theorem full_width_of_preserves
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (preserves : PreservesIdentitiesSeparately regime) :
    regime.HasFullExtensiveWidth := by
  unfold ObligationRegime.HasFullExtensiveWidth
  exact Nat.le_antisymm
    (regime_width_le_source_width regime)
    (source_width_le_regime_width_of_preserves regime preserves)

/-- A surjective full-width regime must preserve every source identity separately. -/
theorem preserves_of_full_width
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (fullWidth : regime.HasFullExtensiveWidth) :
    PreservesIdentitiesSeparately regime := by
  letI : DecidableEq source.Identity := source.decEq
  letI : DecidableEq regime.Obligation := regime.decEq
  intro left right carriedExact
  by_cases same : left = right
  · exact same
  · let withoutLeft := removeFirst left source.frontier
    let image := withoutLeft.map regime.carry
    have rightMember : right ∈ withoutLeft :=
      removeFirst_preserves_other left right (fun rightLeft => same rightLeft.symm)
        (source.complete right)
    have targetContained : regime.frontier ⊆ image := by
      intro obligation _member
      rcases regime.carry_surjective obligation with ⟨identity, identityCarries⟩
      by_cases identityLeft : identity = left
      · have replacement : regime.carry right = obligation := by
          exact Eq.trans carriedExact.symm (identityLeft ▸ identityCarries)
        have mapped : regime.carry right ∈ image :=
          mem_map regime.carry rightMember
        exact replacement ▸ mapped
      · have identityMember : identity ∈ withoutLeft :=
          removeFirst_preserves_other left identity identityLeft
            (source.complete identity)
        have mapped : regime.carry identity ∈ image :=
          mem_map regime.carry identityMember
        exact identityCarries ▸ mapped
    have targetBound : regime.frontier.length ≤ image.length :=
      nodup_length_le_of_subset regime.nodup targetContained
    have imageLength : image.length = withoutLeft.length :=
      length_map regime.carry withoutLeft
    have removedLength : withoutLeft.length + 1 = source.frontier.length :=
      removeFirst_length_of_mem left (source.complete left)
    have impossible : withoutLeft.length + 1 ≤ withoutLeft.length := by
      calc
        withoutLeft.length + 1 = source.frontier.length := removedLength
        _ = regime.frontier.length := fullWidth.symm
        _ ≤ image.length := targetBound
        _ = withoutLeft.length := imageLength
    exact False.elim
      ((Nat.not_le_of_gt (Nat.lt_succ_self withoutLeft.length)) impossible)

/-- General finite theorem: full width is exactly separate preservation. -/
theorem preservesIdentitiesSeparately_iff_fullWidth
    {source : FiniteCarrier}
    (regime : ObligationRegime source) :
    PreservesIdentitiesSeparately regime ↔
      regime.HasFullExtensiveWidth :=
  ⟨full_width_of_preserves regime, preserves_of_full_width regime⟩

/--
The first index of a value is computed from the list itself.  The empty-list
case is a total default; completeness below proves that this default is never
used for a carrier identity.
-/
def firstIndexOf
    {α : Type} [DecidableEq α]
    (target : α) : List α → Nat
  | [] => 0
  | head :: tail =>
      if target = head then 0 else firstIndexOf target tail + 1

/-- A computed first index is in range whenever the value occurs. -/
theorem firstIndexOf_lt_of_mem
    {α : Type} [DecidableEq α]
    (target : α) :
    ∀ {values : List α}, target ∈ values →
      firstIndexOf target values < values.length
  | head :: tail, member => by
      unfold firstIndexOf
      split
      · exact Nat.zero_lt_succ tail.length
      · next different =>
          have tailMember : target ∈ tail := by
            rcases Constructive.list_mem_cons_cases member with same | prior
            · exact False.elim (different same)
            · exact prior
          exact Nat.succ_lt_succ
            (firstIndexOf_lt_of_mem target tailMember)

/-- Equal computed positions of two members force equality of the members. -/
theorem firstIndexOf_injective_on_members
    {α : Type} [DecidableEq α] :
    ∀ {values : List α} {left right : α},
      left ∈ values →
      right ∈ values →
      firstIndexOf left values = firstIndexOf right values →
      left = right
  | [], _, _, leftMember, _, _ => by
      cases leftMember
  | head :: tail, left, right, leftMember, rightMember, sameIndex => by
      by_cases leftHead : left = head
      · by_cases rightHead : right = head
        · exact Eq.trans leftHead rightHead.symm
        · rw [firstIndexOf, if_pos leftHead, firstIndexOf, if_neg rightHead]
            at sameIndex
          exact False.elim (Nat.noConfusion sameIndex)
      · by_cases rightHead : right = head
        · rw [firstIndexOf, if_neg leftHead, firstIndexOf, if_pos rightHead]
            at sameIndex
          exact False.elim (Nat.noConfusion sameIndex)
        · have leftTail : left ∈ tail := by
            rcases Constructive.list_mem_cons_cases leftMember with same | prior
            · exact False.elim (leftHead same)
            · exact prior
          have rightTail : right ∈ tail := by
            rcases Constructive.list_mem_cons_cases rightMember with same | prior
            · exact False.elim (rightHead same)
            · exact prior
          rw [firstIndexOf, if_neg leftHead, firstIndexOf, if_neg rightHead]
            at sameIndex
          exact firstIndexOf_injective_on_members
            leftTail rightTail (Nat.succ.inj sameIndex)

/-- An address space that keeps all carrier identities separately recoverable. -/
structure SeparateAddressingAt
    (carrier : FiniteCarrier)
    (slotCount : Nat) where
  address : carrier.Identity → Fin slotCount
  injective : Function.Injective address

/-- A width bound constructively produces a separate addressing. -/
def separateAddressingOfWidthLe
    (carrier : FiniteCarrier)
    (slotCount : Nat)
    (bound : carrier.frontier.length ≤ slotCount) :
    SeparateAddressingAt carrier slotCount where
  address identity :=
    letI : DecidableEq carrier.Identity := carrier.decEq
    ⟨firstIndexOf identity carrier.frontier,
      Nat.lt_of_lt_of_le
        (firstIndexOf_lt_of_mem identity (carrier.complete identity))
        bound⟩
  injective := by
    letI : DecidableEq carrier.Identity := carrier.decEq
    intro left right sameAddress
    have indexValues :
        firstIndexOf left carrier.frontier =
          firstIndexOf right carrier.frontier :=
      congrArg (fun index : Fin slotCount => index.val) sameAddress
    exact firstIndexOf_injective_on_members
      (carrier.complete left)
      (carrier.complete right)
      indexValues

/-- Any separate addressing needs at least the complete frontier width. -/
theorem widthLeOfSeparateAddressing
    {carrier : FiniteCarrier}
    {slotCount : Nat}
    (addressing : SeparateAddressingAt carrier slotCount) :
    carrier.frontier.length ≤ slotCount := by
  letI : DecidableEq carrier.Identity := carrier.decEq
  let addressed := carrier.frontier.map (fun identity => (addressing.address identity).val)
  have addressedNodup : addressed.Nodup :=
    nodup_map
      (fun identity => (addressing.address identity).val)
      (fun {_left _right} same => addressing.injective (Fin.ext same))
      carrier.nodup
  have contained : addressed ⊆ naturalsBelow slotCount := by
    intro value member
    rcases mem_map_preimage
      (fun identity => (addressing.address identity).val) member with
      ⟨identity, _identityMember, valueExact⟩
    rw [← valueExact]
    exact naturalsBelow_complete _ (addressing.address identity).isLt
  have bound := nodup_length_le_of_subset addressedNodup contained
  rw [naturalsBelow_length slotCount] at bound
  rw [length_map
    (fun identity => (addressing.address identity).val) carrier.frontier] at bound
  exact bound

/-- Exact constructive characterization of finite separate addressing. -/
theorem separateAddressing_iff_widthLe
    (carrier : FiniteCarrier)
    (slotCount : Nat) :
    Nonempty (SeparateAddressingAt carrier slotCount) ↔
      carrier.frontier.length ≤ slotCount :=
  ⟨fun witness =>
      match witness with
      | ⟨addressing⟩ => widthLeOfSeparateAddressing addressing,
    fun bound => ⟨separateAddressingOfWidthLe carrier slotCount bound⟩⟩

/-- Exact minimum capacity with both a witness and its universal lower bound. -/
structure ExactMinimumAddressingCapacity
    (carrier : FiniteCarrier)
    (minimum : Nat) where
  attained : SeparateAddressingAt carrier minimum
  minimal :
    (slotCount : Nat) →
      SeparateAddressingAt carrier slotCount → minimum ≤ slotCount

/-- Every finite carrier is exactly separately addressable at its own width. -/
def exactMinimumAddressingCapacity
    (carrier : FiniteCarrier) :
    ExactMinimumAddressingCapacity carrier carrier.frontier.length :=
  { attained :=
      separateAddressingOfWidthLe carrier carrier.frontier.length
        (Nat.le_refl _)
    minimal := fun _slotCount addressing =>
      widthLeOfSeparateAddressing addressing }

/-- Addressing of source identities that is forced to pass through obligations. -/
structure RegimeSeparateAddressingAt
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (slotCount : Nat) where
  addressObligation : regime.Obligation → Fin slotCount
  separatesCarriedIdentities :
    Function.Injective (fun identity => addressObligation (regime.carry identity))

/--
The regime keeps the already constituted source identities distinct and gives
them separate addresses through its own obligation carrier.  The factorization
condition rules out an address assigned directly behind the regime's back.
-/
structure ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
    {source : FiniteCarrier}
    (regime : ObligationRegime source) : Prop where
  preservesDistinctIdentities : PreservesIdentitiesSeparately regime
  separatelyAddressableThroughRegime :
    Nonempty (RegimeSeparateAddressingAt regime source.frontier.length)

/-- Exact minimum factorized capacity of one obligation regime. -/
structure ExactRegimeSeparateCapacity
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (minimum : Nat) where
  attained : RegimeSeparateAddressingAt regime minimum
  minimal :
    (slotCount : Nat) →
      RegimeSeparateAddressingAt regime slotCount → minimum ≤ slotCount

/-- Factorized addressing itself forces the regime's carry map to be injective. -/
theorem preserves_of_regimeAddressing
    {source : FiniteCarrier}
    {regime : ObligationRegime source}
    {slotCount : Nat}
    (addressing : RegimeSeparateAddressingAt regime slotCount) :
    PreservesIdentitiesSeparately regime := by
  intro left right carriedExact
  apply addressing.separatesCarriedIdentities
  exact congrArg addressing.addressObligation carriedExact

/-- Separate preservation constructs exact source-width capacity through the regime. -/
def exactRegimeCapacityOfPreserves
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (preserves : PreservesIdentitiesSeparately regime) :
    ExactRegimeSeparateCapacity regime source.frontier.length :=
  let obligationAddressing :=
    separateAddressingOfWidthLe
      regime.asFiniteCarrier
      source.frontier.length
      (regime_width_le_source_width regime)
  { attained :=
      { addressObligation := obligationAddressing.address
        separatesCarriedIdentities := by
          intro left right same
          exact preserves (obligationAddressing.injective same) }
    minimal := fun _slotCount addressing =>
      widthLeOfSeparateAddressing
        { address := fun identity =>
            addressing.addressObligation (regime.carry identity)
          injective := addressing.separatesCarriedIdentities } }

/-- Separate preservation positively supplies the factorized addressing. -/
theorem conservationOfPreserves
    {source : FiniteCarrier}
    (regime : ObligationRegime source)
    (preserves : PreservesIdentitiesSeparately regime) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably regime :=
  { preservesDistinctIdentities := preserves
    separatelyAddressableThroughRegime :=
      ⟨(exactRegimeCapacityOfPreserves regime preserves).attained⟩ }

/--
The positive full-width regime really satisfies the complete conservation
condition, including addressing factorized through its obligation carrier.
-/
theorem identityObligationRegime_conserves
    (source : FiniteCarrier) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (identityObligationRegime source) :=
  conservationOfPreserves
    (identityObligationRegime source)
    (identityObligationRegime_preserves source)

/-- The explicit conservation certificate has exactly the injective content. -/
theorem preservesIdentitiesSeparately_iff_distinctSeparateConservation
    {source : FiniteCarrier}
    (regime : ObligationRegime source) :
    PreservesIdentitiesSeparately regime ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably regime :=
  ⟨conservationOfPreserves regime,
    fun conservation => conservation.preservesDistinctIdentities⟩

/-- Exact factorized capacity recovers separate preservation. -/
theorem preserves_of_exactRegimeCapacity
    {source : FiniteCarrier}
    {regime : ObligationRegime source}
    {minimum : Nat}
    (capacity : ExactRegimeSeparateCapacity regime minimum) :
    PreservesIdentitiesSeparately regime :=
  preserves_of_regimeAddressing capacity.attained

/--
Central capacity theorem: for any surjective finite regime, preserving the
constituted identities separately is equivalent to exact source-width
addressability through that regime.
-/
theorem preservesIdentitiesSeparately_iff_exactRegimeCapacity
    {source : FiniteCarrier}
    (regime : ObligationRegime source) :
    PreservesIdentitiesSeparately regime ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime source.frontier.length) :=
  ⟨fun preserves => ⟨exactRegimeCapacityOfPreserves regime preserves⟩,
    fun witness =>
      match witness with
      | ⟨capacity⟩ => preserves_of_exactRegimeCapacity capacity⟩

end Extensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Extensive.FiniteCarrier
#print axioms ConstitutiveSearch.Extensive.ObligationRegime
#print axioms ConstitutiveSearch.Extensive.identityObligationRegime
#print axioms ConstitutiveSearch.Extensive.identityObligationRegime_fullWidth
#print axioms ConstitutiveSearch.Extensive.PreservesIdentitiesSeparately
#print axioms ConstitutiveSearch.Extensive.identityObligationRegime_preserves
#print axioms ConstitutiveSearch.Extensive.regime_width_le_source_width
#print axioms ConstitutiveSearch.Extensive.source_width_le_regime_width_of_preserves
#print axioms ConstitutiveSearch.Extensive.preservesIdentitiesSeparately_iff_fullWidth
#print axioms ConstitutiveSearch.Extensive.firstIndexOf
#print axioms ConstitutiveSearch.Extensive.firstIndexOf_lt_of_mem
#print axioms ConstitutiveSearch.Extensive.firstIndexOf_injective_on_members
#print axioms ConstitutiveSearch.Extensive.SeparateAddressingAt
#print axioms ConstitutiveSearch.Extensive.separateAddressingOfWidthLe
#print axioms ConstitutiveSearch.Extensive.widthLeOfSeparateAddressing
#print axioms ConstitutiveSearch.Extensive.separateAddressing_iff_widthLe
#print axioms ConstitutiveSearch.Extensive.ExactMinimumAddressingCapacity
#print axioms ConstitutiveSearch.Extensive.exactMinimumAddressingCapacity
#print axioms ConstitutiveSearch.Extensive.RegimeSeparateAddressingAt
#print axioms ConstitutiveSearch.Extensive.ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
#print axioms ConstitutiveSearch.Extensive.identityObligationRegime_conserves
#print axioms ConstitutiveSearch.Extensive.ExactRegimeSeparateCapacity
#print axioms ConstitutiveSearch.Extensive.exactRegimeCapacityOfPreserves
#print axioms ConstitutiveSearch.Extensive.conservationOfPreserves
#print axioms ConstitutiveSearch.Extensive.preservesIdentitiesSeparately_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.Extensive.preservesIdentitiesSeparately_iff_exactRegimeCapacity
/- AXIOM_AUDIT_END -/
