import RelationalPerimeter.Computation.ConstitutiveSearch.FiniteExtensiveAddressing

/-!
# Exact finite images of operational targets

This module constructs the operational carrier as the duplicate-free image of
an actually supplied target map.  It does not prescribe a width.  In
particular, width one is equivalent, for a nonempty finite source, to the
convergence of all produced targets.
-/

namespace ConstitutiveSearch
namespace Extensive

/-- Constructive membership test with an explicit equality decision. -/
def containsWith
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) : List α → Bool
  | [] => false
  | head :: tail =>
      match decideEq value head with
      | isTrue _ => true
      | isFalse _ => containsWith decideEq value tail

theorem containsWith_eq_true_iff_mem
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) :
    ∀ values : List α, containsWith decideEq value values = true ↔ value ∈ values
  | [] => by
      constructor <;> intro impossible <;> cases impossible
  | head :: tail => by
      unfold containsWith
      cases same : decideEq value head with
      | isTrue equal =>
          constructor
          · intro _
            exact equal ▸ .head _
          · intro _
            rfl
      | isFalse different =>
          constructor
          · intro found
            exact .tail _ ((containsWith_eq_true_iff_mem decideEq value tail).mp found)
          · intro member
            cases member with
            | head _ => exact False.elim (different rfl)
            | tail _ tailMember =>
                exact (containsWith_eq_true_iff_mem decideEq value tail).mpr tailMember

/-- Constructive duplicate removal, preserving the last occurrence. -/
def deduplicate
    {α : Type}
    (decideEq : DecidableEq α) : List α → List α
  | [] => []
  | head :: tail =>
      let reducedTail := deduplicate decideEq tail
      if containsWith decideEq head reducedTail then
        reducedTail
      else
        head :: reducedTail

/-- Duplicate removal preserves and reflects membership. -/
theorem mem_deduplicate_iff
    {α : Type}
    (decideEq : DecidableEq α)
    (value : α) :
    ∀ values : List α,
      value ∈ deduplicate decideEq values ↔ value ∈ values
  | [] => Iff.rfl
  | head :: tail => by
      change
        value ∈
            (if containsWith decideEq head (deduplicate decideEq tail) then
              deduplicate decideEq tail
            else
              head :: deduplicate decideEq tail) ↔
          value ∈ head :: tail
      cases repeated :
          containsWith decideEq head (deduplicate decideEq tail) with
      | true =>
        rw [if_pos rfl]
        have headRepeated : head ∈ deduplicate decideEq tail :=
          (containsWith_eq_true_iff_mem decideEq head _).mp repeated
        constructor
        · intro reducedMember
          exact .tail _
            ((mem_deduplicate_iff decideEq value tail).mp reducedMember)
        · intro sourceMember
          cases sourceMember with
          | head _ => exact headRepeated
          | tail _ tailMember =>
              exact (mem_deduplicate_iff decideEq value tail).mpr tailMember
      | false =>
        rw [if_neg Bool.false_ne_true]
        constructor
        · intro reducedMember
          cases reducedMember with
          | head _ => exact .head _
          | tail _ tailMember =>
              exact .tail _
                ((mem_deduplicate_iff decideEq value tail).mp tailMember)
        · intro sourceMember
          cases sourceMember with
          | head _ => exact .head _
          | tail _ tailMember =>
              exact .tail _
                ((mem_deduplicate_iff decideEq value tail).mpr tailMember)

/-- Duplicate removal produces a duplicate-free list. -/
theorem deduplicate_nodup
    {α : Type}
    (decideEq : DecidableEq α) :
    ∀ values : List α, (deduplicate decideEq values).Nodup
  | [] => .nil
  | head :: tail => by
      change
        (if containsWith decideEq head (deduplicate decideEq tail) then
          deduplicate decideEq tail
        else
          head :: deduplicate decideEq tail).Nodup
      cases repeated :
          containsWith decideEq head (deduplicate decideEq tail) with
      | true =>
          rw [if_pos rfl]
          exact deduplicate_nodup decideEq tail
      | false =>
          rw [if_neg Bool.false_ne_true]
          exact .cons
            (fun value member same => by
              have headMember : head ∈ deduplicate decideEq tail :=
                same ▸ member
              have found :=
                (containsWith_eq_true_iff_mem decideEq head _).mpr headMember
              rw [repeated] at found
              exact Bool.noConfusion found)
            (deduplicate_nodup decideEq tail)

/-- If a nonempty list has only one value, its duplicate-free image is a singleton. -/
theorem deduplicate_eq_singleton_of_nonempty_of_all_eq
    {α : Type}
    (decideEq : DecidableEq α)
    (values : List α)
    (anchor : α)
    (nonempty : values ≠ [])
    (allEqual : (value : α) → value ∈ values → value = anchor) :
    deduplicate decideEq values = [anchor] := by
  induction values with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail inductionHypothesis =>
      have headExact : head = anchor := allEqual head (.head _)
      cases tail with
      | nil =>
          cases headExact
          rfl
      | cons tailHead tailTail =>
          have tailNonempty : tailHead :: tailTail ≠ [] := by
            intro impossible
            cases impossible
          have tailAllEqual :
              (value : α) → value ∈ tailHead :: tailTail → value = anchor :=
            fun value member => allEqual value (.tail _ member)
          have tailExact :
              deduplicate decideEq (tailHead :: tailTail) = [anchor] :=
            inductionHypothesis tailNonempty tailAllEqual
          change
            (if containsWith decideEq head
                (deduplicate decideEq (tailHead :: tailTail)) then
              deduplicate decideEq (tailHead :: tailTail)
            else
              head :: deduplicate decideEq (tailHead :: tailTail)) = [anchor]
          rw [tailExact, headExact]
          have contained : containsWith decideEq anchor [anchor] = true := by
            unfold containsWith
            cases same : decideEq anchor anchor with
            | isTrue _ => rfl
            | isFalse different => exact False.elim (different rfl)
          rw [contained]
          rw [if_pos rfl]

theorem containsWith_singleton_eq
    {α : Type}
    (decideEq : DecidableEq α)
    (value head : α) :
    containsWith decideEq value [head] = true → value = head := by
  intro found
  cases decision : decideEq value head with
  | isTrue same => exact same
  | isFalse _ =>
      have computed : containsWith decideEq value [head] = false := by
        unfold containsWith
        rw [decision]
        rfl
      exact False.elim (Bool.noConfusion (Eq.trans computed.symm found))

theorem list_ne_nil_of_mem
    {α : Type} {value : α} {values : List α}
    (member : value ∈ values) : values ≠ [] := by
  intro empty
  cases empty
  exact nomatch member

theorem map_ne_nil
    {α β : Type}
    (map : α → β) :
    ∀ {values : List α}, values ≠ [] → values.map map ≠ []
  | [], nonempty => False.elim (nonempty rfl)
  | _ :: _, _ => fun impossible => nomatch impossible

/-- Duplicate-free image of a target map over a complete finite source. -/
def exactTargetImageFrontier
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) : List Target := by
  letI : DecidableEq Target := targetDecEq
  exact deduplicate targetDecEq (source.frontier.map target)

theorem exactTargetImageFrontier_complete
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (identity : source.Identity) :
    target identity ∈ exactTargetImageFrontier source targetDecEq target := by
  letI : DecidableEq Target := targetDecEq
  exact (mem_deduplicate_iff targetDecEq (target identity) _).mpr
    (Extensive.mem_map target (source.complete identity))

theorem exactTargetImageFrontier_nodup
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) :
    (exactTargetImageFrontier source targetDecEq target).Nodup := by
  letI : DecidableEq Target := targetDecEq
  exact deduplicate_nodup targetDecEq _

/-!
## Direct computed image regime

The obligation carrier below is obtained directly from the duplicate-free
image computed from the target map.  No singleton carrier and no width are
supplied independently of that computation.
-/

/-- Attach each finite-image value to its constituting membership. -/
def attachImageMembers {α : Type} :
    (values : List α) → List {value : α // value ∈ values}
  | [] => []
  | head :: tail =>
      ⟨head, .head tail⟩ ::
        (attachImageMembers tail).map fun value =>
          ⟨value.1, .tail head value.2⟩

theorem attachImageMembers_complete {α : Type} :
    (values : List α) →
      (value : {value : α // value ∈ values}) →
      value ∈ attachImageMembers values
  | [], ⟨_, impossible⟩ => nomatch impossible
  | head :: tail, ⟨value, member⟩ => by
      cases member with
      | head => exact .head _
      | tail _ prior =>
          let lift : {value : α // value ∈ tail} →
              {value : α // value ∈ head :: tail} :=
            fun attached => ⟨attached.1, .tail head attached.2⟩
          let attached : {value : α // value ∈ tail} := ⟨value, prior⟩
          have mapped : lift attached ∈
              (attachImageMembers tail).map lift :=
            Extensive.mem_map lift
              (attachImageMembers_complete tail attached)
          have exactValue :
              lift attached =
                (⟨value, .tail head prior⟩ :
                  {value : α // value ∈ head :: tail}) :=
            Subtype.ext rfl
          exact .tail _ (exactValue ▸ mapped)

theorem attachImageMembers_length {α : Type} :
    (values : List α) →
      (attachImageMembers values).length = values.length
  | [] => rfl
  | _ :: tail => by
      unfold attachImageMembers
      exact congrArg Nat.succ
        (Eq.trans (Extensive.length_map _ (attachImageMembers tail))
          (attachImageMembers_length tail))

theorem attachImageMembers_nodup
    {α : Type}
    (values : List α)
    (nodup : values.Nodup) :
    (attachImageMembers values).Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      cases nodup with
      | cons headFresh tailNodup =>
          let lift : {value : α // value ∈ tail} →
              {value : α // value ∈ head :: tail} :=
            fun value => ⟨value.1, .tail head value.2⟩
          have liftInjective : Function.Injective lift := by
            intro left right same
            apply Subtype.ext
            exact congrArg
              (fun value : {value : α // value ∈ head :: tail} => value.1)
              same
          change
            (⟨head, .head tail⟩ ::
              (attachImageMembers tail).map lift).Nodup
          exact .cons
            (fun mapped mappedMember same =>
              let ⟨(prior : {value : α // value ∈ tail}),
                    _priorMember, priorExact⟩ :=
                Extensive.mem_map_preimage lift mappedMember
              headFresh prior.1 prior.2
                (congrArg Subtype.val
                  (Eq.trans same priorExact.symm)))
            (Extensive.nodup_map lift liftInjective
              (inductionHypothesis tailNodup))

/-- Equality of image identities is equality of their computed target values. -/
def targetImageIdentityDecEq
    {source : FiniteCarrier}
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) :
    DecidableEq
      {value : Target //
        value ∈ exactTargetImageFrontier source targetDecEq target} :=
  fun left right =>
    match targetDecEq left.1 right.1 with
    | isTrue same => isTrue (Subtype.ext same)
    | isFalse different =>
        isFalse (fun equal => different (congrArg Subtype.val equal))

/-- The obligation regime is exactly the computed image of `target`. -/
def computedTargetImageRegime
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) :
    ObligationRegime source := by
  let image := exactTargetImageFrontier source targetDecEq target
  exact
    { Obligation := {value : Target // value ∈ image}
      decEq := targetImageIdentityDecEq targetDecEq target
      frontier := attachImageMembers image
      complete := attachImageMembers_complete image
      nodup := attachImageMembers_nodup image
        (exactTargetImageFrontier_nodup source targetDecEq target)
      carry := fun identity =>
        ⟨target identity,
          exactTargetImageFrontier_complete source targetDecEq target identity⟩
      carry_surjective := fun obligation => by
        have rawMember : obligation.1 ∈ source.frontier.map target :=
          (mem_deduplicate_iff targetDecEq obligation.1 _).mp obligation.2
        let ⟨identity, _identityMember, targetExact⟩ :=
          Extensive.mem_map_preimage target rawMember
        exact ⟨identity, Subtype.ext targetExact⟩ }

/-- The computed image regime has exactly the fibres of the computation. -/
theorem computedTargetImageRegime_carry_eq_iff_target_eq
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (left right : source.Identity) :
    (computedTargetImageRegime source targetDecEq target).carry left =
        (computedTargetImageRegime source targetDecEq target).carry right ↔
      target left = target right := by
  constructor
  · intro same
    exact congrArg Subtype.val same
  · intro same
    exact Subtype.ext same

/-- The regime width is the computed target-image width. -/
theorem computedTargetImageRegime_width_eq_image_width
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target) :
    (computedTargetImageRegime source targetDecEq target).frontier.length =
      (exactTargetImageFrontier source targetDecEq target).length :=
  attachImageMembers_length _

/-- Convergent computed targets produce the singleton image at their anchor. -/
theorem exactTargetImage_eq_singleton_of_all_targets_equal
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right) :
    exactTargetImageFrontier source targetDecEq target = [target anchor] := by
  have sourceNonempty : source.frontier ≠ [] :=
    list_ne_nil_of_mem (source.complete anchor)
  have mappedNonempty : source.frontier.map target ≠ [] :=
    map_ne_nil target sourceNonempty
  have allMappedEqual :
      (value : Target) → value ∈ source.frontier.map target →
        value = target anchor := by
    intro value member
    let ⟨identity, _identityMember, valueExact⟩ :=
      Extensive.mem_map_preimage target member
    exact Eq.trans valueExact.symm (targetsConverge identity anchor)
  exact deduplicate_eq_singleton_of_nonempty_of_all_eq
    targetDecEq (source.frontier.map target) (target anchor)
    mappedNonempty allMappedEqual

/-- Width one is derived from convergence of the computed image. -/
theorem computedTargetImageRegime_width_one_of_all_targets_equal
    (source : FiniteCarrier)
    {Target : Type}
    (targetDecEq : DecidableEq Target)
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right) :
    (computedTargetImageRegime source targetDecEq target).frontier.length = 1 := by
  rw [computedTargetImageRegime_width_eq_image_width]
  rw [exactTargetImage_eq_singleton_of_all_targets_equal
    source targetDecEq target anchor targetsConverge]
  rfl

/-!
## Exact convergent image without decidable equality on the target carrier

Some operational targets contain functions and proof-relevant continuations,
so their ambient carrier has no constructive `DecidableEq`.  When execution
itself proves that every produced target converges to the target of one source,
the following carrier retains the actual produced target value together with
that convergence proof.  It is not `Unit`, and its carry map stores
`target identity` rather than discarding the computation.
-/

/-- A target value in the execution-proved fibre of the chosen anchor. -/
def ConvergedTargetObligation
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity) : Type :=
  {value : Target // value = target anchor}

/-- Equality is constructive because both values are proved equal to the
execution-produced anchor target. -/
def convergedTargetObligationDecEq
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity) :
    DecidableEq (ConvergedTargetObligation source target anchor) :=
  fun left right =>
    isTrue (Subtype.ext (Eq.trans left.2 right.2.symm))

/--
The exact operational regime produced by a target map and its convergence
proof.  Every carried obligation retains the actual target value computed for
its source; convergence supplies only the proof that it belongs to the common
executed fibre.
-/
def convergedTargetImageRegime
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right) :
    ObligationRegime source :=
  let anchorObligation : ConvergedTargetObligation source target anchor :=
    ⟨target anchor, rfl⟩
  { Obligation := ConvergedTargetObligation source target anchor
    decEq := convergedTargetObligationDecEq source target anchor
    frontier := [anchorObligation]
    complete := fun obligation => by
      have same : obligation = anchorObligation :=
        Subtype.ext obligation.2
      exact same ▸ .head []
    nodup := .cons (fun _ member _ => nomatch member) .nil
    carry := fun identity =>
      ⟨target identity, targetsConverge identity anchor⟩
    carry_surjective := fun obligation =>
      ⟨anchor, Subtype.ext obligation.2.symm⟩ }

/-- The carried value is definitionally the target produced for its source. -/
theorem convergedTargetImageRegime_carry_value
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right)
    (identity : source.Identity) :
    ((convergedTargetImageRegime source target anchor targetsConverge).carry
      identity).1 = target identity :=
  rfl

/-- Obligation equality has exactly the fibres of the produced target map. -/
theorem convergedTargetImageRegime_carry_eq_iff_target_eq
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right)
    (left right : source.Identity) :
    (convergedTargetImageRegime source target anchor targetsConverge).carry left =
        (convergedTargetImageRegime source target anchor targetsConverge).carry right ↔
      target left = target right := by
  constructor
  · intro same
    exact congrArg Subtype.val same
  · intro same
    exact Subtype.ext same

/-- Its width is one only after an executed convergence proof is supplied. -/
theorem convergedTargetImageRegime_width_exact
    (source : FiniteCarrier)
    {Target : Type}
    (target : source.Identity → Target)
    (anchor : source.Identity)
    (targetsConverge :
      ∀ left right : source.Identity, target left = target right) :
    (convergedTargetImageRegime source target anchor targetsConverge).frontier.length = 1 :=
  rfl

end Extensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Extensive.containsWith
#print axioms ConstitutiveSearch.Extensive.containsWith_eq_true_iff_mem
#print axioms ConstitutiveSearch.Extensive.deduplicate
#print axioms ConstitutiveSearch.Extensive.mem_deduplicate_iff
#print axioms ConstitutiveSearch.Extensive.deduplicate_nodup
#print axioms ConstitutiveSearch.Extensive.deduplicate_eq_singleton_of_nonempty_of_all_eq
#print axioms ConstitutiveSearch.Extensive.containsWith_singleton_eq
#print axioms ConstitutiveSearch.Extensive.list_ne_nil_of_mem
#print axioms ConstitutiveSearch.Extensive.map_ne_nil
#print axioms ConstitutiveSearch.Extensive.exactTargetImageFrontier
#print axioms ConstitutiveSearch.Extensive.exactTargetImageFrontier_complete
#print axioms ConstitutiveSearch.Extensive.exactTargetImageFrontier_nodup
#print axioms ConstitutiveSearch.Extensive.attachImageMembers
#print axioms ConstitutiveSearch.Extensive.attachImageMembers_complete
#print axioms ConstitutiveSearch.Extensive.attachImageMembers_length
#print axioms ConstitutiveSearch.Extensive.attachImageMembers_nodup
#print axioms ConstitutiveSearch.Extensive.targetImageIdentityDecEq
#print axioms ConstitutiveSearch.Extensive.computedTargetImageRegime
#print axioms ConstitutiveSearch.Extensive.computedTargetImageRegime_carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.Extensive.computedTargetImageRegime_width_eq_image_width
#print axioms ConstitutiveSearch.Extensive.exactTargetImage_eq_singleton_of_all_targets_equal
#print axioms ConstitutiveSearch.Extensive.computedTargetImageRegime_width_one_of_all_targets_equal
#print axioms ConstitutiveSearch.Extensive.ConvergedTargetObligation
#print axioms ConstitutiveSearch.Extensive.convergedTargetObligationDecEq
#print axioms ConstitutiveSearch.Extensive.convergedTargetImageRegime
#print axioms ConstitutiveSearch.Extensive.convergedTargetImageRegime_carry_value
#print axioms ConstitutiveSearch.Extensive.convergedTargetImageRegime_carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.Extensive.convergedTargetImageRegime_width_exact
/- AXIOM_AUDIT_END -/
