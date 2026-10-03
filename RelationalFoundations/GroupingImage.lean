import RelationalFoundations.GroupingNormalization
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping.FiniteImage
universe u

/-- Constructive membership test with an explicit equality decision. -/
def containsWith
    {α : Type u}
    (decideEq : DecidableEq α)
    (value : α) : List α → Bool
  | [] => false
  | head :: tail =>
      match decideEq value head with
      | isTrue _ => true
      | isFalse _ => containsWith decideEq value tail

theorem containsWith_eq_true_iff_mem
    {α : Type u}
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
    {α : Type u}
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
    {α : Type u}
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
    {α : Type u}
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
    {α : Type u}
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

structure Source (S : Type u) where
  equality : DecidableEq S
  frontier : List S
  complete : ∀ x, x ∈ frontier
  distinct : frontier.Nodup

def frontier (rules : Rules.{u}) (source : Source rules.State) : List rules.State :=
  deduplicate source.equality (source.frontier.map rules.normal)

theorem mappedMember {A B : Type u} (f : A → B) {x : A} {items : List A}
    (member : x ∈ items) : f x ∈ items.map f := by
  induction member with
  | head => exact List.Mem.head _
  | tail _ _ ih => exact List.Mem.tail _ ih

theorem mapWitness {A B : Type u} (f : A → B) (y : B) (items : List A) :
    y ∈ items.map f → ∃ x, x ∈ items ∧ f x = y := by
  induction items with
  | nil => intro impossible; cases impossible
  | cons head tail ih =>
      intro member
      cases member with
      | head => exact ⟨head, .head _, rfl⟩
      | tail _ member =>
          obtain ⟨x, old, same⟩ := ih member
          exact ⟨x, .tail _ old, same⟩

theorem frontier_exact (rules : Rules.{u}) (source : Source rules.State) (y : rules.State) :
    y ∈ frontier rules source ↔ rules.normal y = y := by
  constructor
  · intro member
    obtain ⟨x, _, same⟩ := mapWitness rules.normal y source.frontier
      ((mem_deduplicate_iff source.equality y _).mp member)
    cases same
    exact rules.normal_idempotent x
  · intro fixed
    apply (mem_deduplicate_iff source.equality y _).mpr
    exact fixed ▸ mappedMember rules.normal (source.complete y)

theorem frontier_nodup (rules : Rules.{u}) (source : Source rules.State) :
    (frontier rules source).Nodup := deduplicate_nodup source.equality _

/-- A normal target positively carries its own preimage. -/
def Target (rules : Rules.{u}) := {x : rules.State // rules.normal x = x}
def carry (rules : Rules.{u}) (x : rules.State) : Target rules :=
  ⟨rules.normal x, rules.normal_idempotent x⟩

theorem carry_fibres (rules : Rules.{u}) (x y : rules.State) :
    carry rules x = carry rules y ↔ Nonempty (Chain rules.Step x y) := by
  constructor
  · intro same
    exact (rules.normal_eq_iff_chain x y).mp (congrArg Subtype.val same)
  · intro chain
    exact Subtype.ext ((rules.normal_eq_iff_chain x y).mpr chain)

theorem carry_surjective (rules : Rules.{u}) (target : Target rules) :
    carry rules target.1 = target := Subtype.ext target.2

/-- A separately constructed fragment frontier is certified by fixed-point
membership; it need not enumerate the extensive source in its producer. -/
structure Composed (rules : Rules.{u}) where
  frontier : List rules.State
  distinct : frontier.Nodup
  exact : ∀ y, y ∈ frontier ↔ rules.normal y = y

theorem exhaustive_composed (rules : Rules.{u}) (source : Source rules.State)
    (composed : Composed rules) (y : rules.State) :
    y ∈ frontier rules source ↔ y ∈ composed.frontier :=
  (frontier_exact rules source y).trans (composed.exact y).symm

theorem singleton_of_connected (rules : Rules.{u}) (source : Source rules.State)
    (anchor : rules.State) (connected : ∀ x y, Join rules.Step x y) :
    frontier rules source = [rules.normal anchor] := by
  apply deduplicate_eq_singleton_of_nonempty_of_all_eq source.equality
  · intro empty
    have member := mappedMember rules.normal (source.complete anchor)
    rw [empty] at member
    cases member
  · intro value member
    obtain ⟨x, _, same⟩ := mapWitness rules.normal value source.frontier member
    exact same.symm.trans (rules.normal_join (connected x anchor))

theorem empty_image (rules : Rules.{u}) (source : Source rules.State) (empty : source.frontier = []) :
    frontier rules source = [] := by
  unfold frontier
  rw [empty]
  rfl
/-- Remove the first occurrence of a value using constructive decidable equality. -/
def removeFirst {α : Type u} [DecidableEq α] (target : α) : List α → List α
  | [] => []
  | head :: tail =>
      if target = head then tail else head :: removeFirst target tail

/-- Removing another value preserves membership. -/
theorem removeFirst_preserves_other
    {α : Type u} [DecidableEq α]
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
    {α : Type u} [DecidableEq α]
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
    {α : Type u} [DecidableEq α] :
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

theorem composed_width (rules : Rules.{u}) (source : Source rules.State) (composed : Composed rules) :
    (frontier rules source).length = composed.frontier.length := by
  letI : DecidableEq rules.State := source.equality
  exact Nat.le_antisymm
    (nodup_length_le_of_subset (frontier_nodup rules source)
      (fun _ member => (exhaustive_composed rules source composed _).mp member))
    (nodup_length_le_of_subset composed.distinct
      (fun _ member => (exhaustive_composed rules source composed _).mpr member))

end RelationalFoundations.CertifiedGrouping.FiniteImage
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.deduplicate
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.mem_deduplicate_iff
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.deduplicate_nodup
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.frontier
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.frontier_exact
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.carry
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.carry_fibres
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.exhaustive_composed
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.singleton_of_connected
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.empty_image
#print axioms RelationalFoundations.CertifiedGrouping.FiniteImage.composed_width
/- AXIOM_AUDIT_END -/
