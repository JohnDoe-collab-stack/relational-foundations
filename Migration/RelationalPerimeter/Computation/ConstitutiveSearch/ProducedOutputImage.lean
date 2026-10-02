import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage

/-! The image carrier depends on the produced map, not on a convergence premise.
Convergence supplies equality on this image and permits local duplicate removal.
Only local frontiers are used by the executed instance. -/
namespace ConstitutiveSearch.Extensive.ProducedOutputImage

def Value (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target) :=
  {value : Target // ∃ identity, produced identity = value}

def carry (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target) (identity : source.Identity) :
    Value source produced := ⟨produced identity, identity, rfl⟩

theorem value_eq {source : FiniteCarrier} {Target : Type}
    {produced : source.Identity → Target}
    (converges : ∀ p q, produced p = produced q)
    (left right : Value source produced) : left = right := by
  apply Subtype.ext
  rcases left.2 with ⟨p, hp⟩
  rcases right.2 with ⟨q, hq⟩
  exact Eq.trans hp.symm (Eq.trans (converges p q) hq)

def decEq (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (converges : ∀ p q, produced p = produced q) :
    DecidableEq (Value source produced) :=
  fun left right => isTrue (value_eq converges left right)

/- The image can be enumerated before any convergence theorem is supplied.
Equality must be decided on actual image values; it need not be available on
the entire continuation codomain. -/
def imageRegime (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (equality : DecidableEq (Value source produced)) : ObligationRegime source :=
  { Obligation := Value source produced
    decEq := equality
    frontier := deduplicate equality (source.frontier.map (carry source produced))
    complete := fun value => by
      apply (mem_deduplicate_iff equality _ _).mpr
      rcases value.2 with ⟨identity, exactValue⟩
      have same : carry source produced identity = value := Subtype.ext exactValue
      exact same ▸ mem_map (carry source produced) (source.complete identity)
    nodup := deduplicate_nodup equality _
    carry := carry source produced
    carry_surjective := fun value => by
      rcases value.2 with ⟨identity, exactValue⟩
      exact ⟨identity, Subtype.ext exactValue⟩ }

/-- When the target has decidable equality, compare its actual values. -/
def targetEquality (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target) (equality : DecidableEq Target) :
    DecidableEq (Value source produced) :=
  fun left right => match equality left.val right.val with
    | isTrue same => isTrue (Subtype.ext same)
    | isFalse different => isFalse (fun same => different (congrArg Subtype.val same))

/-- The executed instance supplies image equality from its proved convergence. -/
def regime (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (converges : ∀ p q, produced p = produced q) : ObligationRegime source :=
  imageRegime source produced (decEq source produced converges)

/-- Membership alone does not merge outputs; equality reflects their values. -/
theorem image_carry_fibres (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (equality : DecidableEq (Value source produced)) (left right : source.Identity) :
    (imageRegime source produced equality).carry left =
        (imageRegime source produced equality).carry right ↔ produced left = produced right :=
  ⟨fun same => congrArg Subtype.val same, fun same => Subtype.ext same⟩

/-- Convergence is exactly the condition for one image obligation, not a
premise in the image-regime type. Nonemptiness is supplied by an actual source. -/
theorem image_width_one_iff_converges (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (equality : DecidableEq (Value source produced)) (anchor : source.Identity) :
    (imageRegime source produced equality).frontier.length = 1 ↔
      ∀ left right, produced left = produced right := by
  constructor
  · intro width left right
    let image := imageRegime source produced equality
    have membersEqual : ∀ p q : image.Obligation, p = q := by
      cases equation : image.frontier with
      | nil =>
          have member := image.complete (image.carry anchor)
          rw [equation] at member
          cases member
      | cons first rest =>
          have length : rest.length + 1 = 1 := by
            change image.frontier.length = 1 at width
            rw [equation] at width
            exact width
          have empty : rest = [] := by
            have zero : rest.length = 0 := Nat.succ.inj length
            cases rest with
            | nil => rfl
            | cons _ _ => cases zero
          intro p q
          have pm := image.complete p
          have qm := image.complete q
          rw [equation, empty] at pm qm
          have pe : p = first := by
            cases pm with
            | head => rfl
            | tail _ impossible => cases impossible
          have qe : q = first := by
            cases qm with
            | head => rfl
            | tail _ impossible => cases impossible
          exact Eq.trans pe qe.symm
    exact congrArg Subtype.val (membersEqual (image.carry left) (image.carry right))
  · intro converges
    have frontier : (imageRegime source produced equality).frontier =
        [carry source produced anchor] := by
      apply deduplicate_eq_singleton_of_nonempty_of_all_eq
      · exact map_ne_nil _ (list_ne_nil_of_mem (source.complete anchor))
      · intro value _
        exact value_eq converges value (carry source produced anchor)
    rw [frontier]
    rfl

theorem carry_fibres (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (converges : ∀ p q, produced p = produced q) (left right : source.Identity) :
    (regime source produced converges).carry left =
        (regime source produced converges).carry right ↔ produced left = produced right :=
  ⟨fun same => congrArg Subtype.val same, fun same => Subtype.ext same⟩

/-- The frontier equation follows from produced convergence and nonemptiness. -/
theorem frontier_exact (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (converges : ∀ p q, produced p = produced q) (anchor : source.Identity) :
    (regime source produced converges).frontier = [carry source produced anchor] := by
  apply deduplicate_eq_singleton_of_nonempty_of_all_eq
  · exact map_ne_nil _ (list_ne_nil_of_mem (source.complete anchor))
  · intro value _
    exact value_eq converges value (carry source produced anchor)

theorem width_exact (source : FiniteCarrier) {Target : Type}
    (produced : source.Identity → Target)
    (converges : ∀ p q, produced p = produced q) (anchor : source.Identity) :
    (regime source produced converges).frontier.length = 1 :=
  (image_width_one_iff_converges source produced
    (decEq source produced converges) anchor).mpr converges

end ConstitutiveSearch.Extensive.ProducedOutputImage

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.Value
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.carry
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.value_eq
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.decEq
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.imageRegime
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.targetEquality
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.image_carry_fibres
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.image_width_one_iff_converges
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.regime
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.carry_fibres
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.frontier_exact
#print axioms ConstitutiveSearch.Extensive.ProducedOutputImage.width_exact
/- AXIOM_AUDIT_END -/
