import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalReductionHistory

/-!
An independent-addressing boundary for complete structural profiles.

The result is deliberately representation-relative and extensional.  It does
not estimate the running time or storage use of an arbitrary algorithm.  It
says that any interface assigning a distinct finite slot to every constituted
structural profile needs at least as many slots as the exact structural
frontier contains.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

/-- A finite addressing interface that keeps every structural profile
independently recoverable.  Injectivity is the operative independence
condition; no enumeration or numerical width is stored in the interface. -/
structure IndependentProfileAddressing
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run) where
  slotCount : Nat
  slotOf : StructuralObligation roles -> Fin slotCount
  slotOf_injective :
    forall {left right}, slotOf left = slotOf right -> left = right

/-- Independent finite addressing of the profiles expanded by one particular
typed normalizer program.  Unlike the compatibility interface above, this
structure makes the program whose exhaustive expansion is being addressed an
explicit index of the type. -/
structure IndependentProgramProfileAddressing
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    (roles : ThreadedConstitutiveRoleHistory run)
    (program : ConstitutiveNormalizerProgram roles) where
  slotCount : Nat
  slotOf : program.Profile -> Fin slotCount
  slotOf_injective :
    forall {left right}, slotOf left = slotOf right -> left = right

/-- The historical public addressing interface is exactly addressing of the
canonical program expansion, not an independently generated carrier. -/
def IndependentProfileAddressing.toCanonicalProgramAddressing
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (addressing : IndependentProfileAddressing roles) :
    IndependentProgramProfileAddressing roles
      (buildConstitutiveNormalizerProgram roles) :=
  ⟨addressing.slotCount, addressing.slotOf, addressing.slotOf_injective⟩

/-- Remove the first occurrence of a natural number using its constructive
decidable equality. -/
def removeFirstNat (target : Nat) : List Nat -> List Nat
  | [] => []
  | head :: tail =>
      if target = head then tail else head :: removeFirstNat target tail

/-- Removing another value preserves membership. -/
theorem removeFirstNat_preserves_other (target value : Nat)
    (different : value ≠ target) :
    forall {values : List Nat}, List.Mem value values ->
      List.Mem value (removeFirstNat target values)
  | _ :: tail, .head _ => by
      unfold removeFirstNat
      split
      next same => exact False.elim (different same.symm)
      next _ => exact .head _
  | head :: _, .tail _ prior => by
      unfold removeFirstNat
      split
      next same =>
        cases same
        exact prior
      next _ =>
        exact .tail _ (removeFirstNat_preserves_other target value different prior)

/-- Removing a value known to occur decreases length by exactly one. -/
theorem removeFirstNat_length_of_mem (target : Nat) :
    forall {values : List Nat}, List.Mem target values ->
      (removeFirstNat target values).length + 1 = values.length
  | _ :: _, .head _ => by
      unfold removeFirstNat
      split
      · rfl
      · contradiction
  | head :: tail, .tail _ prior => by
      unfold removeFirstNat
      split
      · rfl
      · change (removeFirstNat target tail).length + 1 + 1 = tail.length + 1
        exact congrArg (fun length => length + 1)
          (removeFirstNat_length_of_mem target prior)

/-- Constructive specialization of the duplicate-free subset bound to natural
numbers.  Its recursion uses only the decidable removal above. -/
theorem natNodup_length_le_of_subset :
    forall {left right : List Nat},
      left.Nodup -> (left ⊆ right) -> left.length <= right.length
  | [], _, .nil, _ => Nat.zero_le _
  | head :: tail, right, .cons headFresh tailNodup, contained => by
      have headMember : List.Mem head right := contained (.head _)
      have tailContained : tail ⊆ removeFirstNat head right := by
        intro value valueMember
        exact removeFirstNat_preserves_other head value
          (fun same => headFresh value valueMember same.symm)
          (contained (.tail _ valueMember))
      have tailBound : tail.length <= (removeFirstNat head right).length :=
        natNodup_length_le_of_subset tailNodup tailContained
      calc
        tail.length + 1 <= (removeFirstNat head right).length + 1 :=
          Nat.succ_le_succ tailBound
        _ = right.length := removeFirstNat_length_of_mem head headMember

/-- Descending constructive enumeration of all naturals strictly below a
bound.  It is local so its completeness and length do not rely on extensional
library lemmas. -/
def naturalsBelow : Nat -> List Nat
  | 0 => []
  | bound + 1 => bound :: naturalsBelow bound

theorem naturalsBelow_complete (value : Nat) :
    forall {bound : Nat}, value < bound ->
      List.Mem value (naturalsBelow bound)
  | 0, before => False.elim (Nat.not_lt_zero value before)
  | _bound + 1, before =>
      match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with
      | .inl below => .tail _ (naturalsBelow_complete value below)
      | .inr same => same.symm ▸ .head _

theorem naturalsBelow_length :
    forall bound : Nat, (naturalsBelow bound).length = bound
  | 0 => rfl
  | bound + 1 => congrArg Nat.succ (naturalsBelow_length bound)

/-- Exact lower bound for independently addressing the exhaustive expansion of
an arbitrary typed program.  The proof enumerates the program's own profiles;
no role-indexed carrier is substituted for them. -/
theorem independentProgramProfileAddressing_slots_ge_profileWidth
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    {program : ConstitutiveNormalizerProgram roles}
    (addressing : IndependentProgramProfileAddressing roles program) :
    program.profileWidth <= addressing.slotCount := by
  let addressed :=
    program.profileFrontier.map (fun profile => (addressing.slotOf profile).val)
  have addressedNodup : addressed.Nodup :=
    nodup_map_constructive
      (fun profile => (addressing.slotOf profile).val)
      (fun same => addressing.slotOf_injective (Fin.ext same))
      (ConstitutiveNormalizerProgram.profileFrontier_nodup program)
  have contained : forall value, List.Mem value addressed ->
      List.Mem value (naturalsBelow addressing.slotCount) := by
    intro value member
    let ⟨profile, _profileMember, profileExact⟩ :=
      mem_map_preimage_constructive
        (fun profile => (addressing.slotOf profile).val) member
    rw [<- profileExact]
    exact naturalsBelow_complete _ (addressing.slotOf profile).isLt
  have lengthBound : addressed.length <= (naturalsBelow addressing.slotCount).length :=
    natNodup_length_le_of_subset addressedNodup contained
  have slotBound : addressed.length <= addressing.slotCount := by
    exact Eq.mp
      (congrArg (fun length => addressed.length <= length)
        (naturalsBelow_length addressing.slotCount))
      lengthBound
  exact Eq.mp
    (congrArg (fun length => length <= addressing.slotCount)
      (length_map_constructive
        (fun profile => (addressing.slotOf profile).val)
        program.profileFrontier))
    slotBound

/-- The program-indexed bound read through the exact binary expansion of its
instruction constructors. -/
theorem independentProgramProfileAddressing_slots_ge_two_pow_instructionCount
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    {program : ConstitutiveNormalizerProgram roles}
    (addressing : IndependentProgramProfileAddressing roles program) :
    2 ^ program.instructionCount <= addressing.slotCount := by
  rw [<- ConstitutiveNormalizerProgram.profileWidth_eq_two_pow_instructionCount
    program]
  exact independentProgramProfileAddressing_slots_ge_profileWidth addressing

/-- Exact lower bound for any injective finite addressing of the profiles. -/
theorem independentProfileAddressing_slots_ge_structuralWidth
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (addressing : IndependentProfileAddressing roles) :
    structuralWidth roles <= addressing.slotCount := by
  exact independentProgramProfileAddressing_slots_ge_profileWidth
    addressing.toCanonicalProgramAddressing

/-- The same lower bound read through the exact `2^stageCount` frontier. -/
theorem independentProfileAddressing_slots_ge_two_pow_stageCount
    {depth count : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {run : ConstitutiveExecutionHistory (count := count) state}
    {roles : ThreadedConstitutiveRoleHistory run}
    (addressing : IndependentProfileAddressing roles) :
    2 ^ operationalStageCount roles <= addressing.slotCount := by
  rw [<- structuralWidth_eq_two_pow_stageCount roles]
  exact independentProfileAddressing_slots_ge_structuralWidth addressing

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentProgramProfileAddressing
#print axioms ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing.toCanonicalProgramAddressing
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstNat
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstNat_preserves_other
#print axioms ConstitutiveSearch.EndogenousDecomposition.removeFirstNat_length_of_mem
#print axioms ConstitutiveSearch.EndogenousDecomposition.natNodup_length_le_of_subset
#print axioms ConstitutiveSearch.EndogenousDecomposition.naturalsBelow
#print axioms ConstitutiveSearch.EndogenousDecomposition.naturalsBelow_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.naturalsBelow_length
#print axioms ConstitutiveSearch.EndogenousDecomposition.independentProgramProfileAddressing_slots_ge_profileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.independentProgramProfileAddressing_slots_ge_two_pow_instructionCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.independentProfileAddressing_slots_ge_structuralWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.independentProfileAddressing_slots_ge_two_pow_stageCount
/- AXIOM_AUDIT_END -/
