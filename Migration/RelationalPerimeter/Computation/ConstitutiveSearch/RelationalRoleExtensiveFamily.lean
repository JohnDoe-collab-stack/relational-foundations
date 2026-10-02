import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileFiniteCarrier

/-!
# General extensive families constituted by dependent relational roles

The constitutive role history and its unique occurrence-profile carrier are
provided by the earlier relational-profile stratum. This module introduces the
downstream finite carrier, extensive-family interfaces, obligation regimes and
class-level width equivalences. No second profile carrier is defined here.
-/

namespace ConstitutiveSearch
namespace RelationalExtensive

open Extensive

/--
A nontrivial general class.  Problems produce dependent relational histories;
local nontriviality and unbounded stage counts are properties of those
histories.  No global carrier or cardinality formula is a field.
-/
structure RelationalRoleExtensiveFamily where
  State : Type
  Problem : Nat → Type
  initialState : {index : Nat} → Problem index → State
  stageCount : {index : Nat} → Problem index → Nat
  producedHistory : {index : Nat} → (problem : Problem index) →
    DependentRelationalRoleHistory State
      (initialState problem) (stageCount problem)
  nontrivialOpenings : {index : Nat} → (problem : Problem index) →
    AtLeastBinaryLocalArity (producedHistory problem)
  unboundedIndex : Nat → Nat
  unboundedProblem : (bound : Nat) → Problem (unboundedIndex bound)
  unboundedStages : (bound : Nat) →
    bound ≤ stageCount (unboundedProblem bound)

/--
The general binary subclass. Binary width is not stored in this structure:
it is proved from the already produced relational history of every problem.
-/
structure BinaryRelationalRoleExtensiveFamily extends
    RelationalRoleExtensiveFamily where
  binaryOpenings : {index : Nat} → (problem : Problem index) →
    UniformLocalArity (producedHistory problem) 2

namespace RelationalRoleExtensiveFamily

def sourceCarrier
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) : FiniteCarrier :=
  relationalProfileFiniteCarrier (family.producedHistory problem)

theorem sourceWidth_atLeast_exponential
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) :
    2 ^ family.stageCount problem ≤
      (family.sourceCarrier problem).frontier.length := by
  unfold sourceCarrier
  rw [relationalProfileFiniteCarrier_width]
  exact atLeastBinaryLocalArity_width_lowerBound
    (family.producedHistory problem) (family.nontrivialOpenings problem)

/--
General target theorem: on every problem in every relational extensive family,
full operational width is equivalent to preserving the constituted profile
identities separately.
-/
theorem fullWidth_iff_preservesConstitutedIdentities
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.HasFullExtensiveWidth ↔ PreservesIdentitiesSeparately regime :=
  (preservesIdentitiesSeparately_iff_fullWidth regime).symm

/-- Exact factorized capacity form of the general target theorem. -/
theorem fullWidth_iff_exactRegimeCapacity
    (family : RelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.HasFullExtensiveWidth ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  Iff.trans
    (fullWidth_iff_preservesConstitutedIdentities family problem regime)
    (preservesIdentitiesSeparately_iff_exactRegimeCapacity regime)

end RelationalRoleExtensiveFamily

namespace BinaryRelationalRoleExtensiveFamily

/-- Source carrier inherited from the underlying relational family. -/
def sourceCarrier
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) : FiniteCarrier :=
  family.toRelationalRoleExtensiveFamily.sourceCarrier problem

/-- Every problem in a binary relational family has exact exponential width. -/
theorem sourceWidth_eq_twoPow
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index) :
    (family.sourceCarrier problem).frontier.length =
      2 ^ family.stageCount problem := by
  unfold sourceCarrier RelationalRoleExtensiveFamily.sourceCarrier
  rw [relationalProfileFiniteCarrier_width]
  exact uniformLocalArity_width
    (family.producedHistory problem) 2 (family.binaryOpenings problem)

/--
Class-level target theorem. For every problem in every binary relational
extensive family, exact exponential obligation width appears if and only if
the downstream regime preserves the constituted identities separately.
-/
theorem exponentialWidth_iff_preservesConstitutedIdentities
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      PreservesIdentitiesSeparately regime := by
  have sourceWidth := family.sourceWidth_eq_twoPow problem
  constructor
  · intro exponentialWidth
    apply preserves_of_full_width regime
    unfold ObligationRegime.HasFullExtensiveWidth
    exact Eq.trans exponentialWidth sourceWidth.symm
  · intro preserves
    have fullWidth := full_width_of_preserves regime preserves
    unfold ObligationRegime.HasFullExtensiveWidth at fullWidth
    exact Eq.trans fullWidth sourceWidth

/--
The class-level target with the full qualitative wording represented in the
type: identities remain distinct and separately addressable through the
regime itself.
-/
theorem exponentialWidth_iff_distinctSeparateConservation
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  Iff.trans
    (family.exponentialWidth_iff_preservesConstitutedIdentities problem regime)
    (preservesIdentitiesSeparately_iff_distinctSeparateConservation regime)

/-- Exact factorized-capacity form of the class-level exponential `iff`. -/
theorem exponentialWidth_iff_exactRegimeCapacity
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  Iff.trans
    (family.exponentialWidth_iff_preservesConstitutedIdentities problem regime)
    (preservesIdentitiesSeparately_iff_exactRegimeCapacity regime)

end BinaryRelationalRoleExtensiveFamily

/- A concrete variable-arity member proves that the class is not merely the
public binary instance. -/

/-- Constructive finite enumeration avoiding theorem dependencies on quotients. -/
def constructiveFinRange : (size : Nat) → List (Fin size)
  | 0 => []
  | size + 1 =>
      ⟨0, Nat.zero_lt_succ size⟩ ::
        (constructiveFinRange size).map Fin.succ

theorem constructiveFinRange_complete :
    {_size : Nat} → (index : Fin _size) →
      index ∈ constructiveFinRange _size
  | 0, index => Fin.elim0 index
  | _size + 1, ⟨0, _before⟩ => .head _
  | _size + 1, ⟨value + 1, before⟩ =>
      .tail _
        (Extensive.mem_map Fin.succ
          (constructiveFinRange_complete
            ⟨value, Nat.lt_of_succ_lt_succ before⟩))

theorem constructiveFinRange_nodup :
  ∀ size : Nat, (constructiveFinRange size).Nodup
  | 0 => .nil
  | size + 1 => by
      refine .cons ?_ ?_
      · intro value member same
        rcases Extensive.mem_map_preimage Fin.succ member with
          ⟨prior, _priorMember, priorExact⟩
        have impossible : (0 : Nat) = prior.val + 1 :=
          congrArg Fin.val (Eq.trans same priorExact.symm)
        exact Nat.noConfusion impossible
      · exact Extensive.nodup_map Fin.succ
          (fun {_left _right} same => Fin.succ_inj.mp same)
          (constructiveFinRange_nodup size)

theorem constructiveFinRange_length :
    ∀ size : Nat, (constructiveFinRange size).length = size
  | 0 => rfl
  | size + 1 => by
      exact congrArg Nat.succ
        (Eq.trans
          (Extensive.length_map Fin.succ (constructiveFinRange size))
          (constructiveFinRange_length size))

def increasingArityStage (source : Nat) :
    RelationalOpeningStage Nat source (source + 1) :=
  { Role := Unit
    Position := Fin (source + 2)
    Occurrence := Fin (source + 2)
    Provenance := Nat
    SourceRelation := fun observed _ => PLift (observed = source)
    FormationRelation := fun _ occurrence => PLift (occurrence.val < source + 2)
    TargetRelation := fun _ observed => PLift (observed = source + 1)
    ProvenanceRelation := fun provenance _ occurrence =>
      PLift (provenance = source ∧ occurrence.val < source + 2)
    role := ()
    provenance := source
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl⟩
    positionDecEq := inferInstance
    positionFrontier := constructiveFinRange (source + 2)
    positionComplete := constructiveFinRange_complete
    positionNodup := constructiveFinRange_nodup _
    realize := id
    classify := id
    realize_classify := fun _ => rfl
    classify_realize := fun _ => rfl
    formationAgreement := fun occurrence => ⟨occurrence.isLt⟩
    provenanceAgreement := fun occurrence => ⟨rfl, occurrence.isLt⟩ }

def increasingArityHistory :
    (count source : Nat) →
      DependentRelationalRoleHistory Nat source count
  | 0, source => .nil source
  | count + 1, source =>
      .step (increasingArityStage source)
        (increasingArityHistory count (source + 1))

theorem increasingArityHistory_nontrivial :
    (count source : Nat) →
      AtLeastBinaryLocalArity (increasingArityHistory count source)
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · rw [relationallyConstitutedOccurrenceFrontier,
          relational_length_map]
        change 2 ≤ (constructiveFinRange (source + 2)).length
        rw [constructiveFinRange_length]
        exact Nat.le_add_left 2 source
      · exact increasingArityHistory_nontrivial count (source + 1)

/-- Variable local arities and unbounded histories form a concrete member. -/
def increasingArityRelationalFamily : RelationalRoleExtensiveFamily :=
  { State := Nat
    Problem := fun _ => Unit
    initialState := fun _ => 0
    stageCount := fun {index} _ => index + 1
    producedHistory := fun {index} _ => increasingArityHistory (index + 1) 0
    nontrivialOpenings := fun {index} _ =>
      increasingArityHistory_nontrivial (index + 1) 0
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound }

theorem increasingArityRelationalFamily_unbounded (bound : Nat) :
    bound ≤ increasingArityRelationalFamily.stageCount
      (increasingArityRelationalFamily.unboundedProblem bound) :=
  increasingArityRelationalFamily.unboundedStages bound

theorem increasingArityRelationalFamily_variable
    (source : Nat) :
    (relationallyConstitutedOccurrenceFrontier
      (increasingArityStage source)).length = source + 2 :=
  Eq.trans
    (relational_length_map
      (relationallyConstitutedOccurrence (increasingArityStage source))
      (constructiveFinRange (source + 2)))
    (constructiveFinRange_length _)

/-- A binary relational opening independent of the public SAT construction. -/
def abstractBinaryStage (source : Nat) :
    RelationalOpeningStage Nat source (source + 1) :=
  { Role := Nat
    Position := Fin 2
    Occurrence := Fin 2
    Provenance := Nat
    SourceRelation := fun observed role => PLift (observed = role)
    FormationRelation := fun role occurrence =>
      PLift (role = source ∧ occurrence.val < 2)
    TargetRelation := fun role observed =>
      PLift (role = source ∧ observed = source + 1)
    ProvenanceRelation := fun provenance role occurrence =>
      PLift (provenance = source ∧ role = source ∧ occurrence.val < 2)
    role := source
    provenance := source
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl, rfl⟩
    positionDecEq := inferInstance
    positionFrontier := constructiveFinRange 2
    positionComplete := constructiveFinRange_complete
    positionNodup := constructiveFinRange_nodup 2
    realize := id
    classify := id
    realize_classify := fun _ => rfl
    classify_realize := fun _ => rfl
    formationAgreement := fun occurrence => ⟨rfl, occurrence.isLt⟩
    provenanceAgreement := fun occurrence =>
      ⟨rfl, rfl, occurrence.isLt⟩ }

def abstractBinaryHistory :
    (count source : Nat) →
      DependentRelationalRoleHistory Nat source count
  | 0, source => .nil source
  | count + 1, source =>
      .step (abstractBinaryStage source)
        (abstractBinaryHistory count (source + 1))

theorem abstractBinaryHistory_uniform :
    (count source : Nat) →
      UniformLocalArity (abstractBinaryHistory count source) 2
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · exact constructiveFinRange_length 2
      · exact abstractBinaryHistory_uniform count (source + 1)

theorem abstractBinaryHistory_nontrivial :
    (count source : Nat) →
      AtLeastBinaryLocalArity (abstractBinaryHistory count source)
  | 0, _ => True.intro
  | count + 1, source => by
      constructor
      · change 2 ≤ (constructiveFinRange 2).length
        rw [constructiveFinRange_length]
        exact Nat.le_refl 2
      · exact abstractBinaryHistory_nontrivial count (source + 1)

/--
An unbounded binary family distinct from the public SAT family. Its role,
formation, target, and provenance relations are all explicit positive data.
-/
def abstractBinaryRelationalFamily : BinaryRelationalRoleExtensiveFamily :=
  { State := Nat
    Problem := fun _ => Unit
    initialState := fun _ => 0
    stageCount := fun {index} _ => index + 1
    producedHistory := fun {index} _ => abstractBinaryHistory (index + 1) 0
    nontrivialOpenings := fun {index} _ =>
      abstractBinaryHistory_nontrivial (index + 1) 0
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound
    binaryOpenings := fun {index} _ =>
      abstractBinaryHistory_uniform (index + 1) 0 }

theorem abstractBinaryRelationalFamily_unbounded (bound : Nat) :
    bound ≤ abstractBinaryRelationalFamily.stageCount
      (abstractBinaryRelationalFamily.unboundedProblem bound) :=
  abstractBinaryRelationalFamily.unboundedStages bound

end RelationalExtensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily.fullWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily.fullWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.sourceWidth_eq_twoPow
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_distinctSeparateConservation
#print axioms ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_complete
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_nodup
#print axioms ConstitutiveSearch.RelationalExtensive.constructiveFinRange_length
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityStage
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityHistory
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily_unbounded
#print axioms ConstitutiveSearch.RelationalExtensive.increasingArityRelationalFamily_variable
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryStage
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryHistory
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryRelationalFamily
#print axioms ConstitutiveSearch.RelationalExtensive.abstractBinaryRelationalFamily_unbounded
/- AXIOM_AUDIT_END -/
