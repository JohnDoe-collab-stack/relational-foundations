
import RelationalPerimeter

/-! Regression checks for actual realization, witnessed identities and one public carrier. -/
namespace RealizedConstitutionRegression
open ConstitutiveSearch
open RelationalExtensive
open EndogenousDecomposition

/-- A nonidentity realization separates realized values from their positions. -/
def flipStage : RelationalOpeningStage Nat 0 1 :=
  { Role := Unit
    Position := Bool
    Occurrence := Bool
    Provenance := Nat
    SourceRelation := fun observed _ => PLift (observed = 0)
    FormationRelation := fun _ occurrence => PLift ((!(!occurrence)) = occurrence)
    TargetRelation := fun _ observed => PLift (observed = 1)
    ProvenanceRelation := fun provenance _ occurrence =>
      PLift (provenance = 0) × PLift (occurrence = occurrence)
    role := ()
    provenance := 0
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl⟩
    positionDecEq := inferInstance
    positionFrontier := [false, true]
    positionComplete := fun position => by
      cases position with
      | false => exact .head _
      | true => exact .tail _ (.head _)
    positionNodup := by
      exact .cons
        (fun value member same => by
          cases member with
          | head => cases same
          | tail _ impossible => cases impossible)
        (.cons (fun _ impossible _ => nomatch impossible) .nil)
    realize := Bool.not
    classify := Bool.not
    realize_classify := fun occurrence => by cases occurrence <;> rfl
    classify_realize := fun position => by cases position <;> rfl
    formationAgreement := fun position => by cases position <;> exact ⟨rfl⟩
    provenanceAgreement := fun _ => ⟨⟨rfl⟩, ⟨rfl⟩⟩ }

example : (relationallyConstitutedOccurrence flipStage false).realized = true := rfl
example : (relationallyConstitutedOccurrence flipStage false).position = false := rfl
example : (constituteRealizedOccurrence flipStage true).position = false := rfl

/-- Exact return uses realized data even when realization is not identity. -/
theorem flip_roundTrip (identity : RelationallyConstitutedOccurrence flipStage) :
    relationallyConstitutedOccurrence flipStage identity.position = identity :=
  relationallyConstitutedOccurrence_roundTrip identity

/-- All four carried witnesses agree with the same stage, including Type data. -/
theorem witnesses_exact
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    identity.sourceWitness = stage.sourceWitness ∧
    identity.formationWitness = stage.formationAt identity.realized ∧
    identity.targetWitness = stage.targetWitness ∧
    identity.provenanceWitness = stage.provenanceAt identity.realized :=
  ⟨identity.sourceWitnessExact, identity.formationWitnessExact,
    identity.targetWitnessExact, identity.provenanceWitnessExact⟩

example (input : Nat) :
    (publicRoleProfileFiniteCarrier input).Identity =
      RoleOccurrenceProfile (publicRelationalConstitutiveRoles input) := rfl

example (input : Nat) :
    (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
      (index := input) ()).Identity =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

example (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  publicCertificate_executedRegime_width input

example (input : Nat)
    (regime : Extensive.ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔ Function.Injective regime.carry :=
  publicCertificate_exponential_iff_carry_injective input regime

end RealizedConstitutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RealizedConstitutionRegression.flipStage
#print axioms RealizedConstitutionRegression.flip_roundTrip
#print axioms RealizedConstitutionRegression.witnesses_exact
/- AXIOM_AUDIT_END -/
