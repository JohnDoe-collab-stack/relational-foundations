import RelationalPerimeter

namespace AristotleCorrectionRegression
set_option maxHeartbeats 3200000
open ConstitutiveSearch ConstitutiveSearch.SAT ConstitutiveSearch.Extensive
open ConstitutiveSearch.EndogenousDecomposition

/-- Same two constituted roles in all three policy comparisons. -/
def twoRoles {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next) :
    RelationalConstitutiveRoleHistory (.step first (.step second (.nil second.next))) :=
  .step (relationalConstitutiveRoleStage first)
    (.step (relationalConstitutiveRoleStage second) .nil)

def twoPending {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next) : RoleStatus.History (twoRoles first second) :=
  .step none (.step none .nil)

def oneAbsorbed {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next) : RoleStatus.History (twoRoles first second) :=
  .step (some (RoleStatus.returnedTransport (executedRoleReductionLicense (relationalConstitutiveRoleStage first))))
    (.step none .nil)

def twoAbsorbed {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next) : RoleStatus.History (twoRoles first second) :=
  .step (some (RoleStatus.returnedTransport (executedRoleReductionLicense (relationalConstitutiveRoleStage first))))
    (.step (some (RoleStatus.returnedTransport (executedRoleReductionLicense (relationalConstitutiveRoleStage second)))) .nil)

theorem widths_four_two_one {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next) :
    (rolewiseObligationFrontier (twoPending first second).policy).length = 4 ∧
    (rolewiseObligationFrontier (oneAbsorbed first second).policy).length = 2 ∧
    (rolewiseObligationFrontier (twoAbsorbed first second).policy).length = 1 :=
  ⟨(twoPending first second).width, (oneAbsorbed first second).width, (twoAbsorbed first second).width⟩

/-- The mixed-case consumer preserves the same local criterion on every payload. -/
theorem mixed_preservation {state : CausalConstitutiveState}
    (first : CausalConstitutiveStageExecution state)
    (second : CausalConstitutiveStageExecution first.next)
    (p : RoleOccurrenceProfile (twoRoles first second)) (c : RoleProfilePayload p)
    (accepted : RoleSemantics.ProfileAccept p c) :
    RoleSemantics.ProfileAccept ((oneAbsorbed first second).selected p)
      ((oneAbsorbed first second).transform p c) :=
  (oneAbsorbed first second).preserves p c accepted

/-- A constant carry cannot satisfy exact fibres when a local opening is pending. -/
theorem pending_occurrences_not_grouped {state : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution state} (role : RelationalConstitutiveRoleStage run) :
    (RoleStatus.localRegime role none).carry (roleConstitutedOccurrenceAt role .left) ≠
      (RoleStatus.localRegime role none).carry (roleConstitutedOccurrenceAt role .right) := by
  intro same
  have impossible := (RoleStatus.localFibres none _ _).mp same
  exact openingRolePosition_left_ne_right role
    (congrArg (fun occurrence : RoleConstitutedOccurrence role => occurrence.position) impossible)

/-- The source parent is not a realization of its own newly generated child. -/
theorem parent_is_not_formed_child {root : Cnf} (parent : GeneratedStructuralBranchContext root)
    (var : Var) (value : Bool) (fresh : StructuralDecisionsAvoid var parent.context.decisions) :
    ¬ Nonempty (GeneratedChildFormation parent var value fresh parent) := by
  intro witness
  rcases witness with ⟨formation⟩
  exact GeneratedChildFormation.parent_impossible parent var value fresh formation

/-- Correct canonical values do not entail preservation of arbitrary accepted data. -/
def badDescription : SemanticImage.Description :=
  { Source := Unit, Payload := fun _ => Bool, Target := Bool
    Accept := fun _ _ => True, TargetAccept := fun value => value = false
    action := fun _ payload => payload, canonical := fun _ => false, produced := fun _ => false
    reflect := fun target => ⟨(), target⟩, SourceInvariant := True }

theorem no_admission_from_convergence : ¬ SemanticImage.Admission badDescription := by
  intro admission
  have impossible : (true : Bool) = false := admission.preservation () true True.intro
  cases impossible

theorem no_usable_image_from_true :
    ¬ Nonempty (SemanticImage.AdmittedImageValue badDescription (fun value => value = false)) := by
  intro existsValue
  rcases existsValue with ⟨obligation⟩
  have preimage : badDescription.produced () = obligation.value := obligation.produced.symm
  have impossible : (true : Bool) = false :=
    ((obligation.semantics.2.1 () preimage).2 true True.intro)
  cases impossible

/-- Membership in the image alone remains constructible. -/
theorem bad_image_exists : ∃ target, target = badDescription.produced () := ⟨false, rfl⟩

/-- One authoritative carrier also serves the generic admission consumer. -/
theorem unchanged_public_carrier (input : Nat) :
    (publicCertificateNormalization input).imageDescription.Source =
      RoleOccurrenceProfile (publicRelationalConstitutiveRoles input) := rfl

theorem public_width_comes_from_status (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length =
      (rolewiseObligationFrontier
        (RoleStatus.executed (publicCausalOperationalExecution input).stagewiseDecomposition.reduction).policy).length :=
  (publicCertificateNormalization input).regimeWidth_eq_statusWidth

theorem public_status_action (input : Nat)
    (p : RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)) (c : RoleProfilePayload p) :
    RoleStatus.executedPayloadOutput _ p
      ((RoleStatus.executed (publicCausalOperationalExecution input).stagewiseDecomposition.reduction).transform p c) =
        (publicCarriedProfilePayload input p c).1 :=
  Eq.trans (RoleStatus.executed_action_exact _ p c) (publicCarriedProfilePayload_action input p c).symm

end AristotleCorrectionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms AristotleCorrectionRegression.twoRoles
#print axioms AristotleCorrectionRegression.twoPending
#print axioms AristotleCorrectionRegression.oneAbsorbed
#print axioms AristotleCorrectionRegression.twoAbsorbed
#print axioms AristotleCorrectionRegression.widths_four_two_one
#print axioms AristotleCorrectionRegression.mixed_preservation
#print axioms AristotleCorrectionRegression.pending_occurrences_not_grouped
#print axioms AristotleCorrectionRegression.parent_is_not_formed_child
#print axioms AristotleCorrectionRegression.badDescription
#print axioms AristotleCorrectionRegression.no_admission_from_convergence
#print axioms AristotleCorrectionRegression.no_usable_image_from_true
#print axioms AristotleCorrectionRegression.bad_image_exists
#print axioms AristotleCorrectionRegression.unchanged_public_carrier
#print axioms AristotleCorrectionRegression.public_width_comes_from_status
#print axioms AristotleCorrectionRegression.public_status_action
/- AXIOM_AUDIT_END -/
