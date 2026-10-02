import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy
import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage

/-!
# Local status before dependent operational production

The source identities are the constituted occurrences. A preserving transport
licenses a directed action; neither its status nor the local image is supplied
by a numerical width. No global history or convergence premise is an input
to these local definitions.
-/
namespace ConstitutiveSearch.EndogenousDecomposition.RoleStatus
open SAT Extensive RelationalExtensive

abbrev Status {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :=
  Option (AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
    (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right))

def target {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run} :
    Status role → RoleConstitutedOccurrence role → RoleConstitutedOccurrence role
  | none, occurrence => occurrence
  | some _, _ => roleConstitutedOccurrenceAt role .right

/-- A realized local target is retained by the same status, also when pending. -/
theorem target_idempotent {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (status : Status role) (occurrence : RoleConstitutedOccurrence role) :
    target status (target status occurrence) = target status occurrence := by
  cases status <;> rfl

/-- Complete finite image, constructed before any convergence specialisation. -/
def localRegime {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} (role : RelationalConstitutiveRoleStage run)
    (status : Status role) : ObligationRegime (roleOpeningFiniteCarrier role) :=
  computedTargetImageRegime (roleOpeningFiniteCarrier role)
    (relationallyConstitutedOccurrenceDecEq (generalOpeningStageOfRole role)) (target status)

theorem localFibres {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (status : Status role) (p q : RoleConstitutedOccurrence role) :
    (localRegime role status).carry p = (localRegime role status).carry q ↔
      target status p = target status q :=
  computedTargetImageRegime_carry_eq_iff_target_eq _ _ _ _ _

theorem pendingWidth {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} (role : RelationalConstitutiveRoleStage run) :
    (localRegime role none).frontier.length = 2 := rfl

theorem absorbedWidth {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (transport : AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
      (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right)) :
    (localRegime role (some transport)).frontier.length = 1 := rfl

/-- Data-level action uses the supplied transport only in its absorbed case. -/
def act {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run} :
    (status : Status role) → (o : RoleConstitutedOccurrence role) →
      RoleOpeningPayload o → RoleOpeningPayload (target status o)
  | none, _, c => c
  | some transport, o, c =>
      eliminateRoleConstitutedOccurrence role o
        (motive := fun o => RoleOpeningPayload o →
          RoleOpeningPayload (roleConstitutedOccurrenceAt role .right))
        transport.map (fun c => c) c

/-- The preservation law is separate from the action, and consumes the transport. -/
theorem act_preserves {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    (status : Status role) (o : RoleConstitutedOccurrence role) (c : RoleOpeningPayload o) :
    RoleSemantics.LocalAccept o c → RoleSemantics.LocalAccept (target status o) (act status o c) := by
  cases status with
  | none => exact fun accepted => accepted
  | some transport =>
    exact eliminateRoleConstitutedOccurrence role o
      (motive := fun o => ∀ c : RoleOpeningPayload o,
        RoleSemantics.LocalAccept o c →
        RoleSemantics.LocalAccept (target (some transport) o) (act (some transport) o c))
      transport.preservesAccept (fun _ accepted => accepted) c

end ConstitutiveSearch.EndogenousDecomposition.RoleStatus

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.target_idempotent
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.Status
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.localRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.localFibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.pendingWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.absorbedWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.act
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.act_preserves
/- AXIOM_AUDIT_END -/
