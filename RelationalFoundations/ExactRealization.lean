import RelationalFoundations.ExactTransport
set_option genInjectivity false
set_option linter.defProp false

namespace RelationalFoundations
universe u v w

structure ExactRealization (Role : Type u) (Occurrence : Type v)
    (Realizes : Role → Occurrence → Type w) where
  transport : ExactTransport Role Occurrence
  agreement : (role : Role) → Realizes role (transport.forward role)

namespace ExactRealization
variable {Role : Type u} {Occurrence : Type v} {Realizes : Role → Occurrence → Type w}

def inverseAgreement (e : ExactRealization Role Occurrence Realizes)
    (o : Occurrence) : Realizes (e.transport.backward o) o :=
  Eq.mp (congrArg (Realizes (e.transport.backward o)) (e.transport.backwardForward o))
    (e.agreement (e.transport.backward o))

theorem forward_injective (e : ExactRealization Role Occurrence Realizes) :
    Function.Injective e.transport.forward := by
  intro a b eq
  exact (e.transport.forwardBackward a).symm.trans
    ((congrArg e.transport.backward eq).trans (e.transport.forwardBackward b))

theorem backward_injective (e : ExactRealization Role Occurrence Realizes) :
    Function.Injective e.transport.backward := by
  intro a b eq
  exact (e.transport.backwardForward a).symm.trans
    ((congrArg e.transport.forward eq).trans (e.transport.backwardForward b))

def RoleRigid (e : ExactRealization Role Occurrence Realizes) : Prop :=
  ∀ r o, Realizes r o → r = e.transport.backward o

def OccurrenceRigid (e : ExactRealization Role Occurrence Realizes) : Prop :=
  ∀ r o, Realizes r o → o = e.transport.forward r

theorem roleRigid_iff_occurrenceRigid (e : ExactRealization Role Occurrence Realizes) :
    e.RoleRigid ↔ e.OccurrenceRigid := by
  constructor
  · intro rigid r o w
    exact (e.transport.backwardForward o).symm.trans
      (congrArg e.transport.forward (rigid r o w).symm)
  · intro rigid r o w
    exact (e.transport.forwardBackward r).symm.trans
      (congrArg e.transport.backward (rigid r o w).symm)

end ExactRealization
end RelationalFoundations
