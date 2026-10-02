import RelationalFoundations.Quantity
set_option genInjectivity false

namespace RelationalFoundations
universe u v w x

namespace ExactTransport
variable {A : Type u} {B : Type v}

theorem forward_injective (f : ExactTransport A B) : Function.Injective f.forward := by
  intro a b eq
  exact (f.forwardBackward a).symm.trans ((congrArg f.backward eq).trans (f.forwardBackward b))

def restrict (f : ExactTransport A B) (P : A → Prop) (Q : B → Prop)
    (agreement : ∀ a, P a ↔ Q (f.forward a)) :
    ExactTransport {a // P a} {b // Q b} where
  forward := fun a => ⟨f.forward a.val, (agreement a.val).mp a.property⟩
  backward := fun b => ⟨f.backward b.val, (agreement _).mpr (by
    rw [f.backwardForward]; exact b.property)⟩
  forwardBackward := fun a => Subtype.ext (f.forwardBackward a.val)
  backwardForward := fun b => Subtype.ext (f.backwardForward b.val)

end ExactTransport

namespace StructuralQuantity

abbrev Fiber (q : StructuralQuantity.{u,v,w}) (r : q.Role) (o : q.Occurrence) :=
  {w : q.Witness // w.1 = r ∧ w.2.1 = o}

def fiberValue (q : StructuralQuantity.{u,v,w}) (r : q.Role) (o : q.Occurrence)
    (w : q.Fiber r o) : q.Realizes r o := by
  rcases w with ⟨⟨r', o', witness⟩, roleEq, occurrenceEq⟩
  cases roleEq
  cases occurrenceEq
  exact witness

def realizesFiber (q : StructuralQuantity.{u,v,w}) (r : q.Role) (o : q.Occurrence) :
    ExactTransport (q.Realizes r o) (q.Fiber r o) where
  forward := fun witness => ⟨⟨r, o, witness⟩, rfl, rfl⟩
  backward := q.fiberValue r o
  forwardBackward := fun _ => rfl
  backwardForward := by
    intro witness
    rcases witness with ⟨⟨r', o', witness⟩, roleEq, occurrenceEq⟩
    cases roleEq
    cases occurrenceEq
    rfl

theorem distinguishedFiber_value (q : StructuralQuantity.{u,v,w}) {r : q.Role} {o : q.Occurrence}
    (occurrenceExact : o = q.exact.transport.forward r) (witness : q.Fiber r o)
    (witnessExact : witness.val = q.distinguished r) :
    Eq.mp (congrArg (q.Realizes r) occurrenceExact) (q.fiberValue r o witness) = q.exact.agreement r := by
  cases occurrenceExact
  have eq : witness = ⟨q.distinguished r, rfl, rfl⟩ := Subtype.ext witnessExact
  cases eq
  rfl

end StructuralQuantity

namespace ConstitutiveEquiv
variable {a b : StructuralQuantity.{u,v,w}}

def witnessFiber (f : ConstitutiveEquiv a b) (r : a.Role) (o : a.Occurrence) :
    ExactTransport (a.Fiber r o) (b.Fiber (f.roles.forward r) (f.occurrences.forward o)) :=
  f.witnesses.restrict (fun w => w.1 = r ∧ w.2.1 = o)
    (fun w => w.1 = f.roles.forward r ∧ w.2.1 = f.occurrences.forward o) (by
      intro witness
      constructor
      · intro eq
        exact ⟨(f.roleExact witness).symm.trans (congrArg f.roles.forward eq.1),
          (f.occurrenceExact witness).symm.trans (congrArg f.occurrences.forward eq.2)⟩
      · intro eq
        exact ⟨f.roles.forward_injective ((f.roleExact witness).trans eq.1),
          f.occurrences.forward_injective ((f.occurrenceExact witness).trans eq.2)⟩)

/-- Genuine reversible realization-fiber transport, derived from the equipped total map. -/
def realizesFiber (f : ConstitutiveEquiv a b) (r : a.Role) (o : a.Occurrence) :
    ExactTransport (a.Realizes r o) (b.Realizes (f.roles.forward r) (f.occurrences.forward o)) :=
  ((a.realizesFiber r o).compose (f.witnessFiber r o)).compose
    (b.realizesFiber (f.roles.forward r) (f.occurrences.forward o)).reverse

theorem coherence_distinguished_fiber (f : ConstitutiveEquiv a b) (r : a.Role) :
    Eq.mp (congrArg (b.Realizes (f.roles.forward r)) (f.realizationExact r))
      ((f.realizesFiber r (a.exact.transport.forward r)).forward (a.exact.agreement r)) =
        b.exact.agreement (f.roles.forward r) :=
  b.distinguishedFiber_value (f.realizationExact r)
    ((f.witnessFiber r (a.exact.transport.forward r)).forward
      ((a.realizesFiber r (a.exact.transport.forward r)).forward (a.exact.agreement r)))
    (f.distinguishedExact r)

end ConstitutiveEquiv
end RelationalFoundations
