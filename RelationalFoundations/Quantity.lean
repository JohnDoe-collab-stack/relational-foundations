import RelationalFoundations.ExactRealization
import RelationalFoundations.Signature
set_option genInjectivity false

namespace RelationalFoundations
universe u v w

set_option linter.checkUnivs false in
structure StructuralQuantity where
  Role : Type u
  Occurrence : Type v
  Realizes : Role → Occurrence → Type w
  exact : ExactRealization Role Occurrence Realizes

namespace StructuralQuantity

abbrev Witness (q : StructuralQuantity.{u,v,w}) := Σ r : q.Role, Σ o : q.Occurrence, q.Realizes r o

def distinguished (q : StructuralQuantity.{u,v,w}) (r : q.Role) : q.Witness :=
  ⟨r, q.exact.transport.forward r, q.exact.agreement r⟩

end StructuralQuantity

/-- Total witness transports retain all relation witnesses, not only the selected realization. -/
structure ConstitutiveEquiv (first second : StructuralQuantity.{u,v,w}) where
  roles : ExactTransport first.Role second.Role
  occurrences : ExactTransport first.Occurrence second.Occurrence
  witnesses : ExactTransport first.Witness second.Witness
  roleExact : ∀ witness, roles.forward witness.1 = (witnesses.forward witness).1
  occurrenceExact : ∀ witness, occurrences.forward witness.2.1 = (witnesses.forward witness).2.1
  realizationExact : ∀ r,
    occurrences.forward (first.exact.transport.forward r) = second.exact.transport.forward (roles.forward r)
  distinguishedExact : ∀ r,
    witnesses.forward (first.distinguished r) = second.distinguished (roles.forward r)

namespace ConstitutiveEquiv
variable {a b c d : StructuralQuantity.{u,v,w}}

def identity (q : StructuralQuantity.{u,v,w}) : ConstitutiveEquiv q q where
  roles := .reflexive _
  occurrences := .reflexive _
  witnesses := .reflexive _
  roleExact := fun _ => rfl
  occurrenceExact := fun _ => rfl
  realizationExact := fun _ => rfl
  distinguishedExact := fun _ => rfl

theorem classificationExact (f : ConstitutiveEquiv a b) (o : a.Occurrence) :
    f.roles.forward (a.exact.transport.backward o) = b.exact.transport.backward (f.occurrences.forward o) := by
  exact (b.exact.transport.forwardBackward _).symm.trans
    ((congrArg b.exact.transport.backward
      (f.realizationExact (a.exact.transport.backward o)).symm).trans
      (congrArg (fun x => b.exact.transport.backward (f.occurrences.forward x))
        (a.exact.transport.backwardForward o)))

def inverse (f : ConstitutiveEquiv a b) : ConstitutiveEquiv b a where
  roles := f.roles.reverse
  occurrences := f.occurrences.reverse
  witnesses := f.witnesses.reverse
  roleExact := by
    intro witness
    have eq := f.roleExact (f.witnesses.backward witness)
    rw [f.witnesses.backwardForward] at eq
    exact (congrArg f.roles.backward eq).symm.trans (f.roles.forwardBackward _)
  occurrenceExact := by
    intro witness
    have eq := f.occurrenceExact (f.witnesses.backward witness)
    rw [f.witnesses.backwardForward] at eq
    exact (congrArg f.occurrences.backward eq).symm.trans (f.occurrences.forwardBackward _)
  realizationExact := by
    intro r
    have eq := f.realizationExact (f.roles.backward r)
    rw [f.roles.backwardForward] at eq
    exact (congrArg f.occurrences.backward eq).symm.trans (f.occurrences.forwardBackward _)
  distinguishedExact := by
    intro r
    have eq := f.distinguishedExact (f.roles.backward r)
    rw [f.roles.backwardForward] at eq
    exact (congrArg f.witnesses.backward eq).symm.trans (f.witnesses.forwardBackward _)

def compose (f : ConstitutiveEquiv a b) (g : ConstitutiveEquiv b c) : ConstitutiveEquiv a c where
  roles := f.roles.compose g.roles
  occurrences := f.occurrences.compose g.occurrences
  witnesses := f.witnesses.compose g.witnesses
  roleExact := fun witness =>
    (congrArg g.roles.forward (f.roleExact witness)).trans (g.roleExact (f.witnesses.forward witness))
  occurrenceExact := fun witness =>
    (congrArg g.occurrences.forward (f.occurrenceExact witness)).trans
      (g.occurrenceExact (f.witnesses.forward witness))
  realizationExact := fun r =>
    (congrArg g.occurrences.forward (f.realizationExact r)).trans (g.realizationExact (f.roles.forward r))
  distinguishedExact := fun r =>
    (congrArg g.witnesses.forward (f.distinguishedExact r)).trans (g.distinguishedExact (f.roles.forward r))

theorem compose_assoc_witness (f : ConstitutiveEquiv a b) (g : ConstitutiveEquiv b c)
    (h : ConstitutiveEquiv c d) (x : a.Witness) :
    ((f.compose g).compose h).witnesses.forward x =
      (f.compose (g.compose h)).witnesses.forward x := rfl

theorem inverse_witness_roundTrip (f : ConstitutiveEquiv a b) (x : a.Witness) :
    f.inverse.witnesses.forward (f.witnesses.forward x) = x := f.witnesses.forwardBackward x

end ConstitutiveEquiv

def ConstitutivelyEquivalent (first second : StructuralQuantity.{u,v,w}) : Prop :=
  Nonempty (ConstitutiveEquiv first second)

theorem constitutivelyEquivalent_refl (q : StructuralQuantity.{u,v,w}) : ConstitutivelyEquivalent q q :=
  ⟨.identity q⟩

theorem constitutivelyEquivalent_symm {a b : StructuralQuantity.{u,v,w}}
    (h : ConstitutivelyEquivalent a b) : ConstitutivelyEquivalent b a := by
  cases h with
  | intro f => exact ⟨f.inverse⟩

theorem constitutivelyEquivalent_trans {a b c : StructuralQuantity.{u,v,w}}
    (h : ConstitutivelyEquivalent a b) (k : ConstitutivelyEquivalent b c) :
    ConstitutivelyEquivalent a c := by
  cases h with
  | intro f => cases k with
    | intro g => exact ⟨f.compose g⟩

end RelationalFoundations
