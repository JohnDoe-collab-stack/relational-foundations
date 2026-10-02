set_option genInjectivity false
namespace RelationalFoundations
/-!
# Constructive exact transports

An exact transport consists of two explicitly supplied maps with pointwise
round trips.  It is independent of any particular constitution, realization,
admission regime, specification, or readout.
-/


universe uSource uMiddle uTarget

structure ExactTransport
    (Source : Type uSource)
    (Target : Type uTarget) where
  forward : Source → Target
  backward : Target → Source
  forwardBackward : (source : Source) → backward (forward source) = source
  backwardForward : (target : Target) → forward (backward target) = target

namespace ExactTransport

def reflexive
    (Carrier : Type uSource) : ExactTransport Carrier Carrier :=
  { forward := id
    backward := id
    forwardBackward := fun _ => rfl
    backwardForward := fun _ => rfl }

def ofEquality
    {Source Target : Type uSource}
    (equality : Source = Target) : ExactTransport Source Target := by
  cases equality
  exact reflexive Source

/-- Reverse an exact transport. -/
def reverse
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTransport Source Target) :
    ExactTransport Target Source :=
  { forward := transport.backward
    backward := transport.forward
    forwardBackward := transport.backwardForward
    backwardForward := transport.forwardBackward }

/-- Compose exact transports without any choice principle. -/
def compose
    {Source : Type uSource}
    {Middle : Type uMiddle}
    {Target : Type uTarget}
    (first : ExactTransport Source Middle)
    (second : ExactTransport Middle Target) :
    ExactTransport Source Target :=
  { forward := fun source => second.forward (first.forward source)
    backward := fun target => first.backward (second.backward target)
    forwardBackward := by
      intro source
      change
        first.backward (second.backward (second.forward (first.forward source))) =
          source
      rw [second.forwardBackward, first.forwardBackward]
    backwardForward := by
      intro target
      change
        second.forward (first.forward (first.backward (second.backward target))) =
          target
      rw [first.backwardForward, second.backwardForward] }

/-- Extend an exact transport by the unchanged one-point residual. -/
def sumUnit
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTransport Source Target) :
    ExactTransport (Source ⊕ Unit) (Target ⊕ Unit) :=
  { forward := fun value =>
      match value with
      | .inl source => .inl (transport.forward source)
      | .inr _ => .inr ()
    backward := fun value =>
      match value with
      | .inl target => .inl (transport.backward target)
      | .inr _ => .inr ()
    forwardBackward := by
      intro value
      cases value with
      | inl source =>
          change Sum.inl (transport.backward (transport.forward source)) =
            Sum.inl source
          rw [transport.forwardBackward]
      | inr witness => cases witness; rfl
    backwardForward := by
      intro value
      cases value with
      | inl target =>
          change Sum.inl (transport.forward (transport.backward target)) =
            Sum.inl target
          rw [transport.backwardForward]
      | inr witness => cases witness; rfl }

/-- Pointwise agreement of exact forward maps determines their backward maps. -/
theorem backward_eq_of_forward_eq
    {Source : Type uSource}
    {Target : Type uTarget}
    (first second : ExactTransport Source Target)
    (forwardAgreement :
      (source : Source) → first.forward source = second.forward source)
    (target : Target) :
    first.backward target = second.backward target := by
  calc
    first.backward target =
      first.backward (second.forward (second.backward target)) := by
        rw [second.backwardForward]
    _ = first.backward (first.forward (second.backward target)) := by
        rw [forwardAgreement (second.backward target)]
    _ = second.backward target := first.forwardBackward _

end ExactTransport

/- AXIOM_AUDIT_BEGIN -/
#print axioms ExactTransport
#print axioms ExactTransport.reflexive
#print axioms ExactTransport.ofEquality
#print axioms ExactTransport.reverse
#print axioms ExactTransport.compose
#print axioms ExactTransport.sumUnit
#print axioms ExactTransport.backward_eq_of_forward_eq
/- AXIOM_AUDIT_END -/

end RelationalFoundations
