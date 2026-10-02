import RelationalPerimeter.Computation.ConstitutiveSearch.SemanticImage

namespace SemanticImageRegression
open ConstitutiveSearch.SemanticImage

/-- An inhabited source domain with a nontrivial acceptance predicate. -/
def faithful : Description :=
  { Source := Bool
    Payload := fun _ => Bool
    Target := Bool
    Accept := fun _ payload => payload = true
    TargetAccept := fun target => target = true
    action := fun _ payload => payload
    canonical := fun _ => false
    produced := fun _ => false
    reflect := fun target => ⟨true, target⟩
    SourceInvariant := (false : Bool) ≠ true }

theorem faithfulSpecification : Specification faithful false :=
  certify faithful Bool.false_ne_true (fun _ => rfl)
    (fun _ _ accepted => accepted) (fun _ accepted => accepted) false

/-- A canonical sample alone cannot distinguish the correct action from a constant. -/
def prescribed : Description := { faithful with action := fun _ _ => false }

theorem sameCanonicalOutputs : ∀ source,
    prescribed.action source (prescribed.canonical source) = faithful.produced source :=
  fun _ => rfl

theorem prescribedLosesPreservation : ¬ Specification prescribed false := by
  intro specification
  have impossible : false = true := (specification.2.1 false rfl).2 true rfl
  exact Bool.noConfusion impossible

/-- Successful image convergence does not determine the source invariant. -/
def missingConstitution : Description := { faithful with SourceInvariant := False }

theorem missingConstitutionHasNoSpecification :
    ¬ Specification missingConstitution false := by
  intro specification
  exact specification.1

/-- The abstract consumer uses preservation with no concrete relation in scope. -/
theorem arbitraryPayloadPreserved (source payload : Bool) (accepted : payload = true) :
    (use faithfulSpecification source rfl payload).1 = true :=
  (use faithfulSpecification source rfl payload).2.2 accepted

theorem viabilityIsPreservedAndReflected :
    (∃ source payload, faithful.Accept source payload) ↔
      (∃ target, faithful.TargetAccept target) :=
  viable_iff faithful (fun _ => faithfulSpecification)

end SemanticImageRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms SemanticImageRegression.faithful
#print axioms SemanticImageRegression.faithfulSpecification
#print axioms SemanticImageRegression.prescribed
#print axioms SemanticImageRegression.sameCanonicalOutputs
#print axioms SemanticImageRegression.prescribedLosesPreservation
#print axioms SemanticImageRegression.missingConstitution
#print axioms SemanticImageRegression.missingConstitutionHasNoSpecification
#print axioms SemanticImageRegression.arbitraryPayloadPreserved
#print axioms SemanticImageRegression.viabilityIsPreservedAndReflected
/- AXIOM_AUDIT_END -/
