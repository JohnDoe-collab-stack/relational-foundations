import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierPreservation
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ConstraintTransport

/-!
# SAT with structural assignments and explicit acceptance

This module instantiates the hardened search semantics on CNF SAT.

Every total Boolean assignment is a structural continuation.  Satisfaction is
only the acceptance predicate.  Structural transforms must therefore act on
assignments independently of whether those assignments satisfy the source.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Hardened SAT search semantics: all assignments are continuations. -/
def satSystem : SearchSystem :=
  { State := Cnf
    Continuation := fun _formula => Assignment
    Accept := fun formula assignment =>
      Satisfies assignment formula }

namespace CnfWeakening

/--
CNF weakening acts on every assignment by identity and preserves acceptance
when the source assignment is satisfying.
-/
def toAcceptingTransport
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    AcceptingContinuationTransport
      satSystem
      source
      target :=
  { map := fun assignment => assignment
    preservesAccept := by
      intro assignment accepted
      exact weakening.preservesSatisfaction accepted }

/-- Weakening preserves SAT viability without deciding it. -/
theorem preservesViable
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    satSystem.Viable source →
      satSystem.Viable target :=
  weakening.toAcceptingTransport.preservesViable

end CnfWeakening

/-- Absorb a stronger CNF into an explicitly weaker CNF inside a frontier. -/
def absorbByWeakening
    {source target : Cnf}
    {rest : List Cnf}
    (weakening : CnfWeakening source target) :
    AcceptedFrontierPreservation
      satSystem
      (source :: target :: rest)
      (target :: rest) :=
  AcceptedFrontierPreservation.absorbFirstIntoSecond
    weakening.toAcceptingTransport

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.satSystem
#print axioms ConstitutiveSearch.SAT.CnfWeakening.toAcceptingTransport
#print axioms ConstitutiveSearch.SAT.CnfWeakening.preservesViable
#print axioms ConstitutiveSearch.SAT.absorbByWeakening
/- AXIOM_AUDIT_END -/
