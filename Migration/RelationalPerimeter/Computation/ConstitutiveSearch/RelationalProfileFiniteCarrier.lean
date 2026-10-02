import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileConstitution
import RelationalPerimeter.Computation.ConstitutiveSearch.FiniteExtensiveAddressing

/-!
# Finite carrier of constituted relational profiles

This module is the unique passage from the relational profile stratum to the
finite extensive interface. It packages the already constituted occurrence
profiles and their already derived frontier; it introduces no new identity and
no independent enumeration.
-/

namespace ConstitutiveSearch
namespace RelationalExtensive

open Extensive

/-- The finite extensive carrier derived from one relational history. -/
def relationalProfileFiniteCarrier
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) :
    FiniteCarrier :=
  { Identity := RelationalOccurrenceProfile history
    decEq := relationalOccurrenceProfileDecEq history
    frontier := relationalProfileFrontier history
    complete := relationalProfileFrontier_complete history
    nodup := relationalProfileFrontier_nodup history }

/-- The finite carrier and its numerical readout share the same frontier. -/
theorem relationalProfileFiniteCarrier_width
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) :
    (relationalProfileFiniteCarrier history).frontier.length =
      relationalProfileWidth history :=
  rfl

end RelationalExtensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFiniteCarrier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFiniteCarrier_width
/- AXIOM_AUDIT_END -/
