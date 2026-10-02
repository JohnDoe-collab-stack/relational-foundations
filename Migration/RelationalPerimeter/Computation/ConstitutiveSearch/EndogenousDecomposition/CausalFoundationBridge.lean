import RelationalPerimeter.Computation.ConstitutiveGeneration
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-!
# Causal foundation bridge

This is the unique typed bridge from the relational foundation and its free
generation to the semantic state consumed by causal execution.  It joins a
constituted history to an operational SAT state without identifying them and
defines the two generated occurrences of one structural opening.  It contains
no execution history, role history, profile, width, program, or diagnostic
projection.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open StrongPerimetralTurning
open StrongPerimetralTurning.Example

/--
The semantic state passed from one executed opening to the next.  Its
constitutive history and its operational state remain different fields; no
numeric readout is allowed to stand in for either of them.
-/
structure CausalConstitutiveState where
  constitutedHistory : RootedGeneratedHistory examplePresentation
  rootFormula : Cnf
  operationalState : GeneratedStructuralBranchContext rootFormula
  assignment : Assignment
  searchSeed : Nat
  decisions : List StructuralBranchDecision
  provenance : List Var
  provenanceExact :
    provenance = decisions.map (fun decision => decision.var)

/-- Left occurrence produced by opening one causal state. -/
def causalOpeningLeft
    (source : CausalConstitutiveState)
    (selected : Var)
    (fresh :
      StructuralDecisionsAvoid selected source.operationalState.context.decisions) :
    GeneratedStructuralBranchContext source.rootFormula :=
  source.operationalState.child selected false fresh

/-- Right occurrence produced by the same opening. -/
def causalOpeningRight
    (source : CausalConstitutiveState)
    (selected : Var)
    (fresh :
      StructuralDecisionsAvoid selected source.operationalState.context.decisions) :
    GeneratedStructuralBranchContext source.rootFormula :=
  source.operationalState.child selected true fresh

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveState
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOpeningLeft
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOpeningRight
/- AXIOM_AUDIT_END -/
