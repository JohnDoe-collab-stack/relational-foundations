import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ParametricSymmetricFamily

/-!
# Structural families used by growing endogenous discovery

This module owns only the formulas and generated roots. It contains no
discovery run, counter, benchmark statistic, or complexity conclusion. The
foundation-to-search raccord can therefore construct its operational state
without importing later discovery instrumentation.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Put `count` copies of one value in front of a supplied tail. -/
def copiesBefore {α : Type} : Nat → α → List α → List α
  | 0, _value, tail => tail
  | count + 1, value, tail => value :: copiesBefore count value tail

/-- One nonempty syntactic clause containing only the decoy variable. -/
def growingDiscoveryDecoyClause (input : Nat) : Clause :=
  copiesBefore (input + 1) (Literal.positive 0) []

/-- The useful variable varies with the input and is never the decoy `0`. -/
def growingDiscoverySplitVar (input : Nat) : Var :=
  input + 2

/-- A separate anchor for the useful symmetric block. -/
def growingDiscoveryAnchorVar (input : Nat) : Var :=
  input + 3

/-- Decoy prefix followed by the useful flip-symmetric block. -/
def growingDiscoveryFormula (input : Nat) : Cnf :=
  growingDiscoveryDecoyClause input ::
    symmetricBlockFamily
      (growingDiscoverySplitVar input)
      (growingDiscoveryAnchorVar input)
      []

/-- Root state consumed by the ordinary endogenous discovery engine. -/
def growingDiscoveryRoot
    (input : Nat) :
    GeneratedStructuralBranchContext (growingDiscoveryFormula input) :=
  GeneratedStructuralBranchContext.root (growingDiscoveryFormula input)

/-- Descending list `count - 1, ..., 0` of pairwise distinct decoy variables. -/
def distinctDecoyVariables : Nat → List Var
  | 0 => []
  | count + 1 => count :: distinctDecoyVariables count

/-- One positive-literal clause carrying exactly the distinct decoy variables. -/
def distinctDecoyClause : Nat → Clause
  | 0 => []
  | count + 1 => Literal.positive count :: distinctDecoyClause count

/-- Strong formula: distinct decoy variables precede the useful symmetric block. -/
def distinctGrowingDiscoveryFormula (input : Nat) : Cnf :=
  distinctDecoyClause (input + 1) ::
    symmetricBlockFamily
      (growingDiscoverySplitVar input)
      (growingDiscoveryAnchorVar input)
      []

/-- Generated root of the distinct-decoy family. -/
def distinctGrowingDiscoveryRoot
    (input : Nat) :
    GeneratedStructuralBranchContext (distinctGrowingDiscoveryFormula input) :=
  GeneratedStructuralBranchContext.root (distinctGrowingDiscoveryFormula input)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.copiesBefore
#print axioms ConstitutiveSearch.SAT.growingDiscoveryDecoyClause
#print axioms ConstitutiveSearch.SAT.growingDiscoverySplitVar
#print axioms ConstitutiveSearch.SAT.growingDiscoveryAnchorVar
#print axioms ConstitutiveSearch.SAT.growingDiscoveryFormula
#print axioms ConstitutiveSearch.SAT.growingDiscoveryRoot
#print axioms ConstitutiveSearch.SAT.distinctDecoyVariables
#print axioms ConstitutiveSearch.SAT.distinctDecoyClause
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryFormula
#print axioms ConstitutiveSearch.SAT.distinctGrowingDiscoveryRoot
/- AXIOM_AUDIT_END -/
