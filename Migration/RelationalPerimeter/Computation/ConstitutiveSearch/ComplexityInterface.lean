/-!
# Conditional complexity accounting

This module does not assign machine costs to abstract search operations.
Instead it separates:

* certified event counts;
* declared atomic costs for those event classes;
* the charged aggregate cost obtained by multiplication.

A later concrete representation theorem may justify particular atomic-cost
bounds.  Until then, this interface is deliberately conditional.
-/

namespace ConstitutiveSearch

/-- Source-level event counts relevant to one complete search execution. -/
structure ComplexityCounts where
  syntaxUnits : Nat
  frontierSlots : Nat
  provenanceUnits : Nat
  certificateAtoms : Nat
  relationFindCalls : Nat
  closurePrimitiveQueries : Nat
  closureCompositionCandidates : Nat
  terminalChecks : Nat

/-- Declared cost charged to one event of each class. -/
structure AtomicCosts where
  syntaxUnit : Nat
  frontierSlot : Nat
  provenanceUnit : Nat
  certificateAtom : Nat
  relationFindCall : Nat
  closurePrimitiveQuery : Nat
  closureCompositionCandidate : Nat
  terminalCheck : Nat

/-- Aggregate charged cost under the declared atomic-cost model. -/
def chargedCost
    (counts : ComplexityCounts)
    (costs : AtomicCosts) : Nat :=
  counts.syntaxUnits * costs.syntaxUnit +
    (counts.frontierSlots * costs.frontierSlot +
      (counts.provenanceUnits * costs.provenanceUnit +
        (counts.certificateAtoms * costs.certificateAtom +
          (counts.relationFindCalls * costs.relationFindCall +
            (counts.closurePrimitiveQueries * costs.closurePrimitiveQuery +
              (counts.closureCompositionCandidates *
                  costs.closureCompositionCandidate +
                counts.terminalChecks * costs.terminalCheck))))))

/--
Uniform budget with the same structural shape as chargedCost.

Keeping the sum expanded avoids silently assuming any closed-form arithmetic
identity or representation model.
-/
def uniformChargedBudget
    (counts : ComplexityCounts)
    (unitBound : Nat) : Nat :=
  counts.syntaxUnits * unitBound +
    (counts.frontierSlots * unitBound +
      (counts.provenanceUnits * unitBound +
        (counts.certificateAtoms * unitBound +
          (counts.relationFindCalls * unitBound +
            (counts.closurePrimitiveQueries * unitBound +
              (counts.closureCompositionCandidates * unitBound +
                counts.terminalChecks * unitBound))))))

/--
If every atomic event costs at most unitBound, the complete charged cost is
bounded by the corresponding uniform structural budget.
-/
theorem chargedCost_le_uniform
    (counts : ComplexityCounts)
    (costs : AtomicCosts)
    (unitBound : Nat)
    (syntaxLe :
      costs.syntaxUnit ≤ unitBound)
    (frontierLe :
      costs.frontierSlot ≤ unitBound)
    (provenanceLe :
      costs.provenanceUnit ≤ unitBound)
    (certificateLe :
      costs.certificateAtom ≤ unitBound)
    (relationLe :
      costs.relationFindCall ≤ unitBound)
    (closurePrimitiveLe :
      costs.closurePrimitiveQuery ≤ unitBound)
    (closureCandidateLe :
      costs.closureCompositionCandidate ≤ unitBound)
    (terminalLe :
      costs.terminalCheck ≤ unitBound) :
    chargedCost counts costs ≤
      uniformChargedBudget counts unitBound := by
  unfold chargedCost uniformChargedBudget
  exact
    Nat.add_le_add
      (Nat.mul_le_mul_left
        counts.syntaxUnits
        syntaxLe)
      (Nat.add_le_add
        (Nat.mul_le_mul_left
          counts.frontierSlots
          frontierLe)
        (Nat.add_le_add
          (Nat.mul_le_mul_left
            counts.provenanceUnits
            provenanceLe)
          (Nat.add_le_add
            (Nat.mul_le_mul_left
              counts.certificateAtoms
              certificateLe)
            (Nat.add_le_add
              (Nat.mul_le_mul_left
                counts.relationFindCalls
                relationLe)
              (Nat.add_le_add
                (Nat.mul_le_mul_left
                  counts.closurePrimitiveQueries
                  closurePrimitiveLe)
                (Nat.add_le_add
                  (Nat.mul_le_mul_left
                    counts.closureCompositionCandidates
                    closureCandidateLe)
                  (Nat.mul_le_mul_left
                    counts.terminalChecks
                    terminalLe)))))))

/--
A cost model whose every event is bounded by the same explicit envelope.
-/
structure UniformAtomicBound
    (costs : AtomicCosts)
    (unitBound : Nat) : Prop where
  syntaxLe :
    costs.syntaxUnit ≤ unitBound
  frontierLe :
    costs.frontierSlot ≤ unitBound
  provenanceLe :
    costs.provenanceUnit ≤ unitBound
  certificateLe :
    costs.certificateAtom ≤ unitBound
  relationLe :
    costs.relationFindCall ≤ unitBound
  closurePrimitiveLe :
    costs.closurePrimitiveQuery ≤ unitBound
  closureCandidateLe :
    costs.closureCompositionCandidate ≤ unitBound
  terminalLe :
    costs.terminalCheck ≤ unitBound

/-- Packaged form of the conditional aggregate-cost theorem. -/
theorem chargedCost_le_of_uniformBound
    (counts : ComplexityCounts)
    (costs : AtomicCosts)
    (unitBound : Nat)
    (bounded :
      UniformAtomicBound costs unitBound) :
    chargedCost counts costs ≤
      uniformChargedBudget counts unitBound :=
  chargedCost_le_uniform
    counts
    costs
    unitBound
    bounded.syntaxLe
    bounded.frontierLe
    bounded.provenanceLe
    bounded.certificateLe
    bounded.relationLe
    bounded.closurePrimitiveLe
    bounded.closureCandidateLe
    bounded.terminalLe

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ComplexityCounts
#print axioms ConstitutiveSearch.AtomicCosts
#print axioms ConstitutiveSearch.chargedCost
#print axioms ConstitutiveSearch.uniformChargedBudget
#print axioms ConstitutiveSearch.chargedCost_le_uniform
#print axioms ConstitutiveSearch.UniformAtomicBound
#print axioms ConstitutiveSearch.chargedCost_le_of_uniformBound
/- AXIOM_AUDIT_END -/
