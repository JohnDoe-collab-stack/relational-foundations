import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredStateConstruction

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- Charge each constructor emitted by the recursive decoy-clause producer. -/
def constructMeasuredDecoyClause : (count : Nat) → MeasuredValue (distinctDecoyClause count)
  | 0 => ⟨[], rfl, ⟨1, 0⟩⟩
  | count + 1 =>
    let tail := constructMeasuredDecoyClause count
    ⟨Literal.positive count :: tail.value,
      congrArg (List.cons (Literal.positive count)) tail.valueExact,
      tail.work.visit.visit⟩

def measuredEmptyList {α : Type} : MeasuredValue ([] : List α) := ⟨[], rfl, ⟨1, 0⟩⟩

def measuredCons {α : Type} {head : α} {tail : List α}
    (producedHead : MeasuredValue head) (producedTail : MeasuredValue tail) :
    MeasuredValue (head :: tail) :=
  ⟨producedHead.value :: producedTail.value,
    by rw [producedHead.valueExact, producedTail.valueExact],
    (producedHead.work.add producedTail.work).visit⟩

def measuredLiteral (literal : Literal) : MeasuredValue literal := ⟨literal, rfl, ⟨1, 0⟩⟩

/-- Emit each literal/list constructor, including the CNF terminator.
These are constructor units, not a claim to measure label arithmetic. -/
def constructMeasuredFormula (index : Nat) : MeasuredValue (distinctGrowingDiscoveryFormula index) :=
  let decoys := constructMeasuredDecoyClause (index + 1)
  let selected := growingDiscoverySplitVar index
  let anchor := growingDiscoveryAnchorVar index
  let positive := measuredCons (measuredLiteral (.positive selected))
    (measuredCons (measuredLiteral (.positive anchor)) measuredEmptyList)
  let negative := measuredCons (measuredLiteral (.negative selected))
    (measuredCons (measuredLiteral (.positive anchor)) measuredEmptyList)
  measuredCons decoys (measuredCons positive (measuredCons negative measuredEmptyList))

/-- Root construction consumes the formula just produced, then reindexes its type. -/
def constructMeasuredOperationalRoot (index : Nat) :
    MeasuredValue (distinctGrowingDiscoveryRoot index) :=
  let formula := constructMeasuredFormula index
  let root := GeneratedStructuralBranchContext.root formula.value
  let indexed := Eq.rec (motive := fun formula _ => GeneratedStructuralBranchContext formula)
    root formula.valueExact
  ⟨indexed, by
    dsimp only [indexed, root]
    cases formula with
    | mk value same work => cases same; rfl,
    formula.work.visit⟩

theorem constructMeasuredDecoyClause_work (count : Nat) :
    (constructMeasuredDecoyClause count).work.total = 2 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (constructMeasuredDecoyClause count).work.nodes + 1 + 1 +
      (constructMeasuredDecoyClause count).work.labelSteps = _
    have shift : ∀ a b : Nat, a + 1 + 1 + b = (a + b) + 2 := by
      intro a b
      rw [Nat.add_assoc a 1 1, Nat.add_assoc, Nat.add_comm 2 b, ← Nat.add_assoc]
    rw [shift]
    change (constructMeasuredDecoyClause count).work.total + 2 = _
    rw [ih, Nat.mul_succ]

theorem constructMeasuredFormula_work (index : Nat) :
    (constructMeasuredFormula index).work.total = 2 * (index + 1) + 15 := by
  change ((constructMeasuredDecoyClause (index + 1)).work.add ⟨13, 0⟩).visit.total = _
  rw [ComparisonWork.total_visit, ComparisonWork.total_add, constructMeasuredDecoyClause_work]
  rfl

theorem constructMeasuredOperationalRoot_work (index : Nat) :
    (constructMeasuredOperationalRoot index).work.total = 2 * (index + 1) + 16 := by
  change (constructMeasuredFormula index).work.visit.total = _
  rw [ComparisonWork.total_visit, constructMeasuredFormula_work]

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredEmptyList
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredCons
#print axioms ConstitutiveSearch.EndogenousDecomposition.measuredLiteral
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredDecoyClause
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredFormula
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredOperationalRoot
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredDecoyClause_work
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredFormula_work
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredOperationalRoot_work
/- AXIOM_AUDIT_END -/
