import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredComparison

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

/-- The returned data, correctness evidence and work share one executable run. -/
structure MeasuredValue {α : Type} (expected : α) where
  value : α
  valueExact : value = expected
  work : ComparisonWork

def flipMeasuredLiteral (selected : Var) :
    (literal : Literal) → MeasuredValue (Literal.flipAt selected literal)
  | .positive label =>
    let labels := compareUnary label selected
    match labels.result with
    | .isTrue same =>
      ⟨.negative label, by rw [Literal.flipAt, if_pos same], labels.work.visit⟩
    | .isFalse different =>
      ⟨.positive label, by rw [Literal.flipAt, if_neg different], labels.work.visit⟩
  | .negative label =>
    let labels := compareUnary label selected
    match labels.result with
    | .isTrue same =>
      ⟨.positive label, by rw [Literal.flipAt, if_pos same], labels.work.visit⟩
    | .isFalse different =>
      ⟨.negative label, by rw [Literal.flipAt, if_neg different], labels.work.visit⟩

def flipMeasuredClause (selected : Var) :
    (clause : Clause) → MeasuredValue (Clause.flipAt selected clause)
  | [] => ⟨[], rfl, ⟨1, 0⟩⟩
  | literal :: rest =>
    let head := flipMeasuredLiteral selected literal
    let tail := flipMeasuredClause selected rest
    ⟨head.value :: tail.value, by rw [head.valueExact, tail.valueExact]; rfl,
      (head.work.add tail.work).visit⟩

def flipMeasuredCnf (selected : Var) :
    (formula : Cnf) → MeasuredValue (Cnf.flipAt selected formula)
  | [] => ⟨[], rfl, ⟨1, 0⟩⟩
  | clause :: rest =>
    let head := flipMeasuredClause selected clause
    let tail := flipMeasuredCnf selected rest
    ⟨head.value :: tail.value, by rw [head.valueExact, tail.valueExact]; rfl,
      (head.work.add tail.work).visit⟩

def flipMeasuredDecision (selected : Var) (decision : StructuralBranchDecision) :
    MeasuredValue (StructuralBranchDecision.flipAt selected decision) :=
  let labels := compareUnary decision.var selected
  match labels.result with
  | .isTrue same =>
    ⟨⟨decision.var, !decision.value⟩,
      by rw [StructuralBranchDecision.flipAt, if_pos same], labels.work.visit⟩
  | .isFalse different =>
    ⟨decision, by rw [StructuralBranchDecision.flipAt, if_neg different],
      labels.work.visit⟩

def flipMeasuredHistory (selected : Var) :
    (history : List StructuralBranchDecision) →
      MeasuredValue (flipStructuralDecisionsAt selected history)
  | [] => ⟨[], rfl, ⟨1, 0⟩⟩
  | decision :: rest =>
    let head := flipMeasuredDecision selected decision
    let tail := flipMeasuredHistory selected rest
    ⟨head.value :: tail.value, by rw [head.valueExact, tail.valueExact]; rfl,
      (head.work.add tail.work).visit⟩

def checkMeasuredFreshness (selected : Var) :
    (history : List StructuralBranchDecision) →
      MeasuredValue (structuralDecisionsAvoidCheck selected history)
  | [] => ⟨true, rfl, ⟨1, 0⟩⟩
  | decision :: rest =>
    let labels := compareUnary decision.var selected
    match labels.result with
    | .isTrue same =>
      ⟨false, by rw [structuralDecisionsAvoidCheck, if_pos same], labels.work.visit⟩
    | .isFalse different =>
      let tail := checkMeasuredFreshness selected rest
      ⟨tail.value, by
        rw [tail.valueExact, structuralDecisionsAvoidCheck, if_neg different],
        (labels.work.add tail.work).visit⟩

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredLiteral
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredClause
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredCnf
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.flipMeasuredHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.checkMeasuredFreshness
/- AXIOM_AUDIT_END -/
