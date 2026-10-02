import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredTransformation

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

def containsMeasuredLiteral (target : Literal) :
    (clause : Clause) → MeasuredValue (Clause.containsLiteral target clause)
  | [] => ⟨false, rfl, ⟨1, 0⟩⟩
  | literal :: rest =>
    let compared := compareMeasuredLiteral literal target
    match compared.result with
    | .isTrue same =>
      ⟨true, by rw [Clause.containsLiteral, if_pos same], compared.work.visit⟩
    | .isFalse different =>
      let tail := containsMeasuredLiteral target rest
      ⟨tail.value, by rw [Clause.containsLiteral, if_neg different, tail.valueExact],
        (compared.work.add tail.work).visit⟩

def constructMeasuredResidual (selected : Var) (value : Bool) :
    (formula : Cnf) → MeasuredValue (branchResidual formula selected value)
  | [] => ⟨[], rfl, ⟨1, 0⟩⟩
  | clause :: rest =>
    let tail := constructMeasuredResidual selected value rest
    let contains := containsMeasuredLiteral (Literal.forValue selected value) clause
    match found : contains.value with
    | true =>
      ⟨tail.value, by
        rw [branchResidual_cons_hit clause rest selected value
          (Eq.trans contains.valueExact.symm found)]
        exact tail.valueExact,
        (tail.work.add contains.work).visit⟩
    | false =>
      ⟨clause :: tail.value, by
        rw [branchResidual_cons_miss clause rest selected value
          (Eq.trans contains.valueExact.symm found)]
        exact congrArg (List.cons clause) tail.valueExact,
        (tail.work.add contains.work).visit⟩

/-- Construct the child data from the residual actually returned by the run. -/
def childFromMeasuredResidual {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) (selected : Var) (value : Bool)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (residual : MeasuredValue (branchResidual parent.context.formula selected value)) :
    GeneratedStructuralBranchContext root :=
  let context : StructuralBranchContext :=
    ⟨residual.value, ⟨selected, value⟩ :: parent.context.decisions⟩
  have contextExact : context = structuralChildContext parent.context selected value := by
    change StructuralBranchContext.mk residual.value _ = _
    rw [residual.valueExact]
    rfl
  let generated : StructuralGeneratedFrom root context :=
    Eq.rec (motive := fun context _ => StructuralGeneratedFrom root context)
      (.child parent.generated selected value fresh) contextExact.symm
  ⟨context, generated⟩

theorem childFromMeasuredResidual_exact {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) (selected : Var) (value : Bool)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions)
    (residual : MeasuredValue (branchResidual parent.context.formula selected value)) :
    childFromMeasuredResidual parent selected value fresh residual = parent.child selected value fresh := by
  cases residual with
  | mk residual exact work =>
    cases exact
    rfl

def constructMeasuredChild {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) (selected : Var) (value : Bool)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    MeasuredValue (parent.child selected value fresh) :=
  let residual := constructMeasuredResidual selected value parent.context.formula
  { value := childFromMeasuredResidual parent selected value fresh residual
    valueExact := childFromMeasuredResidual_exact parent selected value fresh residual
    work := residual.work.visit }

theorem constructMeasuredChild_consumes_residual {root : Cnf}
    (parent : GeneratedStructuralBranchContext root) (selected : Var) (value : Bool)
    (fresh : StructuralDecisionsAvoid selected parent.context.decisions) :
    (constructMeasuredChild parent selected value fresh).value.context.formula =
      (constructMeasuredResidual selected value parent.context.formula).value := rfl

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.containsMeasuredLiteral
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredResidual
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredChild
#print axioms ConstitutiveSearch.EndogenousDecomposition.childFromMeasuredResidual
#print axioms ConstitutiveSearch.EndogenousDecomposition.childFromMeasuredResidual_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.constructMeasuredChild_consumes_residual
/- AXIOM_AUDIT_END -/
