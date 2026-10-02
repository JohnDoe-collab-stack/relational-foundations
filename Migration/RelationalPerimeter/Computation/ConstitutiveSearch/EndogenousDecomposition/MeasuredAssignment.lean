import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredDiscovery

/-!
Instrumented reading of transported assignments. A function-valued assignment
is not a constant-time oracle: each executed flip compares the queried label,
then reads its input through the preceding measured reader. The public concrete
pipeline supplies its own measured initial reader.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

abbrev MeasuredAssignment (assignment : Assignment) :=
  (query : Var) → MeasuredValue (assignment query)

def readFlippedAssignment (selected : Var) {assignment : Assignment}
    (readInput : MeasuredAssignment assignment) (query : Var) :
    MeasuredValue (Assignment.flipAt selected assignment query) :=
  let compared := compareUnary query selected
  let prior := readInput query
  match compared.result with
  | .isTrue same =>
    ⟨!prior.value, by rw [Assignment.flipAt, if_pos same, prior.valueExact],
      (compared.work.add prior.work).visit⟩
  | .isFalse different =>
    ⟨prior.value, by rw [Assignment.flipAt, if_neg different]; exact prior.valueExact,
      (compared.work.add prior.work).visit⟩

/-- Interpret the actual returned code, including its composition structure. -/
def readTransportedAssignment {root : Cnf} (selected : Var) :
    {source target : GeneratedStructuralBranchContext root} →
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target) →
    (input : GeneratedStructuralBranchContinuation source) →
    MeasuredAssignment input.1 →
    MeasuredAssignment (((code.eval (generatedStructuralFlipAtAction root selected)).map input).1)
  | _, _, .identity _, _, readInput => fun query =>
    let prior := readInput query
    ⟨prior.value, prior.valueExact, prior.work.visit⟩
  | _, _, .atom _, _, readInput => readFlippedAssignment selected readInput
  | _, _, .compose first second, input, readInput => fun query =>
    let middle := (first.eval (generatedStructuralFlipAtAction root selected)).map input
    let readMiddle := readTransportedAssignment selected first input readInput
    let output := readTransportedAssignment selected second middle readMiddle query
    ⟨output.value, output.valueExact, output.work.visit⟩

structure MeasuredAssignmentReadout {assignment : Assignment} (queries : List Var) where
  bits : List Bool
  bitsExact : bits = queries.map assignment
  work : ComparisonWork

/-- Both the terminal bits and their evaluation work come from these reads. -/
def readAssignmentQueries {assignment : Assignment}
    (reader : MeasuredAssignment assignment) :
    (queries : List Var) → MeasuredAssignmentReadout (assignment := assignment) queries
  | [] => ⟨[], rfl, ⟨1, 0⟩⟩
  | query :: rest =>
    let head := reader query
    let tail := readAssignmentQueries reader rest
    ⟨head.value :: tail.bits, by rw [head.valueExact, tail.bitsExact]; rfl,
      (head.work.add tail.work).visit⟩

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.readFlippedAssignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.readTransportedAssignment
#print axioms ConstitutiveSearch.EndogenousDecomposition.readAssignmentQueries
/- AXIOM_AUDIT_END -/
