import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierNormalization
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GeneratedStructuralContext
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ResidualFlipTransport

/-!
# Global relations between generated structural SAT contexts

This module migrates the global polarity flip to the hardened semantics.

The structural transport acts on every continuation that realizes the source
history, independently of SAT acceptance.  Preservation of residual
satisfaction is a separate theorem.
-/

namespace ConstitutiveSearch
namespace SAT

namespace StructuralBranchDecision

/-- Flip the recorded Boolean value exactly at the selected variable. -/
def flipAt
    (var : Var)
    (decision : StructuralBranchDecision) :
    StructuralBranchDecision :=
  if decision.var = var then
    { var := decision.var, value := !decision.value }
  else
    decision

end StructuralBranchDecision

/-- Flip one variable throughout a structural decision history. -/
def flipStructuralDecisionsAt
    (var : Var) :
    List StructuralBranchDecision →
      List StructuralBranchDecision
  | [] => []
  | decision :: rest =>
      StructuralBranchDecision.flipAt var decision ::
        flipStructuralDecisionsAt var rest

namespace StructuralDecisionsHold

/--
Flipping both an assignment and the selected values in its structural history
preserves realization of the complete history.
-/
theorem flipAt
    {assignment : Assignment}
    {decisions : List StructuralBranchDecision}
    (holds : StructuralDecisionsHold assignment decisions)
    (var : Var) :
    StructuralDecisionsHold
      (Assignment.flipAt var assignment)
      (flipStructuralDecisionsAt var decisions) := by
  induction decisions with
  | nil =>
      exact True.intro
  | cons decision rest inductionHypothesis =>
      cases holds with
      | intro headHold tailHold =>
          by_cases same : decision.var = var
          · have selected :
                Assignment.flipAt var assignment decision.var =
                  !(assignment decision.var) := by
              rw [same]
              exact Assignment.flipAt_selected var assignment
            have flippedHead :
                Assignment.flipAt var assignment decision.var =
                  !decision.value := by
              rw [selected, headHold]
            constructor
            · rw [StructuralBranchDecision.flipAt, if_pos same]
              exact flippedHead
            · exact inductionHypothesis tailHold
          · have preserved :
                Assignment.flipAt var assignment decision.var =
                  assignment decision.var :=
              Assignment.flipAt_other
                var
                decision.var
                assignment
                same
            constructor
            · rw [StructuralBranchDecision.flipAt, if_neg same]
              rw [preserved]
              exact headHold
            · exact inductionHypothesis tailHold

end StructuralDecisionsHold

/--
Global polarity-flip relation between generated structural contexts.

The contexts may have different immediate parents.  The relation requires exact
compatibility of the current residual syntax and complete constituted history.
-/
structure GeneratedStructuralFlipAtRelation
    {rootFormula : Cnf}
    (var : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) : Type where
  formulaExact :
    target.context.formula =
      Cnf.flipAt var source.context.formula
  decisionsExact :
    target.context.decisions =
      flipStructuralDecisionsAt
        var
        source.context.decisions

namespace GeneratedStructuralFlipAtRelation

/--
Total structural map.  No satisfaction proof is required to transform a
continuation.
-/
def mapContinuation
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (relation :
      GeneratedStructuralFlipAtRelation var source target)
    (continuation :
      GeneratedStructuralBranchContinuation source) :
    GeneratedStructuralBranchContinuation target :=
  let targetAssignment :=
    Assignment.flipAt var continuation.1
  let flippedDecisions :
      StructuralDecisionsHold
        targetAssignment
        (flipStructuralDecisionsAt
          var
          source.context.decisions) :=
    StructuralDecisionsHold.flipAt continuation.2 var
  let targetDecisions :
      StructuralDecisionsHold
        targetAssignment
        target.context.decisions :=
    Eq.mp
      (congrArg
        (StructuralDecisionsHold targetAssignment)
        relation.decisionsExact.symm)
      flippedDecisions
  ⟨targetAssignment, targetDecisions⟩

/-- The transported continuation carries exactly the flipped assignment. -/
theorem mapContinuation_assignment
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (relation :
      GeneratedStructuralFlipAtRelation var source target)
    (continuation :
      GeneratedStructuralBranchContinuation source) :
    (relation.mapContinuation continuation).1 =
      Assignment.flipAt var continuation.1 := by
  rfl

/-- Acceptance is preserved separately from the total structural map. -/
theorem mapContinuation_accept
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (relation :
      GeneratedStructuralFlipAtRelation var source target)
    (continuation :
      GeneratedStructuralBranchContinuation source)
    (accepted :
      GeneratedStructuralBranchAccept source continuation) :
    GeneratedStructuralBranchAccept
      target
      (relation.mapContinuation continuation) := by
  change
    Satisfies continuation.1 source.context.formula at accepted
  have flipped :
      Satisfies
        (Assignment.flipAt var continuation.1)
        (Cnf.flipAt var source.context.formula) :=
    accepted.flipAt var
  change
    Satisfies
      (Assignment.flipAt var continuation.1)
      target.context.formula
  exact
    Eq.mp
      (congrArg
        (Satisfies (Assignment.flipAt var continuation.1))
        relation.formulaExact.symm)
      flipped

/-- Hardened acceptance-preserving transport induced by the relation witness. -/
def toAcceptingTransport
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (relation :
      GeneratedStructuralFlipAtRelation var source target) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem rootFormula)
      source
      target :=
  { map := relation.mapContinuation
    preservesAccept := relation.mapContinuation_accept }

end GeneratedStructuralFlipAtRelation

/-- Positive action of global structural flips in the hardened search system. -/
def generatedStructuralFlipAtAction
    (rootFormula : Cnf)
    (var : Var) :
    AcceptedRelationalAction
      (generatedStructuralBranchSystem rootFormula)
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        var) :=
  { toTransport := fun relation =>
      relation.toAcceptingTransport }

/--
Executable exact search for the global structural flip relation.

Failure remains failure of this relation finder, not a proof that no useful
relation exists.
-/
def generatedStructuralFlipAtSearch
    (rootFormula : Cnf)
    (var : Var) :
    RelationSearch
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        var) :=
  { find := fun source target =>
      if formulaExact :
          target.context.formula =
            Cnf.flipAt var source.context.formula then
        if decisionsExact :
            target.context.decisions =
              flipStructuralDecisionsAt
                var
                source.context.decisions then
          some
            { formulaExact := formulaExact
              decisionsExact := decisionsExact }
        else
          none
      else
        none }

/--
Automatically normalize an arbitrary heterogeneous generated structural
frontier using one selected global flip relation.
-/
def normalizeGeneratedStructuralFrontierByFlip
    (rootFormula : Cnf)
    (var : Var)
    (frontier :
      List (GeneratedStructuralBranchContext rootFormula)) :
    AcceptedIrreducibleFrontierReduction
      (system := generatedStructuralBranchSystem rootFormula)
      (generatedStructuralFlipAtSearch rootFormula var)
      frontier :=
  normalizeAcceptedFrontier
    (generatedStructuralFlipAtSearch rootFormula var)
    (generatedStructuralFlipAtAction rootFormula var)
    frontier

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.StructuralBranchDecision.flipAt
#print axioms ConstitutiveSearch.SAT.flipStructuralDecisionsAt
#print axioms ConstitutiveSearch.SAT.StructuralDecisionsHold.flipAt
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipAtRelation
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipAtRelation.mapContinuation
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipAtRelation.mapContinuation_assignment
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipAtRelation.mapContinuation_accept
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipAtRelation.toAcceptingTransport
#print axioms ConstitutiveSearch.SAT.generatedStructuralFlipAtAction
#print axioms ConstitutiveSearch.SAT.generatedStructuralFlipAtSearch
#print axioms ConstitutiveSearch.SAT.normalizeGeneratedStructuralFrontierByFlip
/- AXIOM_AUDIT_END -/
