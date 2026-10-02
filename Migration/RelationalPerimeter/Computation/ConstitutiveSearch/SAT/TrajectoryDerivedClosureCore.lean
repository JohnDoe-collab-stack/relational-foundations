import RelationalPerimeter.Computation.ConstitutiveSearch.ClosureSearch
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ParametricSymmetricTrajectory
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-!
# Generic closure data reconstructed from SAT trajectories

Bounded closure search takes three pieces of finite search control as explicit
arguments: primitive generators, an intermediate-candidate list, and fuel.

This module reconstructs all three from an already constituted
FlipSymmetricTrajectory.

No satisfiability information is introduced:
* generator variables are exactly the variables recorded by trajectory steps;
* candidates are exactly the false/true children that occur in the certified
  split frontiers along the trajectory;
* fuel is the number of recorded generator variables.

The resulting bounded closure search therefore has no separately supplied
candidate list, generator list, or fuel.  It is still only a bounded closure
search: reconstruction of its finite search domain does not imply that every
useful transport lies in that domain.
-/

namespace ConstitutiveSearch
namespace SAT

/--
One exact structural flip whose variable belongs to an explicit finite
provenance list.
-/
structure ProvenanceStructuralFlipWitness
    {rootFormula : Cnf}
    (vars : List Var)
    (source target :
      GeneratedStructuralBranchContext rootFormula) : Type where
  var : Var
  member : var ∈ vars
  relation :
    GeneratedStructuralFlipAtRelation
      var
      source
      target

namespace ProvenanceStructuralFlipWitness

/-- Every provenance-restricted witness still acts by the hardened total transport. -/
def toAcceptingTransport
    {rootFormula : Cnf}
    {vars : List Var}
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (witness :
      ProvenanceStructuralFlipWitness
        vars
        source
        target) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem rootFormula)
      source
      target :=
  witness.relation.toAcceptingTransport

end ProvenanceStructuralFlipWitness

/--
Executable primitive search through exactly the variables in one finite
provenance list.

The list is searched from head to tail.  Each individual query is the existing
exact generatedStructuralFlipAtSearch and therefore contains no SAT query.
-/
def provenanceStructuralFlipSearch
    (rootFormula : Cnf) :
    (vars : List Var) →
      RelationSearch
        (ProvenanceStructuralFlipWitness
          (rootFormula := rootFormula)
          vars)
  | [] =>
      { find := fun _source _target =>
          none }
  | var :: rest =>
      { find := fun source target =>
          match
            (generatedStructuralFlipAtSearch
              rootFormula
              var).find
                source
                target with
          | some relation =>
              some
                { var := var
                  member := by
                    exact List.mem_cons_self
                  relation := relation }
          | none =>
              match
                (provenanceStructuralFlipSearch
                  rootFormula
                  rest).find
                    source
                    target with
              | none =>
                  none
              | some witness =>
                  some
                    { var := witness.var
                      member :=
                        List.mem_cons_of_mem
                          var
                          witness.member
                      relation :=
                        witness.relation } }

/-- Positive action of provenance-restricted structural flips. -/
def provenanceStructuralFlipAction
    (rootFormula : Cnf)
    (vars : List Var) :
    AcceptedRelationalAction
      (generatedStructuralBranchSystem rootFormula)
      (ProvenanceStructuralFlipWitness
        (rootFormula := rootFormula)
        vars) :=
  { toTransport := fun witness =>
      witness.toAcceptingTransport }

namespace FlipSymmetricTrajectory

/-- Decision variables in the exact order in which the trajectory constitutes them. -/
def decisionVars
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      List Var
  | .done _ =>
      []
  | .step var _fresh _symmetric tail =>
      var :: tail.decisionVars

/--
All structural children that actually occur in certified split frontiers.

Each constitutive step contributes its false sibling and retained true child.
No state is synthesized independently of a trajectory step.
-/
def splitCandidates
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    List (GeneratedStructuralBranchContext rootFormula) :=
  match trajectory with
  | .done _ =>
      []
  | .step var fresh _symmetric tail =>
      GeneratedStructuralBranchContext.child
          start
          var
          false
          fresh ::
        GeneratedStructuralBranchContext.child
            start
            var
            true
            fresh ::
          tail.splitCandidates

/-- Structural true decision canonically associated with one trajectory variable. -/
def trueDecisionOfVar
    (var : Var) :
    StructuralBranchDecision :=
  { var := var
    value := true }

/--
The extracted generator variables are not an auxiliary annotation: they are
exactly the newly constituted prefix of the final structural history.

Histories are stored newest-first, hence the reversal of chronological
trajectory variables.
-/
theorem finish_decisions_eq_trajectoryVars
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    finish.context.decisions =
      trajectory.decisionVars.reverse.map
          trueDecisionOfVar ++
        start.context.decisions := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      rw [inductionHypothesis]
      rw [
        decisionVars,
        Constructive.list_reverse_cons,
        Constructive.list_map_append,
        GeneratedStructuralBranchContext.child_decisions,
        Constructive.list_append_assoc
      ]
      rfl

/--
Projecting only variable names gives the same exact provenance statement.
-/
theorem finish_decisionVariables_eq_trajectoryVars
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    finish.context.decisions.map
        StructuralBranchDecision.var =
      trajectory.decisionVars.reverse ++
        start.context.decisions.map
          StructuralBranchDecision.var := by
  rw [
    trajectory.finish_decisions_eq_trajectoryVars
  ]
  calc
    ((trajectory.decisionVars.reverse.map trueDecisionOfVar ++
          start.context.decisions).map
        StructuralBranchDecision.var) =
        (trajectory.decisionVars.reverse.map
            trueDecisionOfVar).map
              StructuralBranchDecision.var ++
          start.context.decisions.map
            StructuralBranchDecision.var :=
      Constructive.list_map_append
        StructuralBranchDecision.var
        (trajectory.decisionVars.reverse.map trueDecisionOfVar)
        start.context.decisions
    _ = trajectory.decisionVars.reverse.map
            (fun value =>
              StructuralBranchDecision.var
                (trueDecisionOfVar value)) ++
          start.context.decisions.map
            StructuralBranchDecision.var :=
      congrArg
        (fun values =>
          values ++
            start.context.decisions.map
              StructuralBranchDecision.var)
        (Constructive.list_map_map
          trueDecisionOfVar
          StructuralBranchDecision.var
          trajectory.decisionVars.reverse)
    _ = trajectory.decisionVars.reverse.map
            (fun value => value) ++
          start.context.decisions.map
            StructuralBranchDecision.var := rfl
    _ = trajectory.decisionVars.reverse ++
          start.context.decisions.map
            StructuralBranchDecision.var :=
      congrArg
        (fun values =>
          values ++
            start.context.decisions.map
              StructuralBranchDecision.var)
        (Constructive.list_map_id
          trajectory.decisionVars.reverse)

/-- The generator-variable list has exactly one entry per constitutive step. -/
theorem decisionVars_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.decisionVars.length =
      length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      change
        Nat.succ tail.decisionVars.length =
          _ + 1
      rw [inductionHypothesis]

/-- The derived candidate list contributes exactly two split children per step. -/
theorem splitCandidates_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.splitCandidates.length =
      2 * length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      change
        Nat.succ
            (Nat.succ
              tail.splitCandidates.length) =
          2 * (_ + 1)
      rw [
        inductionHypothesis,
        Nat.mul_succ
      ]

/-- Closure fuel reconstructed from the number of constituted generator variables. -/
def closureFuel
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    Nat :=
  trajectory.decisionVars.length

/-- Reconstructed fuel is exactly the trajectory length. -/
theorem closureFuel_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.closureFuel =
      length :=
  trajectory.decisionVars_length

/-- Primitive relation search reconstructed solely from trajectory provenance. -/
def primitiveSearch
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    RelationSearch
      (ProvenanceStructuralFlipWitness
        (rootFormula := rootFormula)
        trajectory.decisionVars) :=
  provenanceStructuralFlipSearch
    rootFormula
    trajectory.decisionVars

/--
Bounded transport-closure search whose complete finite control domain is
reconstructed from the trajectory itself.
-/
def derivedClosureSearch
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    RelationSearch
      (TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula := rootFormula)
          trajectory.decisionVars)) :=
  boundedTransportClosureSearch
    trajectory.primitiveSearch
    trajectory.splitCandidates
    trajectory.closureFuel

/--
The first certified sibling flip of any nonempty trajectory is reconstructible
by the trajectory-derived primitive search.
-/
theorem primitiveSearch_finds_firstSibling
    {rootFormula : Cnf}
    {parent finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var)
    (tail :
      FlipSymmetricTrajectory
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh)
        finish
        length) :
    let trajectory :=
      FlipSymmetricTrajectory.step
        var
        fresh
        symmetric
        tail
    trajectory.primitiveSearch.find
        (GeneratedStructuralBranchContext.child
          parent
          var
          false
          fresh)
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh) ≠
      none := by
  dsimp [primitiveSearch, decisionVars, provenanceStructuralFlipSearch]
  let relation :=
    flipSymmetricSiblingRelation
      parent
      var
      fresh
      symmetric
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos relation.formulaExact,
    dif_pos relation.decisionsExact
  ]
  intro impossible
  cases impossible

end FlipSymmetricTrajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ProvenanceStructuralFlipWitness
#print axioms ConstitutiveSearch.SAT.ProvenanceStructuralFlipWitness.toAcceptingTransport
#print axioms ConstitutiveSearch.SAT.provenanceStructuralFlipSearch
#print axioms ConstitutiveSearch.SAT.provenanceStructuralFlipAction
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.decisionVars
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.trueDecisionOfVar
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.finish_decisions_eq_trajectoryVars
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.finish_decisionVariables_eq_trajectoryVars
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.splitCandidates
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.decisionVars_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.splitCandidates_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.closureFuel
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.closureFuel_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.primitiveSearch
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.derivedClosureSearch
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.primitiveSearch_finds_firstSibling
/- AXIOM_AUDIT_END -/
