import RelationalPerimeter.Computation.ConstitutiveSearch.LocalSearchableCodeExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCodeValidationCore
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.TrajectoryDerivedClosureCore

/-!
# Generic constituted local-code schedule extracted from SAT trajectories

A FlipSymmetricTrajectory is not itself a linear path of primitive flips:
each constitutive step expands a parent into two children and then absorbs the
false sibling into the retained true child.  The primitive flip therefore runs
between siblings, not from the trajectory parent to its retained child.

This module preserves that distinction.

It extracts, directly from the proof-relevant trajectory, one local sibling
witness per constitutive step.  Every schedule entry retains exactly the
variable and structural relation already carried by that step.

No witness list, candidate list, closure fuel, global provenance domain, or
global ClosureSearch result is supplied separately.

Each entry:
* compiles to a one-atom local TransportCode;
* is validated by generatedStructuralFlipAtSearch at its own constituted var;
* validates with exactly one primitive query;
* executes by an actual candidate-free ClosureSearch run with fuel one;
* performs exactly one primitive query and zero composition-candidate
  inspections.

The complete schedule has exactly one local witness and one transport atom per
constitutive step.  Its variable projection is exactly trajectory.decisionVars.
Thus no future trajectory variable is needed to validate or execute an earlier
entry.
-/

namespace ConstitutiveSearch
namespace SAT

/--
One locally constituted sibling relation packaged with its dependent endpoints
and the exact variable that generated it.
-/
structure ConstitutedLocalWitness
    (rootFormula : Cnf) where
  var : Var
  source :
    GeneratedStructuralBranchContext
      rootFormula
  target :
    GeneratedStructuralBranchContext
      rootFormula
  relation :
    GeneratedStructuralFlipAtRelation
      var
      source
      target

namespace ConstitutedLocalWitness

/-- Compile one constituted local relation to its one-atom transport code. -/
def code
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    TransportClosure
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        entry.var)
      entry.source
      entry.target :=
  TransportClosure.ofGenerator
    entry.relation

/-- Every packaged local relation contributes exactly one transport atom. -/
theorem code_size
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    entry.code.size = 1 := by
  rfl

/--
The code is searchable by the exact primitive search indexed by the variable
already constituted at this trajectory step.
-/
theorem code_searchable
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    entry.code.SearchableBy
      (generatedStructuralFlipAtSearch
        rootFormula
        entry.var) := by
  change
    (generatedStructuralFlipAtSearch
        rootFormula
        entry.var).find
      entry.source
      entry.target ≠
    none
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos entry.relation.formulaExact,
    dif_pos entry.relation.decisionsExact
  ]
  intro impossible
  cases impossible

/-- Executable SearchableBy validation of one local code succeeds. -/
theorem validation_success
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    (validateSearchableCode
        (generatedStructuralFlipAtSearch
          rootFormula
          entry.var)
        entry.code).success =
      true :=
  validateSearchableCode_success_of_searchable
    (generatedStructuralFlipAtSearch
      rootFormula
      entry.var)
    entry.code
    entry.code_searchable

/-- Executable validation performs exactly one primitive query per local code. -/
theorem validation_primitiveQueries
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    (validateSearchableCode
        (generatedStructuralFlipAtSearch
          rootFormula
          entry.var)
        entry.code).primitiveQueries =
      1 := by
  calc
    (validateSearchableCode
        (generatedStructuralFlipAtSearch
          rootFormula
          entry.var)
        entry.code).primitiveQueries
        =
      entry.code.size :=
        validateSearchableCode_primitiveQueries
          (generatedStructuralFlipAtSearch
            rootFormula
            entry.var)
          entry.code
    _ = 1 :=
      entry.code_size

/--
Actual candidate-free ClosureSearch run for one locally constituted sibling
relation.  No intermediate candidates are supplied and the fuel is one.
-/
def executionRun
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    ClosureSearchRun
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        entry.var)
      entry.source
      entry.target :=
  searchTransportClosureBounded
    (generatedStructuralFlipAtSearch
      rootFormula
      entry.var)
    []
    1
    entry.source
    entry.target

/-- The actual local run succeeds because the constituted relation is a primitive hit. -/
theorem executionRun_found
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    entry.executionRun.code? ≠ none := by
  unfold executionRun
  simp only [
    searchTransportClosureBounded
  ]
  cases found :
      (generatedStructuralFlipAtSearch
        rootFormula
        entry.var).find
          entry.source
          entry.target with
  | none =>
      exact
        False.elim
          (entry.code_searchable found)
  | some witness =>
      simp only
      intro impossible
      cases impossible

/--
Actual local run statistics: one primitive query and no composition-candidate
inspection.
-/
theorem executionRun_stats
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    entry.executionRun.stats.primitiveQueries = 1 ∧
      entry.executionRun.stats.compositionCandidates = 0 := by
  simpa only [executionRun] using
    PrimitiveHitPath.primitiveHit_run_stats
      (generatedStructuralFlipAtSearch
        rootFormula
        entry.var)
      []
      1
      entry.source
      entry.target
      (by decide)
      entry.code_searchable

/-- Every constituted local code admits the minimal candidate-free execution. -/
theorem localSequentialExecution
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness
        rootFormula) :
    TransportCode.LocalSequentialExecution
      (generatedStructuralFlipAtSearch
        rootFormula
        entry.var)
      entry.code :=
  TransportCode.localSequentialExecution_of_searchable
    (generatedStructuralFlipAtSearch
      rootFormula
      entry.var)
    entry.code
    entry.code_searchable

end ConstitutedLocalWitness

namespace FlipSymmetricTrajectory

/--
Canonical local schedule extracted directly from the proof-relevant trajectory.

Every entry is built only from the current constructor fields var, fresh and
symmetric, then recursion continues into the already-constituted tail.
-/
def constitutedLocalWitnesses
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    List
      (ConstitutedLocalWitness
        rootFormula) :=
  match trajectory with
  | .done _ =>
      []
  | .step var fresh symmetric tail =>
      { var := var
        source :=
          GeneratedStructuralBranchContext.child
            start
            var
            false
            fresh
        target :=
          GeneratedStructuralBranchContext.child
            start
            var
            true
            fresh
        relation :=
          flipSymmetricSiblingRelation
            start
            var
            fresh
            symmetric } ::
        tail.constitutedLocalWitnesses

/-- The extracted schedule contains exactly one local witness per step. -/
theorem constitutedLocalWitnesses_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    trajectory.constitutedLocalWitnesses.length =
      length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      simp only [
        constitutedLocalWitnesses,
        List.length_cons
      ]
      rw [
        inductionHypothesis
      ]

/--
The variable projection of the extracted schedule is definitionally the
trajectory provenance produced by decisionVars.
-/
theorem constitutedLocalWitnesses_vars
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    trajectory.constitutedLocalWitnesses.map
        (fun entry => entry.var) =
      trajectory.decisionVars := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      change
        var ::
            tail.constitutedLocalWitnesses.map
              (fun entry => entry.var) =
          var ::
            tail.decisionVars
      rw [
        inductionHypothesis
      ]

end FlipSymmetricTrajectory

namespace ConstitutedLocalSchedule

/-- Total number of transport atoms produced by an extracted local schedule. -/
def atomCount
    {rootFormula : Cnf} :
    List
      (ConstitutedLocalWitness
        rootFormula) →
      Nat
  | [] =>
      0
  | entry :: rest =>
      entry.code.size +
        atomCount rest

/-- Total executable validation primitive queries for an extracted schedule. -/
def validationPrimitiveQueries
    {rootFormula : Cnf} :
    List
      (ConstitutedLocalWitness
        rootFormula) →
      Nat
  | [] =>
      0
  | entry :: rest =>
      (validateSearchableCode
          (generatedStructuralFlipAtSearch
            rootFormula
            entry.var)
          entry.code).primitiveQueries +
        validationPrimitiveQueries
          rest

/-- Aggregate statistics of the actual candidate-free local ClosureSearch runs. -/
def executionStats
    {rootFormula : Cnf} :
    List
      (ConstitutedLocalWitness
        rootFormula) →
      ClosureSearchStats
  | [] =>
      ClosureSearchStats.zero
  | entry :: rest =>
      ClosureSearchStats.combine
        entry.executionRun.stats
        (executionStats rest)

/-- Actual primitive-query count of the candidate-free local schedule. -/
def executionPrimitiveQueries
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    Nat :=
  (executionStats schedule).primitiveQueries

/-- Actual composition-candidate count of the candidate-free local schedule. -/
def executionCompositionCandidates
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    Nat :=
  (executionStats schedule).compositionCandidates

/-- Every local code in the schedule validates successfully. -/
def ValidationSucceeds
    {rootFormula : Cnf} :
    List
      (ConstitutedLocalWitness
        rootFormula) →
      Prop
  | [] =>
      True
  | entry :: rest =>
      (validateSearchableCode
          (generatedStructuralFlipAtSearch
            rootFormula
            entry.var)
          entry.code).success =
          true ∧
        ValidationSucceeds rest

/-- Every local code in the schedule admits candidate-free local execution. -/
def HasLocalExecutions
    {rootFormula : Cnf} :
    List
      (ConstitutedLocalWitness
        rootFormula) →
      Prop
  | [] =>
      True
  | entry :: rest =>
      TransportCode.LocalSequentialExecution
          (generatedStructuralFlipAtSearch
            rootFormula
            entry.var)
          entry.code ∧
        HasLocalExecutions rest

/-- Production atom count is exactly schedule length. -/
theorem atomCount_eq_length
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    atomCount schedule =
      schedule.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      change
        entry.code.size +
            atomCount rest =
          rest.length + 1
      rw [
        entry.code_size,
        inductionHypothesis
      ]
      exact
        Nat.add_comm 1 rest.length

/-- Executable validation query count is exactly schedule length. -/
theorem validationPrimitiveQueries_eq_length
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    validationPrimitiveQueries schedule =
      schedule.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      change
        (validateSearchableCode
            (generatedStructuralFlipAtSearch
              rootFormula
              entry.var)
            entry.code).primitiveQueries +
              validationPrimitiveQueries rest =
          rest.length + 1
      rw [
        entry.validation_primitiveQueries,
        inductionHypothesis
      ]
      exact
        Nat.add_comm 1 rest.length

/-- Actual local execution performs exactly one primitive query per schedule entry. -/
theorem executionPrimitiveQueries_eq_length
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    executionPrimitiveQueries schedule =
      schedule.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      have entryStats :=
        entry.executionRun_stats
      change
        entry.executionRun.stats.primitiveQueries +
            (executionStats rest).primitiveQueries =
          rest.length + 1
      rw [
        entryStats.1,
        show
          (executionStats rest).primitiveQueries =
            rest.length from
          inductionHypothesis
      ]
      exact
        Nat.add_comm 1 rest.length

/-- Actual local execution inspects no composition candidates. -/
theorem executionCompositionCandidates_eq_zero
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    executionCompositionCandidates schedule =
      0 := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      have entryStats :=
        entry.executionRun_stats
      change
        entry.executionRun.stats.compositionCandidates +
            (executionStats rest).compositionCandidates =
          0
      rw [
        entryStats.2,
        show
          (executionStats rest).compositionCandidates =
            0 from
          inductionHypothesis
      ]

/-- Every extracted schedule validates successfully. -/
theorem validationSucceeds
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    ValidationSucceeds schedule := by
  induction schedule with
  | nil =>
      exact True.intro
  | cons entry rest inductionHypothesis =>
      exact
        ⟨entry.validation_success,
          inductionHypothesis⟩

/-- Every extracted schedule admits candidate-free executions stepwise. -/
theorem hasLocalExecutions
    {rootFormula : Cnf}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula)) :
    HasLocalExecutions schedule := by
  induction schedule with
  | nil =>
      exact True.intro
  | cons entry rest inductionHypothesis =>
      exact
        ⟨entry.localSequentialExecution,
          inductionHypothesis⟩

end ConstitutedLocalSchedule

namespace FlipSymmetricTrajectory

/-- Produced local transport atoms are exactly the constitutive trajectory length. -/
theorem constitutedLocalAtomCount_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.atomCount
        trajectory.constitutedLocalWitnesses =
      length := by
  rw [
    ConstitutedLocalSchedule.atomCount_eq_length,
    trajectory.constitutedLocalWitnesses_length
  ]

/-- Executable validation charges exactly one direct primitive query per step. -/
theorem constitutedLocalValidationQueries_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.validationPrimitiveQueries
        trajectory.constitutedLocalWitnesses =
      length := by
  rw [
    ConstitutedLocalSchedule.validationPrimitiveQueries_eq_length,
    trajectory.constitutedLocalWitnesses_length
  ]

/-- Candidate-free actual local execution uses exactly one primitive query per step. -/
theorem constitutedLocalExecutionQueries_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.executionPrimitiveQueries
        trajectory.constitutedLocalWitnesses =
      length := by
  rw [
    ConstitutedLocalSchedule.executionPrimitiveQueries_eq_length,
    trajectory.constitutedLocalWitnesses_length
  ]

/-- Candidate-free local execution inspects no composition candidates. -/
theorem constitutedLocalExecutionCompositionCandidates_eq_zero
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.executionCompositionCandidates
        trajectory.constitutedLocalWitnesses =
      0 :=
  ConstitutedLocalSchedule.executionCompositionCandidates_eq_zero
    trajectory.constitutedLocalWitnesses

/-- Every code produced from the trajectory validates successfully. -/
theorem constitutedLocalValidationSucceeds
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.ValidationSucceeds
      trajectory.constitutedLocalWitnesses :=
  ConstitutedLocalSchedule.validationSucceeds
    trajectory.constitutedLocalWitnesses

/-- Every code produced from the trajectory has a candidate-free local execution. -/
theorem constitutedLocalHasLocalExecutions
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.HasLocalExecutions
      trajectory.constitutedLocalWitnesses :=
  ConstitutedLocalSchedule.hasLocalExecutions
    trajectory.constitutedLocalWitnesses

end FlipSymmetricTrajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code_size
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code_searchable
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.validation_success
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.validation_primitiveQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.executionRun
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.executionRun_found
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.executionRun_stats
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.localSequentialExecution
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses_vars
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.atomCount
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationPrimitiveQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.executionStats
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.executionPrimitiveQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.executionCompositionCandidates
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.ValidationSucceeds
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.HasLocalExecutions
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.atomCount_eq_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationPrimitiveQueries_eq_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.executionPrimitiveQueries_eq_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.executionCompositionCandidates_eq_zero
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationSucceeds
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.hasLocalExecutions
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalAtomCount_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalValidationQueries_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalExecutionQueries_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalExecutionCompositionCandidates_eq_zero
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalValidationSucceeds
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalHasLocalExecutions
/- AXIOM_AUDIT_END -/
