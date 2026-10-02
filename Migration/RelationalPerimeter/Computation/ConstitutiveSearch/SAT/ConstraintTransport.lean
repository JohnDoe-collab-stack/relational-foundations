import RelationalPerimeter.Computation.ConstitutiveSearch.IrreducibleFrontier

/-!
# First SAT instance: transports reconstructed from CNF weakening

This module instantiates constitutive search on propositional CNF constraints
without assuming satisfiability, unsatisfiability, or an oracle for either.

A completion is a total Boolean assignment together with a proof that it
satisfies every clause of the CNF.  The structural relation `CnfWeakening`
expresses that the target CNF is obtained by deleting zero or more clauses from
the source CNF while preserving the order of retained clauses.

Every source completion therefore transports constructively to a target
completion by keeping the same assignment and restricting the satisfaction
proof.  This gives a concrete `ContinuationTransport` from a purely structural
constraint relation.

An executable structural search constructs weakening witnesses when it finds
them.  It is deliberately not used as a negative decision procedure: `none`
means only that this search found no witness.
-/

namespace ConstitutiveSearch
namespace SAT

abbrev Var := Nat
abbrev Assignment := Var → Bool

inductive Literal where
  | positive : Var → Literal
  | negative : Var → Literal
  deriving DecidableEq

abbrev Clause := List Literal
abbrev Cnf := List Clause

namespace Literal

/-- Boolean evaluation of one literal under a total assignment. -/
def eval (assignment : Assignment) : Literal → Bool
  | .positive var => assignment var
  | .negative var => !(assignment var)

end Literal

namespace Clause

/-- Disjunctive evaluation of a clause.  The empty clause is false. -/
def eval (assignment : Assignment) : Clause → Bool
  | [] => false
  | literal :: rest => literal.eval assignment || eval assignment rest

end Clause

/-- Constructive proof that one assignment satisfies every clause of a CNF. -/
inductive Satisfies (assignment : Assignment) : Cnf → Prop
  | nil : Satisfies assignment []
  | cons
      {clause : Clause}
      {rest : Cnf}
      (headSatisfied : Clause.eval assignment clause = true)
      (tailSatisfied : Satisfies assignment rest) :
      Satisfies assignment (clause :: rest)

/-- Proof-relevant terminal completion space of a CNF. -/
abbrev Completion (formula : Cnf) : Type :=
  { assignment : Assignment // Satisfies assignment formula }

/--
Constructive clause-deletion relation.  `CnfWeakening source target` means that
`target` is an order-preserving sublist of `source`.
-/
inductive CnfWeakening : Cnf → Cnf → Type
  | done {source : Cnf} : CnfWeakening source []
  | drop
      {source target : Cnf}
      (clause : Clause)
      (rest : CnfWeakening source target) :
      CnfWeakening (clause :: source) target
  | keep
      {source target : Cnf}
      (clause : Clause)
      (rest : CnfWeakening source target) :
      CnfWeakening (clause :: source) (clause :: target)

namespace CnfWeakening

/-- Every CNF weakens to itself. -/
def refl : (formula : Cnf) → CnfWeakening formula formula
  | [] => .done
  | clause :: rest => .keep clause (refl rest)

/-- Weakening preserves satisfaction by deleting obligations only. -/
theorem preservesSatisfaction
    {source target : Cnf}
    (weakening : CnfWeakening source target)
    {assignment : Assignment} :
    Satisfies assignment source → Satisfies assignment target := by
  induction weakening with
  | done =>
      intro _
      exact .nil
  | drop clause rest inductionHypothesis =>
      intro sourceSatisfaction
      cases sourceSatisfaction with
      | cons _ tailSatisfaction =>
          exact inductionHypothesis tailSatisfaction
  | keep clause rest inductionHypothesis =>
      intro sourceSatisfaction
      cases sourceSatisfaction with
      | cons headSatisfaction tailSatisfaction =>
          exact .cons headSatisfaction
            (inductionHypothesis tailSatisfaction)

/-- A weakening witness acts constructively on completion spaces. -/
def completionMap
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    Completion source → Completion target :=
  fun completion =>
    ⟨completion.1,
      weakening.preservesSatisfaction completion.2⟩

/-- Structural CNF weakening reconstructs the generic continuation transport. -/
def toTransport
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    ContinuationTransport Completion source target :=
  { map := weakening.completionMap }

/-- Keep structurally equal clause heads while retaining the dependent indices. -/
def keepOfEq
    {source target : Cnf}
    (sourceHead targetHead : Clause)
    (headsEqual : sourceHead = targetHead)
    (rest : CnfWeakening source target) :
    CnfWeakening (sourceHead :: source) (targetHead :: target) := by
  cases headsEqual
  exact .keep sourceHead rest

/--
Executable structural search for a target sub-CNF.  The recursion is structural
on the source list.  When equal heads are encountered the procedure commits to
retaining them, so failure remains only failure of this particular search.
-/
def find : (source target : Cnf) → Option (CnfWeakening source target)
  | _, [] => some .done
  | [], _ :: _ => none
  | sourceHead :: sourceTail, targetHead :: targetTail =>
      if headsEqual : sourceHead = targetHead then
        match find sourceTail targetTail with
        | some retainedTail =>
            some (keepOfEq sourceHead targetHead headsEqual retainedTail)
        | none => none
      else
        match find sourceTail (targetHead :: targetTail) with
        | some droppedTail => some (.drop sourceHead droppedTail)
        | none => none

end CnfWeakening

/-- Generic relational action instantiated by CNF weakening. -/
def weakeningAction :
    RelationalContinuationAction CnfWeakening Completion :=
  { act := fun witness completion =>
      witness.completionMap completion }

/-- Executable weakening search exposed through the generic relation interface. -/
def weakeningSearch : RelationSearch CnfWeakening :=
  { find := CnfWeakening.find }

/-- Convenient singleton positive clause. -/
def positiveUnit (var : Var) : Clause :=
  [Literal.positive var]

/-- Convenient singleton negative clause. -/
def negativeUnit (var : Var) : Clause :=
  [Literal.negative var]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal
#print axioms ConstitutiveSearch.SAT.Clause.eval
#print axioms ConstitutiveSearch.SAT.Satisfies
#print axioms ConstitutiveSearch.SAT.CnfWeakening
#print axioms ConstitutiveSearch.SAT.CnfWeakening.preservesSatisfaction
#print axioms ConstitutiveSearch.SAT.CnfWeakening.toTransport
#print axioms ConstitutiveSearch.SAT.CnfWeakening.find
#print axioms ConstitutiveSearch.SAT.weakeningAction
#print axioms ConstitutiveSearch.SAT.weakeningSearch
/- AXIOM_AUDIT_END -/