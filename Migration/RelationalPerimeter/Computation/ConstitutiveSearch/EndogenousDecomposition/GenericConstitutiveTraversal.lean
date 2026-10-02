import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveInterface

/-!
Generic traversal of actual generated endpoints. A generated step does not
contain a local relation: the latter is obtained by exploring extracted
candidates. Failure is retained, including on a concrete SAT surface below.
The resulting history stores local endpoints separately, not an invented
composition of sibling transports.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open StrongPerimetralTurning SAT

namespace ConstitutiveOperationalInterface

universe u

abbrev LocalDiscovery (I : ConstitutiveOperationalInterface.{u})
    (operational : I.OperationalState) :=
  Sigma fun endpoints : I.LocalState operational × I.LocalState operational =>
    I.OperationalRelation operational endpoints.1 endpoints.2

structure Exploration (I : ConstitutiveOperationalInterface.{u})
    (operational : I.OperationalState) where
  result : Option (I.LocalDiscovery operational)
  tested : List I.Candidate
  attempts : Nat

def explore (I : ConstitutiveOperationalInterface.{u})
    (operational : I.OperationalState) : List I.Candidate → I.Exploration operational
  | [] => ⟨none, [], 0⟩
  | candidate :: rest =>
    match I.discover operational candidate with
    | some relation => ⟨some relation, [candidate], 1⟩
    | none =>
      let tail := I.explore operational rest
      ⟨tail.result, candidate :: tail.tested, tail.attempts + 1⟩

theorem explore_tested (I : ConstitutiveOperationalInterface.{u})
    (operational : I.OperationalState) (candidates : List I.Candidate) :
    (I.explore operational candidates).tested.length =
      (I.explore operational candidates).attempts := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    unfold explore
    split
    · rfl
    · exact congrArg (fun n => n + 1) ih

def discoverState (I : ConstitutiveOperationalInterface.{u})
    (target : I.ConstitutiveState) : I.Exploration (I.realize target) :=
  let operational := I.realize target
  I.explore operational (I.extract operational)

/-- Production retains the first projection of every actual call to generate. -/
def produceHistory (I : ConstitutiveOperationalInterface.{u})
    (source : I.ConstitutiveState) : Nat →
    Sigma fun target => History I.ConstitutiveGenerator source target
  | 0 => ⟨source, .root⟩
  | count + 1 =>
    let prior := I.produceHistory source count
    let next := I.generate prior.1
    ⟨next.1, .extend prior.2 next.2⟩

inductive DiscoveredHistory (I : ConstitutiveOperationalInterface.{u}) :
    {source target : I.ConstitutiveState} →
    History I.ConstitutiveGenerator source target → Type u where
  | root {source} : DiscoveredHistory I (.root (a := source))
  | extend {source middle target}
      {prior : History I.ConstitutiveGenerator source middle}
      (step : I.ConstitutiveGenerator middle target)
      (previous : DiscoveredHistory I prior)
      (relation : I.LocalDiscovery (I.realize target))
      (found : (I.discoverState target).result = some relation) :
      DiscoveredHistory I (.extend prior step)

def discoverHistory (I : ConstitutiveOperationalInterface.{u})
    {source target : I.ConstitutiveState}
    (history : History I.ConstitutiveGenerator source target) :
    Option (I.DiscoveredHistory history) :=
  match history with
  | .root => some .root
  | .extend prior step =>
    match I.discoverHistory prior with
    | none => none
    | some previous =>
      match found : (I.discoverState target).result with
      | none => none
      | some relation => some (.extend step previous relation found)
termination_by structural history

theorem discoverHistory_failure (I : ConstitutiveOperationalInterface.{u})
    {source middle target : I.ConstitutiveState}
    (prior : History I.ConstitutiveGenerator source middle)
    (step : I.ConstitutiveGenerator middle target)
    (failed : (I.discoverState target).result = none) :
    I.discoverHistory (.extend prior step) = none := by
  unfold discoverHistory
  split
  · rfl
  · split
    · rfl
    · rename_i relation found
      rw [failed] at found
      cases found

end ConstitutiveOperationalInterface

/-- Every variable is tried; the result retains the variable returned by search. -/
def discoverCnfCandidate (formula : Cnf) (candidate : Var) :
    Option (Sigma fun endpoints :
      GeneratedStructuralBranchContext formula × GeneratedStructuralBranchContext formula =>
        Sigma fun splitVar => GeneratedStructuralFlipAtRelation splitVar endpoints.1 endpoints.2) :=
  let state := GeneratedStructuralBranchContext.root formula
  match tryEndogenousFlipCandidate state candidate with
  | none => none
  | some found => some
      ⟨(GeneratedStructuralBranchContext.child state candidate false found.fresh,
        GeneratedStructuralBranchContext.child state candidate true found.fresh),
        ⟨candidate, found.relation⟩⟩

/-- A closed constitutive producer with a chosen concrete SAT realization. -/
def cnfConstitutiveInterface
    (realize : PositiveConstitution Example.examplePresentation → Cnf) :
    ConstitutiveOperationalInterface where
  ConstitutiveState := PositiveConstitution Example.examplePresentation
  ConstitutiveGenerator := GeneratedStep
  OperationalState := Cnf
  Candidate := Var
  LocalState := GeneratedStructuralBranchContext
  OperationalRelation := fun _ source target =>
    Sigma fun splitVar => GeneratedStructuralFlipAtRelation splitVar source target
  Continuation := fun _ => GeneratedStructuralBranchContinuation
  Accept := fun continuation => GeneratedStructuralBranchAccept _ continuation
  generate := generate
  realize := realize
  extract := fun formula => (extractCnfCandidateRun formula).candidates
  discover := discoverCnfCandidate
  act := fun relation continuation => relation.2.mapContinuation continuation
  actPreservesAccept := fun relation continuation accepted =>
    relation.2.mapContinuation_accept continuation accepted

/-- This surface has an extracted candidate but no positive flip relation. -/
def asymmetricConstitutiveInterface : ConstitutiveOperationalInterface :=
  cnfConstitutiveInterface (fun _ => [[Literal.positive 0]])

theorem asymmetric_discovery_really_fails
    (state : PositiveConstitution Example.examplePresentation) :
    (asymmetricConstitutiveInterface.discoverState state).attempts = 1 ∧
      (asymmetricConstitutiveInterface.discoverState state).result = none := by
  exact ⟨rfl, rfl⟩

theorem produced_step_does_not_imply_discovery
    (source : PositiveConstitution Example.examplePresentation) :
    asymmetricConstitutiveInterface.discoverHistory
      (asymmetricConstitutiveInterface.produceHistory source 1).2 = none := by
  exact ConstitutiveOperationalInterface.discoverHistory_failure
    asymmetricConstitutiveInterface .root (generate source).2
    (asymmetric_discovery_really_fails _).2

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.explore
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.explore_tested
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.produceHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.discoverHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.discoverHistory_failure
#print axioms ConstitutiveSearch.EndogenousDecomposition.cnfConstitutiveInterface
#print axioms ConstitutiveSearch.EndogenousDecomposition.asymmetric_discovery_really_fails
#print axioms ConstitutiveSearch.EndogenousDecomposition.produced_step_does_not_imply_discovery
/- AXIOM_AUDIT_END -/
