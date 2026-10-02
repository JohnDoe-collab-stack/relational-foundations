import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryExecution

/-!
# Honest interface between constitution and local operational search

The two relations are distinct fields.  `ConstitutiveGenerator` produces a new
constituted state.  `OperationalRelation` is returned only by `discover` after
that state has been realized and candidates have been extracted.  The
interface contains no map from a constitutive generator witness to an
operational relation, code, or action.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open ConstitutiveGeneration
open SAT

universe u

structure ConstitutiveOperationalInterface where
  ConstitutiveState : Type u
  ConstitutiveGenerator : ConstitutiveState → ConstitutiveState → Type u
  OperationalState : Type u
  Candidate : Type u
  LocalState : OperationalState → Type u
  OperationalRelation :
    (operational : OperationalState) →
      LocalState operational → LocalState operational → Type u
  Continuation :
    (operational : OperationalState) → LocalState operational → Type u
  Accept :
    {operational : OperationalState} →
      {localState : LocalState operational} →
        Continuation operational localState → Prop
  generate :
    (source : ConstitutiveState) →
      Sigma fun target => ConstitutiveGenerator source target
  realize : ConstitutiveState → OperationalState
  extract : (operational : OperationalState) → List Candidate
  discover :
    (operational : OperationalState) →
      Candidate →
      Option
        (Sigma fun endpoints : LocalState operational × LocalState operational =>
          OperationalRelation operational endpoints.1 endpoints.2)
  act :
    {operational : OperationalState} →
      {source target : LocalState operational} →
      OperationalRelation operational source target →
      Continuation operational source → Continuation operational target
  actPreservesAccept :
    {operational : OperationalState} →
      {source target : LocalState operational} →
      (relation : OperationalRelation operational source target) →
      (continuation : Continuation operational source) →
      Accept continuation → Accept (act relation continuation)

def concreteOperationalDiscover
    (searchIndex candidate : Nat) :
    Option
      (Sigma fun endpoints :
          GeneratedStructuralBranchContext
              (distinctGrowingDiscoveryFormula searchIndex) ×
            GeneratedStructuralBranchContext
              (distinctGrowingDiscoveryFormula searchIndex) =>
        Sigma fun splitVar => GeneratedStructuralFlipAtRelation
          (rootFormula := distinctGrowingDiscoveryFormula searchIndex)
          splitVar endpoints.1 endpoints.2) :=
    match tryEndogenousFlipCandidate
        (distinctGrowingDiscoveryRoot searchIndex)
        candidate with
    | none => none
    | some discovery =>
        some
          ⟨(GeneratedStructuralBranchContext.child
              (distinctGrowingDiscoveryRoot searchIndex)
              candidate false discovery.fresh,
            GeneratedStructuralBranchContext.child
              (distinctGrowingDiscoveryRoot searchIndex)
              candidate true discovery.fresh),
            ⟨candidate, discovery.relation⟩⟩

/--
Concrete closed instance of the generic interface.  Constitution is carried by
`PositiveConstitution` and `GeneratedStep`; its operational realization is only
the search index read from the constituted state.  Discovery still has to run
on the realized root before any operational relation exists.
-/
abbrev concreteConstitutiveOperationalInterface :
    ConstitutiveOperationalInterface where
  ConstitutiveState := PositiveConstitution examplePresentation
  ConstitutiveGenerator := GeneratedStep
  OperationalState := Nat
  Candidate := Var
  LocalState := fun searchIndex =>
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula searchIndex)
  OperationalRelation := fun searchIndex source target =>
    Sigma fun splitVar => GeneratedStructuralFlipAtRelation
      (rootFormula := distinctGrowingDiscoveryFormula searchIndex)
      splitVar
      source
      target
  Continuation := fun _searchIndex localState =>
    GeneratedStructuralBranchContinuation localState
  Accept := fun continuation =>
    GeneratedStructuralBranchAccept _ continuation
  generate := generate
  realize := fun constituted => 2 * positiveDepth constituted
  extract := fun searchIndex =>
    (runCandidateExtraction
      (distinctGrowingDiscoveryRoot searchIndex)).candidates
  discover := concreteOperationalDiscover
  act := fun relation continuation =>
    relation.2.mapContinuation continuation
  actPreservesAccept := fun relation continuation accepted =>
    relation.2.mapContinuation_accept continuation accepted

/-- The closed interface realizes a produced endpoint by its exact search index. -/
theorem concreteInterface_realize_constitutedEndpoint (depth : Nat) :
    concreteConstitutiveOperationalInterface.realize
        (constitutedEndpoint depth) =
      constitutedSearchIndex depth :=
  rfl

/-- The concrete interface closes discovery on its useful extracted variable. -/
theorem concreteInterface_discover_selected (searchIndex : Nat) :
    concreteConstitutiveOperationalInterface.discover
        searchIndex
        (growingDiscoverySplitVar searchIndex) ≠
      none := by
  change
    concreteOperationalDiscover
        searchIndex
        (growingDiscoverySplitVar searchIndex) ≠ none
  unfold concreteOperationalDiscover
  cases found : tryEndogenousFlipCandidate
      (distinctGrowingDiscoveryRoot searchIndex)
      (growingDiscoverySplitVar searchIndex) with
  | none =>
      exact
        False.elim
          ((distinctGrowingDiscoveryUsefulCandidate_found searchIndex) found)
  | some discovery =>
      intro impossible
      cases impossible

/--
Concrete realization object.  It retains the constituted endpoint and the
operational stage as different data connected by exact readout equations.
-/
structure RealizedConstitutiveStage (depth : Nat) : Type 2 where
  constituted : PositiveConstitution examplePresentation
  constitutedExact : constituted = constitutedEndpoint depth
  operational : ConstitutiveOperationalStage depth
  operationalExact : operational = constructStage depth
  readoutExact : operational.operationalIndex = positiveDepth constituted
  searchIndexExact : operational.searchIndex = 2 * positiveDepth constituted

def realizeConstitutedStage (depth : Nat) : RealizedConstitutiveStage depth :=
  { constituted := constitutedEndpoint depth
    constitutedExact := rfl
    operational := constructStage depth
    operationalExact := rfl
    readoutExact := rfl
    searchIndexExact := rfl }

/-- Realization recovers exactly the constituted endpoint readout. -/
theorem realizeConstitutedStage_roundTrip (depth : Nat) :
    (realizeConstitutedStage depth).operational.operationalIndex =
      positiveDepth (realizeConstitutedStage depth).constituted :=
  (realizeConstitutedStage depth).readoutExact

/--
The concrete operational relation stored by a run is exactly the relation
returned by its discovery; it is not obtained from `run.generation`.
-/
theorem concreteRelation_comes_from_discovery
    {depth : Nat}
    {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.schedule.entry.relation = run.discovery.relation := by
  cases run.scheduleExact
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteOperationalDiscover
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteConstitutiveOperationalInterface
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteInterface_realize_constitutedEndpoint
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteInterface_discover_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeConstitutedStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeConstitutedStage_roundTrip
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteRelation_comes_from_discovery
/- AXIOM_AUDIT_END -/
