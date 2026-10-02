import Init.Omega
import RelationalPerimeter.Computation.ConstitutiveSearch.SequentialPrimitiveExecution

/-!
# Searchable constituted transport codes

WitnessCompleteSequentialization assumes primitive search is complete on every
possible generator witness.  That assumption is stronger than necessary when
one concrete TransportCode is already constituted.

This module gives the exact local condition needed by a code itself.

A TransportCode is SearchableBy a primitive RelationSearch when:
* identity needs no search;
* every atom's endpoint pair is a primitive hit;
* both subcodes of a composition are searchable.

Under this code-local condition:
* the code can be converted directly to a PrimitiveHitPath;
* the path has exactly the same atom count;
* sequential execution costs one primitive query per atom and zero composition
  candidates.

This also characterizes GlobalCompositionRequired without executing bounded
global ClosureSearch: direct primitive miss plus existence of a searchable code
of size at least two.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace TransportCode

/--
Code-local executability through one announced primitive search.
-/
def SearchableBy
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    {source target : State} →
      TransportCode Generator source target →
        Prop
  | _, _, .identity _ =>
      True
  | source, target, .atom _ =>
      primitive.find source target ≠ none
  | _, _, .compose first second =>
      first.SearchableBy primitive ∧
        second.SearchableBy primitive

/--
A searchable transport code has a primitive-hit path with the same number of
atoms, without running global closure.
-/
theorem hasPrimitiveHitPath_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = code.size := by
  induction code with
  | identity state =>
      exact
        ⟨PrimitiveHitPath.identity state,
          rfl⟩
  | @atom source target witness =>
      cases found :
          primitive.find source target with
      | none =>
          exact
            False.elim
              (searchable found)
      | some executableWitness =>
          exact
            ⟨PrimitiveHitPath.step
                found
                (PrimitiveHitPath.identity target),
              rfl⟩
  | compose first second firstHypothesis secondHypothesis =>
      rcases searchable with
        ⟨firstSearchable, secondSearchable⟩
      rcases
          firstHypothesis firstSearchable with
        ⟨firstPath, firstLength⟩
      rcases
          secondHypothesis secondSearchable with
        ⟨secondPath, secondLength⟩
      refine
        ⟨firstPath.trans secondPath, ?_⟩
      rw [
        firstPath.trans_length,
        firstLength,
        secondLength
      ]
      rfl

/--
A searchable code executes sequentially with one primitive query per atom and
zero composition-candidate inspection.
-/
theorem hasSequentialExecution_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = code.size ∧
        (path.sequentialStats
            candidates
            fuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            candidates
            fuel).compositionCandidates =
          0 := by
  rcases
      code.hasPrimitiveHitPath_of_searchable
        primitive
        searchable with
    ⟨path, pathLength⟩
  refine
    ⟨path,
      pathLength,
      ?_,
      ?_⟩
  · calc
      (path.sequentialStats
          candidates
          fuel).primitiveQueries
          =
        path.length :=
          path.sequentialStats_primitiveQueries
            candidates
            fuel
            fuelPositive
      _ =
        code.size :=
          pathLength
  · exact
      path.sequentialStats_compositionCandidates
        candidates
        fuel
        fuelPositive

end TransportCode

namespace PrimitiveHitPath

/--
The TransportCode compiled from an executable primitive-hit path is searchable
by the same primitive search.
-/
theorem toTransportCode_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    path.toTransportCode.SearchableBy
      primitive := by
  induction path with
  | identity state =>
      exact True.intro
  | @step source middle target witness hit tail inductionHypothesis =>
      constructor
      · exact
          step_hit_ne_none
            hit
            tail
      · exact inductionHypothesis

/--
Global composition requirement is exactly direct primitive miss plus existence
of a searchable constituted code with at least two primitive atoms.

No global ClosureSearch execution is used in either direction.
-/
theorem globalCompositionRequired_iff_searchableCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) :
    GlobalCompositionRequired
        primitive
        source
        target ↔
      primitive.find source target = none ∧
        ∃ code :
            TransportClosure
              Generator
              source
              target,
          code.SearchableBy primitive ∧
            2 ≤ code.size := by
  constructor
  · intro required
    rcases required with
      ⟨directMiss, path, pathLength⟩
    refine
      ⟨directMiss,
        ⟨path.toTransportCode,
          path.toTransportCode_searchable,
          ?_⟩⟩
    rw [path.toTransportCode_size]
    exact pathLength
  · intro knownCode
    rcases knownCode with
      ⟨directMiss,
        code,
        searchable,
        codeSize⟩
    rcases
        code.hasPrimitiveHitPath_of_searchable
          primitive
          searchable with
      ⟨path, pathLength⟩
    refine
      ⟨directMiss,
        ⟨path, ?_⟩⟩
    rw [pathLength]
    exact codeSize

end PrimitiveHitPath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.TransportCode.SearchableBy
#print axioms ConstitutiveSearch.TransportCode.hasPrimitiveHitPath_of_searchable
#print axioms ConstitutiveSearch.TransportCode.hasSequentialExecution_of_searchable
#print axioms ConstitutiveSearch.PrimitiveHitPath.toTransportCode_searchable
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_iff_searchableCode
/- AXIOM_AUDIT_END -/
