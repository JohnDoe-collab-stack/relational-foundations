import RelationalPerimeter.Computation.ConstitutiveSearch.ClosureSearch
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

set_option linter.unusedVariables false

/-!
# Sequential execution of certified primitive-hit paths

Global closure can ask for a relation between distant endpoints even when the
constitutive path between them is already known edge by edge.

This module factors the generic object behind the SAT separators:
a finite path whose every edge is an executable primitive-search hit.

Such a path has three distinct readings:
* proof-relevant sequential structure;
* a finite TransportCode obtained by composing its primitive witnesses;
* an actual sequential ClosureSearch execution.

The sequential execution theorem is exact.  For every positive fuel and every
candidate list, a path of length k executes as:
* exactly k primitive queries;
* zero composition candidates.

Thus a direct primitive miss between the endpoints can coexist with a fully
primitive sequential realization.  In that situation composition is required
only by the global endpoint query, not by execution of the constituted path.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
A finite path of primitive-search hits.

Each edge stores the exact witness returned by the announced RelationSearch.
-/
inductive PrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    State → State → Type uGenerator where
  | identity
      (state : State) :
      PrimitiveHitPath primitive state state
  | step
      {source middle target : State}
      {witness : Generator source middle}
      (hit :
        primitive.find source middle =
          some witness)
      (tail :
        PrimitiveHitPath
          primitive
          middle
          target) :
      PrimitiveHitPath
        primitive
        source
        target

namespace PrimitiveHitPath

/-- Number of primitive edges in the path. -/
def length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State} :
    PrimitiveHitPath primitive source target → Nat
  | .identity _ =>
      0
  | .step _ tail =>
      tail.length + 1

/-- Compile a primitive-hit path into the free transport closure. -/
def toTransportCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State} :
    PrimitiveHitPath primitive source target →
      TransportClosure Generator source target
  | .identity state =>
      .identity state
  | .step (witness := witness) _ tail =>
      .compose
        (.atom witness)
        tail.toTransportCode

/-- Compilation preserves exactly the number of primitive generator atoms. -/
theorem toTransportCode_size
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    path.toTransportCode.size =
      path.length := by
  induction path with
  | identity state =>
      rfl
  | step hit tail inductionHypothesis =>
      change
        1 + tail.toTransportCode.size =
          tail.length + 1
      rw [inductionHypothesis]
      exact Nat.add_comm 1 tail.length


/-- Concatenate two executable primitive-hit paths. -/
def trans
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source middle target : State}
    (first :
      PrimitiveHitPath
        primitive
        source
        middle)
    (second :
      PrimitiveHitPath
        primitive
        middle
        target) :
    PrimitiveHitPath
      primitive
      source
      target :=
  match first with
  | .identity _ =>
      second
  | .step hit tail =>
      .step
        hit
        (tail.trans second)

/-- Concatenation adds primitive-edge lengths. -/
theorem trans_length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source middle target : State}
    (first :
      PrimitiveHitPath
        primitive
        source
        middle)
    (second :
      PrimitiveHitPath
        primitive
        middle
        target) :
    (first.trans second).length =
      first.length + second.length := by
  induction first with
  | identity state =>
      exact
        (Nat.zero_add second.length).symm
  | step hit tail inductionHypothesis =>
      calc
        (tail.trans second).length + 1 =
            (tail.length + second.length) + 1 :=
          congrArg
            (fun value => value + 1)
            (inductionHypothesis second)
        _ = tail.length + (second.length + 1) :=
          Nat.add_assoc
            tail.length
            second.length
            1
        _ = tail.length + (1 + second.length) :=
          congrArg
            (Nat.add tail.length)
            (Nat.add_comm second.length 1)
        _ = (tail.length + 1) + second.length :=
          (Nat.add_assoc
            tail.length
            1
            second.length).symm

/--
Aggregate actual ClosureSearch statistics obtained by following path edges
sequentially.

The same candidate list and fuel are supplied to every edge run; primitive hits
make those global parameters irrelevant to the successful edge itself.
-/
def sequentialStats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat) :
    {source target : State} →
      PrimitiveHitPath
        primitive
        source
        target →
      ClosureSearchStats
  | _, _, .identity _ =>
      ClosureSearchStats.zero
  | source, _, .step (middle := middle) _ tail =>
      ClosureSearchStats.combine
        (searchTransportClosureBounded
          primitive
          candidates
          fuel
          source
          middle).stats
        (sequentialStats
          candidates
          fuel
          tail)

/--
A positive-fuel ClosureSearch query that is already a primitive hit performs
exactly one primitive query and no composition-candidate inspection.
-/
theorem primitiveHit_run_stats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (fuelPositive : 0 < fuel)
    (primitiveHit :
      primitive.find source target ≠ none) :
    let run :=
      searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target
    run.stats.primitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 := by
  cases fuel with
  | zero =>
      nomatch fuelPositive
  | succ fuel =>
      cases found :
          primitive.find source target with
      | none =>
          exact False.elim (primitiveHit found)
      | some witness =>
          rw [
            searchTransportClosureBounded,
            found
          ]
          exact ⟨rfl, rfl⟩

/-- Every stored edge is a non-none primitive hit. -/
theorem step_hit_ne_none
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source middle target : State}
    {witness : Generator source middle}
    (hit :
      primitive.find source middle =
        some witness)
    (tail :
      PrimitiveHitPath
        primitive
        middle
        target) :
    primitive.find source middle ≠ none := by
  rw [hit]
  intro impossible
  cases impossible

/--
Sequential execution performs exactly one primitive query per certified edge.
-/
theorem sequentialStats_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    (path.sequentialStats
      candidates
      fuel).primitiveQueries =
        path.length := by
  induction path with
  | identity state =>
      rfl
  | @step source middle target witness hit tail inductionHypothesis =>
      have edgeStats :=
        primitiveHit_run_stats
          primitive
          candidates
          fuel
          source
          middle
          fuelPositive
          (step_hit_ne_none
            hit
            tail)
      calc
        (sequentialStats
            candidates
            fuel
            (.step hit tail)).primitiveQueries =
            (searchTransportClosureBounded
                primitive
                candidates
                fuel
                source
                middle).stats.primitiveQueries +
              (tail.sequentialStats
                candidates
                fuel).primitiveQueries := rfl
        _ = 1 +
              (tail.sequentialStats
                candidates
                fuel).primitiveQueries :=
          congrArg
            (fun value =>
              value +
                (tail.sequentialStats
                  candidates
                  fuel).primitiveQueries)
            edgeStats.1
        _ = 1 + tail.length :=
          congrArg
            (Nat.add 1)
            inductionHypothesis
        _ = tail.length + 1 :=
          Nat.add_comm 1 tail.length

/--
Sequential execution never inspects a composition candidate: every edge
short-circuits at the primitive layer.
-/
theorem sequentialStats_compositionCandidates
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    (path.sequentialStats
      candidates
      fuel).compositionCandidates =
        0 := by
  induction path with
  | identity state =>
      rfl
  | @step source middle target witness hit tail inductionHypothesis =>
      have edgeStats :=
        primitiveHit_run_stats
          primitive
          candidates
          fuel
          source
          middle
          fuelPositive
          (step_hit_ne_none
            hit
            tail)
      calc
        (sequentialStats
            candidates
            fuel
            (.step hit tail)).compositionCandidates =
            (searchTransportClosureBounded
                primitive
                candidates
                fuel
                source
                middle).stats.compositionCandidates +
              (tail.sequentialStats
                candidates
                fuel).compositionCandidates := rfl
        _ = 0 +
              (tail.sequentialStats
                candidates
                fuel).compositionCandidates :=
          congrArg
            (fun value =>
              value +
                (tail.sequentialStats
                  candidates
                  fuel).compositionCandidates)
            edgeStats.2
        _ = 0 + 0 :=
          congrArg
            (Nat.add 0)
            inductionHypothesis
        _ = 0 := rfl


/--
If a primitive-hit path has length one, its endpoints are themselves a direct
primitive hit.
-/
theorem directHit_of_length_one
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target)
    (lengthOne :
      path.length = 1) :
    primitive.find source target ≠ none := by
  cases path with
  | identity state =>
      change 0 = 1 at lengthOne
      cases lengthOne
  | @step source middle target witness hit tail =>
      cases tail with
      | identity state =>
          rw [hit]
          intro impossible
          cases impossible
      | step tailHit rest =>
          change
            (rest.length + 1) + 1 = 1 at lengthOne
          have impossible :
              Nat.succ rest.length = 0 :=
            Nat.succ.inj lengthOne
          cases impossible

/--
Whenever the candidate-recursion layer returns a code, it carries an executable
primitive-hit path with the same atom count.

The hypothesis states the corresponding property for each recursive subquery.
-/
theorem searchClosureViaCandidates_found_hasPrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target)
    (recursePath :
      ∀ (source target : State)
        (code :
          TransportClosure
            Generator
            source
            target),
        (recurse source target).code? =
            some code →
          ∃ path :
              PrimitiveHitPath
                primitive
                source
                target,
            0 < path.length ∧
              path.length = code.size) :
    ∀ (candidates : List State)
      (source target : State)
      (code :
        TransportClosure
          Generator
          source
          target),
      (searchClosureViaCandidates
        recurse
        candidates
        source
        target).code? =
          some code →
        ∃ path :
            PrimitiveHitPath
              primitive
              source
              target,
          0 < path.length ∧
            path.length = code.size := by
  intro candidates
  induction candidates with
  | nil =>
      intro source target code found
      change
        (none :
          Option
            (TransportClosure
              Generator
              source
              target)) =
          some code at found
      cases found
  | cons middle rest inductionHypothesis =>
      intro source target code found
      cases firstResult :
          (recurse source middle).code? with
      | none =>
          rw [
            searchClosureViaCandidates,
            firstResult
          ] at found
          exact
            inductionHypothesis
              source
              target
              code
              found
      | some firstCode =>
          cases secondResult :
              (recurse middle target).code? with
          | none =>
              rw [searchClosureViaCandidates] at found
              rw [firstResult] at found
              dsimp only at found
              rw [secondResult] at found
              exact
                inductionHypothesis
                  source
                  target
                  code
                  found
          | some secondCode =>
              rw [searchClosureViaCandidates] at found
              rw [firstResult] at found
              dsimp only at found
              rw [secondResult] at found
              injection found with codeExact
              subst code
              rcases
                  recursePath
                    source
                    middle
                    firstCode
                    firstResult with
                ⟨firstPath,
                  firstPositive,
                  firstLength⟩
              rcases
                  recursePath
                    middle
                    target
                    secondCode
                    secondResult with
                ⟨secondPath,
                  secondPositive,
                  secondLength⟩
              let path :=
                firstPath.trans
                  secondPath
              refine
                ⟨path, ?_, ?_⟩
              · have positiveSum :
                    0 < firstPath.length +
                      secondPath.length :=
                  Nat.lt_of_lt_of_le
                    firstPositive
                    (Nat.le_add_right
                      firstPath.length
                      secondPath.length)
                exact
                  (trans_length
                    firstPath
                    secondPath).symm ▸
                    positiveSum
              · calc
                  path.length =
                      firstPath.length +
                        secondPath.length :=
                    trans_length
                      firstPath
                      secondPath
                  _ = firstCode.size +
                        secondPath.length :=
                    congrArg
                      (fun value =>
                        value + secondPath.length)
                      firstLength
                  _ = firstCode.size +
                        secondCode.size :=
                    congrArg
                      (Nat.add firstCode.size)
                      secondLength

/--
Every code actually found by bounded ClosureSearch has an executable
primitive-hit path with exactly the same number of primitive atoms.
-/
theorem searchTransportClosureBounded_found_hasPrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State) :
    ∀ (fuel : Nat)
      (source target : State)
      (code :
        TransportClosure
          Generator
          source
          target),
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).code? =
          some code →
        ∃ path :
            PrimitiveHitPath
              primitive
              source
              target,
          0 < path.length ∧
            path.length = code.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target code found
      simp only [
        searchTransportClosureBounded,
        ClosureSearchRun.empty
      ] at found
      cases found
  | succ fuel inductionHypothesis =>
      intro source target code found
      cases direct :
          primitive.find source target with
      | some witness =>
          simp only [
            searchTransportClosureBounded,
            direct
          ] at found
          injection found with codeExact
          subst code
          let path :
              PrimitiveHitPath
                primitive
                source
                target :=
            .step
              direct
              (.identity target)
          refine
            ⟨path, ?_, ?_⟩
          · change 0 < 1
            exact Nat.zero_lt_succ 0
          · change 1 = 1
            rfl
      | none =>
          simp only [
            searchTransportClosureBounded,
            direct
          ] at found
          exact
            searchClosureViaCandidates_found_hasPrimitiveHitPath
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              (fun left right recursiveCode recursiveFound =>
                inductionHypothesis
                  left
                  right
                  recursiveCode
                  recursiveFound)
              candidates
              source
              target
              code
              found

/--
A global endpoint query is composition-required relative to a primitive search
when the direct primitive query misses while a certified primitive-hit path of
length at least two connects the same endpoints.
-/
def GlobalCompositionRequired
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) : Prop :=
  primitive.find source target = none ∧
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      2 ≤ path.length

/--
Any nonempty candidate layer executes at least one composition-candidate
inspection, independently of whether the first or a later candidate succeeds.
-/
theorem searchClosureViaCandidates_cons_compositionCandidates_pos
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target)
    (middle : State)
    (rest : List State)
    (source target : State) :
    0 <
      (searchClosureViaCandidates
        recurse
        (middle :: rest)
        source
        target).stats.compositionCandidates := by
  cases firstResult :
      (recurse source middle).code? with
  | none =>
      simp only [
        searchClosureViaCandidates,
        firstResult,
        ClosureSearchStats.withCompositionCandidate,
        ClosureSearchStats.combine
      ]
      exact Nat.zero_lt_succ _
  | some firstCode =>
      cases secondResult :
          (recurse middle target).code? with
      | none =>
          simp only [
            searchClosureViaCandidates,
            firstResult,
            secondResult,
            ClosureSearchStats.withCompositionCandidate,
            ClosureSearchStats.combine
          ]
          exact Nat.zero_lt_succ _
      | some secondCode =>
          simp only [
            searchClosureViaCandidates,
            firstResult,
            secondResult,
            ClosureSearchStats.withCompositionCandidate,
            ClosureSearchStats.combine
          ]
          exact Nat.zero_lt_succ _

/--
If the direct primitive query misses but bounded ClosureSearch still succeeds,
the actual global run necessarily inspects at least one composition candidate.
-/
theorem searchTransportClosureBounded_directMiss_found_compositionCandidates_pos
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (directMiss :
      primitive.find source target = none)
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).code? =
          some code) :
    0 <
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).stats.compositionCandidates := by
  cases fuel with
  | zero =>
      simp only [
        searchTransportClosureBounded,
        ClosureSearchRun.empty
      ] at found
      cases found
  | succ fuel =>
      cases candidates with
      | nil =>
          simp only [
            searchTransportClosureBounded,
            directMiss,
            searchClosureViaCandidates,
            ClosureSearchRun.empty
          ] at found
          cases found
      | cons middle rest =>
          simp only [
            searchTransportClosureBounded,
            directMiss,
            ClosureSearchStats.withPrimitiveQuery
          ]
          exact
            searchClosureViaCandidates_cons_compositionCandidates_pos
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  (middle :: rest)
                  fuel
                  left
                  right)
              middle
              rest
              source
              target

/--
Every successfully found closure code admits a sequential replacement through
the primitive-hit path reconstructed from the same executable search result.

The replacement may use any positive fuel and any candidate list because each
stored edge short-circuits at the primitive layer.
-/
theorem searchTransportClosureBounded_found_hasSequentialReplacement
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (globalCandidates : List State)
    (globalFuel : Nat)
    (source target : State)
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchTransportClosureBounded
        primitive
        globalCandidates
        globalFuel
        source
        target).code? =
          some code)
    (sequentialCandidates : List State)
    (sequentialFuel : Nat)
    (sequentialFuelPositive :
      0 < sequentialFuel) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = code.size ∧
        (path.sequentialStats
            sequentialCandidates
            sequentialFuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            sequentialCandidates
            sequentialFuel).compositionCandidates =
          0 := by
  rcases
      searchTransportClosureBounded_found_hasPrimitiveHitPath
        primitive
        globalCandidates
        globalFuel
        source
        target
        code
        found with
    ⟨path, _pathPositive, pathLength⟩
  refine
    ⟨path, pathLength, ?_, ?_⟩
  · calc
      (path.sequentialStats
          sequentialCandidates
          sequentialFuel).primitiveQueries
          =
        path.length :=
          path.sequentialStats_primitiveQueries
            sequentialCandidates
            sequentialFuel
            sequentialFuelPositive
      _ =
        code.size :=
          pathLength
  · exact
      path.sequentialStats_compositionCandidates
        sequentialCandidates
        sequentialFuel
        sequentialFuelPositive

/--
If the successful global query is a direct primitive miss, the replacement path
has at least two edges while the global run necessarily performs composition
candidate search and the sequential replacement performs none.
-/
theorem searchTransportClosureBounded_directMiss_found_hasSequentialReplacement
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (globalCandidates : List State)
    (globalFuel : Nat)
    (source target : State)
    (directMiss :
      primitive.find source target = none)
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchTransportClosureBounded
        primitive
        globalCandidates
        globalFuel
        source
        target).code? =
          some code)
    (sequentialCandidates : List State)
    (sequentialFuel : Nat)
    (sequentialFuelPositive :
      0 < sequentialFuel) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      2 ≤ path.length ∧
        path.length = code.size ∧
        0 <
          (searchTransportClosureBounded
            primitive
            globalCandidates
            globalFuel
            source
            target).stats.compositionCandidates ∧
        (path.sequentialStats
            sequentialCandidates
            sequentialFuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            sequentialCandidates
            sequentialFuel).compositionCandidates =
          0 := by
  rcases
      searchTransportClosureBounded_found_hasPrimitiveHitPath
        primitive
        globalCandidates
        globalFuel
        source
        target
        code
        found with
    ⟨path, pathPositive, pathLength⟩
  have pathNotOne :
      path.length ≠ 1 := by
    intro pathOne
    exact
      (directHit_of_length_one
        path
        pathOne)
        directMiss
  have twoLe :
      2 ≤ path.length := by
    exact
      Constructive.two_le_of_pos_of_ne_one
        pathPositive
        pathNotOne
  have globalCompositionPositive :
      0 <
        (searchTransportClosureBounded
          primitive
          globalCandidates
          globalFuel
          source
          target).stats.compositionCandidates :=
    searchTransportClosureBounded_directMiss_found_compositionCandidates_pos
      primitive
      globalCandidates
      globalFuel
      source
      target
      directMiss
      found
  refine
    ⟨path,
      twoLe,
      pathLength,
      globalCompositionPositive,
      ?_,
      ?_⟩
  · calc
      (path.sequentialStats
          sequentialCandidates
          sequentialFuel).primitiveQueries
          =
        path.length :=
          path.sequentialStats_primitiveQueries
            sequentialCandidates
            sequentialFuel
            sequentialFuelPositive
      _ =
        code.size :=
          pathLength
  · exact
      path.sequentialStats_compositionCandidates
        sequentialCandidates
        sequentialFuel
        sequentialFuelPositive

/--
A successful bounded closure query whose direct primitive query misses is
necessarily a genuine global composition requirement.
-/
theorem searchTransportClosureBounded_directMiss_found_requiresComposition
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (directMiss :
      primitive.find source target = none)
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).code? =
          some code) :
    GlobalCompositionRequired
      primitive
      source
      target := by
  rcases
      searchTransportClosureBounded_found_hasPrimitiveHitPath
        primitive
        candidates
        fuel
        source
        target
        code
        found with
    ⟨path, pathPositive, pathLength⟩
  have pathNotOne :
      path.length ≠ 1 := by
    intro pathOne
    exact
      (directHit_of_length_one
        path
        pathOne)
        directMiss
  have twoLe :
      2 ≤ path.length := by
    exact
      Constructive.two_le_of_pos_of_ne_one
        pathPositive
        pathNotOne
  exact
    ⟨directMiss,
      ⟨path, twoLe⟩⟩

/--
The code returned in a direct-miss success has at least two primitive atoms.
-/
theorem searchTransportClosureBounded_directMiss_found_codeSize
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (directMiss :
      primitive.find source target = none)
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).code? =
          some code) :
    2 ≤ code.size := by
  rcases
      searchTransportClosureBounded_found_hasPrimitiveHitPath
        primitive
        candidates
        fuel
        source
        target
        code
        found with
    ⟨path, pathPositive, pathLength⟩
  have pathNotOne :
      path.length ≠ 1 := by
    intro pathOne
    exact
      (directHit_of_length_one
        path
        pathOne)
        directMiss
  have twoLe :
      2 ≤ path.length := by
    exact
      Constructive.two_le_of_pos_of_ne_one
        pathPositive
        pathNotOne
  exact pathLength ▸ twoLe

/--
A global composition requirement carries an explicit closure code with at least
two primitive atoms.
-/
theorem globalCompositionRequired_hasCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (required :
      GlobalCompositionRequired
        primitive
        source
        target) :
    ∃ code :
        TransportClosure
          Generator
          source
          target,
      2 ≤ code.size := by
  rcases required with
    ⟨_directMiss, path, pathLength⟩
  exact
    ⟨path.toTransportCode,
      by
        rw [path.toTransportCode_size]
        exact pathLength⟩

/--
A global composition requirement can still be executed sequentially without any
composition-candidate search once its constituted primitive path is retained.
-/
theorem globalCompositionRequired_hasSequentialExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (required :
      GlobalCompositionRequired
        primitive
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      2 ≤ path.length ∧
        (path.sequentialStats
            candidates
            fuel).primitiveQueries =
          path.length ∧
        (path.sequentialStats
            candidates
            fuel).compositionCandidates =
          0 := by
  rcases required with
    ⟨_directMiss, path, pathLength⟩
  exact
    ⟨path,
      pathLength,
      path.sequentialStats_primitiveQueries
        candidates
        fuel
        fuelPositive,
      path.sequentialStats_compositionCandidates
        candidates
        fuel
        fuelPositive⟩

end PrimitiveHitPath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveHitPath
#print axioms ConstitutiveSearch.PrimitiveHitPath.length
#print axioms ConstitutiveSearch.PrimitiveHitPath.toTransportCode
#print axioms ConstitutiveSearch.PrimitiveHitPath.toTransportCode_size
#print axioms ConstitutiveSearch.PrimitiveHitPath.trans
#print axioms ConstitutiveSearch.PrimitiveHitPath.trans_length
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats
#print axioms ConstitutiveSearch.PrimitiveHitPath.primitiveHit_run_stats
#print axioms ConstitutiveSearch.PrimitiveHitPath.step_hit_ne_none
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_primitiveQueries
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_compositionCandidates
#print axioms ConstitutiveSearch.PrimitiveHitPath.directHit_of_length_one
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchClosureViaCandidates_found_hasPrimitiveHitPath
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_found_hasPrimitiveHitPath
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchClosureViaCandidates_cons_compositionCandidates_pos
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_compositionCandidates_pos
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_found_hasSequentialReplacement
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_hasSequentialReplacement
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_requiresComposition
#print axioms ConstitutiveSearch.PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_codeSize
#print axioms ConstitutiveSearch.PrimitiveHitPath.GlobalCompositionRequired
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_hasCode
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_hasSequentialExecution
/- AXIOM_AUDIT_END -/
