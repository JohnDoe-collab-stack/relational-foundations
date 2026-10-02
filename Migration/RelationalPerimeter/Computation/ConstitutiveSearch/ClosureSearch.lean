import RelationalPerimeter.Computation.ConstitutiveSearch.TransportClosure

/-!
# Bounded executable search in transport-code closure

The free transport closure already exists as proof-relevant syntax. This module
adds an explicitly bounded executable search procedure.

The procedure is deliberately incomplete:
* it searches only through an explicit finite candidate list;
* it is bounded by a composition-depth fuel;
* none means only that this bounded search found no code.

The run object also counts source-level control-flow events:
* primitive relation queries;
* intermediate candidates tested for composition.

These counts are algorithmic counters for this search procedure, not wall-clock
runtime bounds.
-/

namespace ConstitutiveSearch

universe uGenerator

structure ClosureSearchStats where
  primitiveQueries : Nat
  compositionCandidates : Nat

namespace ClosureSearchStats

def zero : ClosureSearchStats :=
  { primitiveQueries := 0
    compositionCandidates := 0 }

def combine
    (left right : ClosureSearchStats) :
    ClosureSearchStats :=
  { primitiveQueries :=
      left.primitiveQueries + right.primitiveQueries
    compositionCandidates :=
      left.compositionCandidates +
        right.compositionCandidates }

def withPrimitiveQuery
    (stats : ClosureSearchStats) :
    ClosureSearchStats :=
  { primitiveQueries := stats.primitiveQueries + 1
    compositionCandidates :=
      stats.compositionCandidates }

def withCompositionCandidate
    (stats : ClosureSearchStats) :
    ClosureSearchStats :=
  { primitiveQueries := stats.primitiveQueries
    compositionCandidates :=
      stats.compositionCandidates + 1 }

end ClosureSearchStats

structure ClosureSearchRun
    {State : Type}
    (Generator : State → State → Type uGenerator)
    (source target : State) where
  code? :
    Option (TransportClosure Generator source target)
  stats : ClosureSearchStats

namespace ClosureSearchRun

def empty
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (source target : State) :
    ClosureSearchRun Generator source target :=
  { code? := none
    stats := ClosureSearchStats.zero }

end ClosureSearchRun

def searchClosureViaCandidates
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target) :
    (candidates : List State) →
      (source target : State) →
        ClosureSearchRun Generator source target
  | [], source, target =>
      ClosureSearchRun.empty source target
  | middle :: rest, source, target =>
      let first := recurse source middle
      match first.code? with
      | none =>
          let later :=
            searchClosureViaCandidates
              recurse
              rest
              source
              target
          { code? := later.code?
            stats :=
              ClosureSearchStats.withCompositionCandidate
                (ClosureSearchStats.combine
                  first.stats
                  later.stats) }
      | some firstCode =>
          let second := recurse middle target
          match second.code? with
          | some secondCode =>
              { code? :=
                  some
                    (TransportClosure.compose
                      firstCode
                      secondCode)
                stats :=
                  ClosureSearchStats.withCompositionCandidate
                    (ClosureSearchStats.combine
                      first.stats
                      second.stats) }
          | none =>
              let later :=
                searchClosureViaCandidates
                  recurse
                  rest
                  source
                  target
              { code? := later.code?
                stats :=
                  ClosureSearchStats.withCompositionCandidate
                    (ClosureSearchStats.combine
                      (ClosureSearchStats.combine
                        first.stats
                        second.stats)
                      later.stats) }

def searchTransportClosureBounded
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State) :
    (fuel : Nat) →
      (source target : State) →
        ClosureSearchRun Generator source target
  | 0, source, target =>
      ClosureSearchRun.empty source target
  | fuel + 1, source, target =>
      match primitive.find source target with
      | some witness =>
          { code? :=
              some
                (TransportClosure.ofGenerator witness)
            stats :=
              ClosureSearchStats.withPrimitiveQuery
                ClosureSearchStats.zero }
      | none =>
          let via :=
            searchClosureViaCandidates
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              candidates
              source
              target
          { code? := via.code?
            stats :=
              ClosureSearchStats.withPrimitiveQuery
                via.stats }

def boundedTransportClosureSearch
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat) :
    RelationSearch (TransportClosure Generator) :=
  { find := fun source target =>
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).code? }

theorem boundedTransportClosureSearch_find
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State) :
    (boundedTransportClosureSearch
      primitive candidates fuel).find source target =
      (searchTransportClosureBounded
        primitive candidates fuel source target).code? :=
  rfl

theorem boundedClosure_zero_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (source target : State) :
    (searchTransportClosureBounded
      primitive candidates 0 source target).stats.primitiveQueries =
      0 := by
  rfl

theorem boundedClosure_zero_compositionCandidates
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (source target : State) :
    (searchTransportClosureBounded
      primitive candidates 0 source target).stats.compositionCandidates =
      0 := by
  rfl

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ClosureSearchStats
#print axioms ConstitutiveSearch.ClosureSearchStats.combine
#print axioms ConstitutiveSearch.ClosureSearchRun
#print axioms ConstitutiveSearch.searchClosureViaCandidates
#print axioms ConstitutiveSearch.searchTransportClosureBounded
#print axioms ConstitutiveSearch.boundedTransportClosureSearch
#print axioms ConstitutiveSearch.boundedTransportClosureSearch_find
#print axioms ConstitutiveSearch.boundedClosure_zero_primitiveQueries
#print axioms ConstitutiveSearch.boundedClosure_zero_compositionCandidates
/- AXIOM_AUDIT_END -/
