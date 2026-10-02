import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalTransport

/-!
# Search-relative irreducible frontiers

This module gives a precise, deliberately relative meaning to frontier
irreducibility.

A frontier is search-irreducible when the supplied executable relation search
finds no directional witness between any earlier state and any later state.
This is not a theorem that no mathematical relation witness exists.  Search
failure and semantic non-existence remain distinct.

For a two-state frontier, a certified pair search records both positive
witnesses and negative search outcomes.  It then constructs a reduced frontier,
a completion-preserving frontier transport, and a proof that the retained
frontier is irreducible relative to that search procedure.
-/

namespace ConstitutiveSearch

universe uState uRelation uCompletion

/--
No relation witness is found in either direction between any head state and a
later state, recursively through the finite frontier.
-/
def SearchIrreducible
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation) : List State → Prop
  | [] => True
  | state :: rest =>
      (∀ other : State,
        other ∈ rest →
          search.find state other = none ∧
            search.find other state = none) ∧
      SearchIrreducible search rest

namespace SearchIrreducible

/-- The empty frontier is search-irreducible. -/
theorem nil
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation) :
    SearchIrreducible search [] :=
  True.intro

/-- Every singleton frontier is search-irreducible. -/
theorem singleton
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (state : State) :
    SearchIrreducible search [state] := by
  constructor
  · intro other member
    cases member
  · exact nil search

/-- A two-state frontier is search-irreducible when both directional searches fail. -/
theorem pair
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (left right : State)
    (forwardNotFound : search.find left right = none)
    (backwardNotFound : search.find right left = none) :
    SearchIrreducible search [left, right] := by
  constructor
  · intro other member
    cases member with
    | head =>
        exact ⟨forwardNotFound, backwardNotFound⟩
    | tail _ tailMember =>
        cases tailMember
  · exact singleton search right

end SearchIrreducible

/--
Witness-carrying result of searching a pair in both directions, including the
actual `none` equalities when a direction is not found.
-/
inductive CertifiedPairSearchResult
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (left right : State) where
  | bidirectional
      (forward : Relation left right)
      (backward : Relation right left)
      (forwardFound : search.find left right = some forward)
      (backwardFound : search.find right left = some backward) :
      CertifiedPairSearchResult search left right
  | forwardOnly
      (forward : Relation left right)
      (forwardFound : search.find left right = some forward)
      (backwardNotFound : search.find right left = none) :
      CertifiedPairSearchResult search left right
  | backwardOnly
      (backward : Relation right left)
      (forwardNotFound : search.find left right = none)
      (backwardFound : search.find right left = some backward) :
      CertifiedPairSearchResult search left right
  | unresolved
      (forwardNotFound : search.find left right = none)
      (backwardNotFound : search.find right left = none) :
      CertifiedPairSearchResult search left right

namespace RelationSearch

/-- Search both pair directions while retaining the exact search equations. -/
def classifyPairCertified
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (left right : State) :
    CertifiedPairSearchResult search left right :=
  match forwardFound : search.find left right with
  | some forward =>
      match backwardFound : search.find right left with
      | some backward =>
          .bidirectional forward backward forwardFound backwardFound
      | none =>
          .forwardOnly forward forwardFound backwardFound
  | none =>
      match backwardFound : search.find right left with
      | some backward =>
          .backwardOnly backward forwardFound backwardFound
      | none =>
          .unresolved forwardFound backwardFound

end RelationSearch

/--
A reduced pair frontier together with the constructive transport from the
original pair and a proof of search-relative irreducibility of the retained
frontier.
-/
structure PairFrontierReduction
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (left right : State) where
  retained : List State
  transport : FrontierTransport Completion [left, right] retained
  irreducible : SearchIrreducible search retained

namespace PairFrontierReduction

/-- The number of retained states after certified pair reduction. -/
def width
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {left right : State}
    (reduction : PairFrontierReduction (Completion := Completion) search left right) : Nat :=
  reduction.retained.length

end PairFrontierReduction

/--
Reduce a pair using exactly the relation witnesses found by the certified
classification.  A forward witness retains the right state, a backward witness
retains the left state, and an unresolved pair is retained unchanged.
-/
def reduceCertifiedPair
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (left right : State)
    (classification : CertifiedPairSearchResult search left right) :
    PairFrontierReduction (Completion := Completion) search left right :=
  match classification with
  | .bidirectional forward _backward _ _ =>
      { retained := [right]
        transport :=
          FrontierCompletion.absorbFirstIntoSecond
            (action.toTransport forward)
        irreducible := SearchIrreducible.singleton search right }
  | .forwardOnly forward _ _ =>
      { retained := [right]
        transport :=
          FrontierCompletion.absorbFirstIntoSecond
            (action.toTransport forward)
        irreducible := SearchIrreducible.singleton search right }
  | .backwardOnly backward _ _ =>
      { retained := [left]
        transport :=
          FrontierCompletion.absorbSecondIntoFirst
            (action.toTransport backward)
        irreducible := SearchIrreducible.singleton search left }
  | .unresolved forwardNotFound backwardNotFound =>
      { retained := [left, right]
        transport := ContinuationTransport.identity [left, right]
        irreducible :=
          SearchIrreducible.pair
            search left right forwardNotFound backwardNotFound }

/-- End-to-end executable pair reduction. -/
def reducePair
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (left right : State) :
    PairFrontierReduction (Completion := Completion) search left right :=
  reduceCertifiedPair
    search action left right (search.classifyPairCertified left right)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SearchIrreducible
#print axioms ConstitutiveSearch.CertifiedPairSearchResult
#print axioms ConstitutiveSearch.RelationSearch.classifyPairCertified
#print axioms ConstitutiveSearch.PairFrontierReduction
#print axioms ConstitutiveSearch.reduceCertifiedPair
#print axioms ConstitutiveSearch.reducePair
/- AXIOM_AUDIT_END -/