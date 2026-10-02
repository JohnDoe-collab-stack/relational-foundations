import RelationalPerimeter.Computation.ConstitutiveSearch.FrontierReduction

/-!
# Relational reconstruction of continuation transports

This module separates three layers that must not be collapsed:

1. a structural relation between search states;
2. a constructive action showing how a witness of that relation transforms
   terminal completions;
3. an executable search that may or may not produce a relation witness.

A successful relation search therefore reconstructs a continuation transport.
A failed search carries no non-existence claim.  Negative completeness, when
needed later, must be proved separately.
-/

namespace ConstitutiveSearch

universe uState uRelation uCompletion

/--
A structural relation acts on completion spaces.  The action is the positive
content that makes a relation witness useful for safe search reduction.
-/
structure RelationalContinuationAction
    {State : Type uState}
    (Relation : State → State → Type uRelation)
    (Completion : State → Type uCompletion) where
  act :
    {source target : State} →
      Relation source target → Completion source → Completion target

namespace RelationalContinuationAction

/-- Every relation witness induces a directional continuation transport. -/
def toTransport
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (action : RelationalContinuationAction Relation Completion)
    {source target : State}
    (witness : Relation source target) :
    ContinuationTransport Completion source target :=
  { map := action.act witness }

/-- A relation witness can absorb the first frontier branch into the second. -/
def absorbFirstIntoSecond
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (action : RelationalContinuationAction Relation Completion)
    {first second : State}
    {rest : List State}
    (witness : Relation first second) :
    FrontierTransport Completion
      (first :: second :: rest) (second :: rest) :=
  FrontierCompletion.absorbFirstIntoSecond
    (action.toTransport witness)

/-- Symmetric frontier absorption from the second state into the first. -/
def absorbSecondIntoFirst
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (action : RelationalContinuationAction Relation Completion)
    {first second : State}
    {rest : List State}
    (witness : Relation second first) :
    FrontierTransport Completion
      (first :: second :: rest) (first :: rest) :=
  FrontierCompletion.absorbSecondIntoFirst
    (action.toTransport witness)

end RelationalContinuationAction

/--
Executable attempt to construct a structural relation witness for an ordered
pair of states.

Returning `none` means only that this search procedure produced no witness.
-/
structure RelationSearch
    {State : Type uState}
    (Relation : State → State → Type uRelation) where
  find : (source target : State) → Option (Relation source target)

namespace RelationSearch

/-- Successful structural search reconstructs a continuation transport. -/
def findTransport
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (source target : State) :
    Option (ContinuationTransport Completion source target) :=
  match search.find source target with
  | none => none
  | some witness => some (action.toTransport witness)

end RelationSearch

/-- Four witness-carrying outcomes of searching both relation directions. -/
inductive PairSearchResult
    {State : Type uState}
    (Relation : State → State → Type uRelation)
    (left right : State) where
  | bidirectional :
      Relation left right → Relation right left → PairSearchResult Relation left right
  | forwardOnly :
      Relation left right → PairSearchResult Relation left right
  | backwardOnly :
      Relation right left → PairSearchResult Relation left right
  | unresolved : PairSearchResult Relation left right

namespace PairSearchResult

inductive Kind where
  | bidirectional
  | forwardOnly
  | backwardOnly
  | unresolved

/-- Forget witnesses and retain only the executable search outcome tag. -/
def kind
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {left right : State} :
    PairSearchResult Relation left right → Kind
  | .bidirectional _ _ => .bidirectional
  | .forwardOnly _ => .forwardOnly
  | .backwardOnly _ => .backwardOnly
  | .unresolved => .unresolved

/-- Recover a left-to-right continuation transport when the search found one. -/
def forwardTransport?
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {left right : State}
    (action : RelationalContinuationAction Relation Completion) :
    PairSearchResult Relation left right →
      Option (ContinuationTransport Completion left right)
  | .bidirectional forward _ => some (action.toTransport forward)
  | .forwardOnly forward => some (action.toTransport forward)
  | .backwardOnly _ => none
  | .unresolved => none

/-- Recover a right-to-left continuation transport when the search found one. -/
def backwardTransport?
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {left right : State}
    (action : RelationalContinuationAction Relation Completion) :
    PairSearchResult Relation left right →
      Option (ContinuationTransport Completion right left)
  | .bidirectional _ backward => some (action.toTransport backward)
  | .forwardOnly _ => none
  | .backwardOnly backward => some (action.toTransport backward)
  | .unresolved => none

end PairSearchResult

/-- Search both structural directions without turning search failure into refutation. -/
def RelationSearch.classifyPair
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (left right : State) : PairSearchResult Relation left right :=
  match search.find left right with
  | some forward =>
      match search.find right left with
      | some backward => .bidirectional forward backward
      | none => .forwardOnly forward
  | none =>
      match search.find right left with
      | some backward => .backwardOnly backward
      | none => .unresolved

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationalContinuationAction
#print axioms ConstitutiveSearch.RelationalContinuationAction.toTransport
#print axioms ConstitutiveSearch.RelationSearch
#print axioms ConstitutiveSearch.RelationSearch.findTransport
#print axioms ConstitutiveSearch.PairSearchResult
#print axioms ConstitutiveSearch.RelationSearch.classifyPair
/- AXIOM_AUDIT_END -/