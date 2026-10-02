import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierPreservation
import RelationalPerimeter.Computation.ConstitutiveSearch.IrreducibleFrontier

/-!
# Relational reconstruction with explicit acceptance

This module lifts executable structural relation search to the hardened search
semantics.  A relation witness is useful only when it reconstructs a total
continuation map together with a separate theorem preserving acceptance.

Search failure remains operational: `none` means only that the executable
search produced no witness.
-/

namespace ConstitutiveSearch

universe uRelation

/--
Positive semantic content attached to a structural relation witness.

The witness reconstructs a total acceptance-preserving continuation transport;
it does not decide whether the source state is viable.
-/
structure AcceptedRelationalAction
    (system : SearchSystem)
    (Relation : system.State → system.State → Type uRelation) where
  toTransport :
    {source target : system.State} →
      Relation source target →
        AcceptingContinuationTransport system source target

namespace AcceptedRelationalAction

/-- A relation witness transports viability in its positive direction. -/
theorem preservesViable
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (action : AcceptedRelationalAction system Relation)
    {source target : system.State}
    (witness : Relation source target) :
    system.Viable source → system.Viable target :=
  (action.toTransport witness).preservesViable

/-- A relation witness safely absorbs the first branch into the second. -/
def absorbFirstIntoSecond
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (action : AcceptedRelationalAction system Relation)
    {first second : system.State}
    {rest : List system.State}
    (witness : Relation first second) :
    AcceptedFrontierPreservation
      system
      (first :: second :: rest)
      (second :: rest) :=
  AcceptedFrontierPreservation.absorbFirstIntoSecond
    (action.toTransport witness)

/-- Symmetric safe absorption of the second branch into the first. -/
def absorbSecondIntoFirst
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (action : AcceptedRelationalAction system Relation)
    {first second : system.State}
    {rest : List system.State}
    (witness : Relation second first) :
    AcceptedFrontierPreservation
      system
      (first :: second :: rest)
      (first :: rest) :=
  AcceptedFrontierPreservation.absorbSecondIntoFirst
    (action.toTransport witness)

end AcceptedRelationalAction

namespace RelationSearch

/--
Successful executable search reconstructs a total acceptance-preserving
transport.  Failure remains only failure of this search procedure.
-/
def findAcceptedTransport
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (source target : system.State) :
    Option (AcceptingContinuationTransport system source target) :=
  match search.find source target with
  | none => none
  | some witness => some (action.toTransport witness)

end RelationSearch

namespace PairSearchResult

/-- Recover a hardened left-to-right transport when pair search found one. -/
def acceptedForwardTransport?
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (action : AcceptedRelationalAction system Relation) :
    PairSearchResult Relation left right →
      Option (AcceptingContinuationTransport system left right)
  | .bidirectional forward _ => some (action.toTransport forward)
  | .forwardOnly forward => some (action.toTransport forward)
  | .backwardOnly _ => none
  | .unresolved => none

/-- Recover a hardened right-to-left transport when pair search found one. -/
def acceptedBackwardTransport?
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    {left right : system.State}
    (action : AcceptedRelationalAction system Relation) :
    PairSearchResult Relation left right →
      Option (AcceptingContinuationTransport system right left)
  | .bidirectional _ backward => some (action.toTransport backward)
  | .forwardOnly _ => none
  | .backwardOnly backward => some (action.toTransport backward)
  | .unresolved => none

end PairSearchResult

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.AcceptedRelationalAction
#print axioms ConstitutiveSearch.AcceptedRelationalAction.preservesViable
#print axioms ConstitutiveSearch.AcceptedRelationalAction.absorbFirstIntoSecond
#print axioms ConstitutiveSearch.AcceptedRelationalAction.absorbSecondIntoFirst
#print axioms ConstitutiveSearch.RelationSearch.findAcceptedTransport
#print axioms ConstitutiveSearch.PairSearchResult.acceptedForwardTransport?
#print axioms ConstitutiveSearch.PairSearchResult.acceptedBackwardTransport?
/- AXIOM_AUDIT_END -/
