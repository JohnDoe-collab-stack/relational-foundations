import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedSplit
import RelationalPerimeter.Computation.ConstitutiveSearch.FrontierReduction

/-!
# Frontiers with explicit acceptance

The existing FrontierCompletion type is reused only as a proof-relevant
structural disjunction of continuation spaces.  Acceptance is defined
separately and follows the state index carried by the frontier constructor.
-/

namespace ConstitutiveSearch

universe uState uContinuation

/-- Structural continuation carried by one state of a finite frontier. -/
abbrev FrontierContinuation
    (system : SearchSystem)
    (frontier : List system.State) : Type _ :=
  FrontierCompletion system.Continuation frontier

/-- Acceptance of the state-indexed continuation carried by a frontier. -/
def FrontierAccept
    (system : SearchSystem) :
    (frontier : List system.State) →
      FrontierContinuation system frontier →
        Prop
  | [], continuation => nomatch continuation
  | state :: _rest, .head continuation =>
      system.Accept state continuation
  | _state :: rest, .tail continuation =>
      FrontierAccept system rest continuation

/-- Lift a search system pointwise to finite search frontiers. -/
abbrev SearchSystem.frontierSystem
    (system : SearchSystem) : SearchSystem :=
  { State := List system.State
    Continuation := FrontierContinuation system
    Accept := FrontierAccept system }

/-- A frontier is viable when one of its structural continuations is accepted. -/
def FrontierViable
    (system : SearchSystem)
    (frontier : List system.State) : Prop :=
  system.frontierSystem.Viable frontier

/-- Acceptance-preserving transport between two finite frontiers. -/
abbrev AcceptingFrontierTransport
    (system : SearchSystem)
    (source target : List system.State) :=
  AcceptingContinuationTransport
    system.frontierSystem
    source
    target

namespace AcceptingFrontierTransport

/-- Every frontier transports to itself. -/
def identity
    (system : SearchSystem)
    (frontier : List system.State) :
    AcceptingFrontierTransport system frontier frontier :=
  AcceptingContinuationTransport.identity
    system.frontierSystem
    frontier

/-- Frontier transports compose without changing the acceptance semantics. -/
def trans
    {system : SearchSystem}
    {first second third : List system.State}
    (left : AcceptingFrontierTransport system first second)
    (right : AcceptingFrontierTransport system second third) :
    AcceptingFrontierTransport system first third :=
  AcceptingContinuationTransport.trans left right

/--
Expand the head state through an exact structural split while preserving
acceptance explicitly.
-/
def expandHead
    {system : SearchSystem}
    {parent left right : system.State}
    {rest : List system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    AcceptingFrontierTransport
      system
      (parent :: rest)
      (left :: right :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head continuation =>
          match splitter.split continuation with
          | .inl leftContinuation =>
              .head leftContinuation
          | .inr rightContinuation =>
              .tail (.head rightContinuation)
      | .tail restContinuation =>
          .tail (.tail restContinuation)
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head continuation =>
          have branchAccepted :=
            splitter.splitPreservesAccept continuation accepted
          cases splitExact : splitter.split continuation with
          | inl leftContinuation =>
              simpa only [
                SearchSystem.frontierSystem,
                FrontierAccept,
                BinaryAccept,
                splitExact
              ] using branchAccepted
          | inr rightContinuation =>
              simpa only [
                SearchSystem.frontierSystem,
                FrontierAccept,
                BinaryAccept,
                splitExact
              ] using branchAccepted
      | tail restContinuation =>
          exact accepted }

/--
Contract an expanded head back to its parent using the exact split merger.
This is the acceptance-preserving reverse direction needed for viability.
-/
def contractExpandedHead
    {system : SearchSystem}
    {parent left right : system.State}
    {rest : List system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    AcceptingFrontierTransport
      system
      (left :: right :: rest)
      (parent :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head leftContinuation =>
          .head (splitter.merge (.inl leftContinuation))
      | .tail (.head rightContinuation) =>
          .head (splitter.merge (.inr rightContinuation))
      | .tail (.tail restContinuation) =>
          .tail restContinuation
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head leftContinuation =>
          change
            system.Accept parent
              (splitter.merge (.inl leftContinuation))
          exact
            splitter.mergePreservesAccept
              (.inl leftContinuation)
              accepted
      | tail tailContinuation =>
          cases tailContinuation with
          | head rightContinuation =>
              change
                system.Accept parent
                  (splitter.merge (.inr rightContinuation))
              exact
                splitter.mergePreservesAccept
                  (.inr rightContinuation)
                  accepted
          | tail restContinuation =>
              exact accepted }

/--
Absorb the first frontier state into the second using a total
acceptance-preserving state transport.
-/
def absorbFirstIntoSecond
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State}
    (transport : AcceptingContinuationTransport system first second) :
    AcceptingFrontierTransport
      system
      (first :: second :: rest)
      (second :: rest) :=
  { map :=
      (FrontierCompletion.absorbFirstIntoSecond
        transport.toStructuralTransport).map
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head continuation =>
          exact
            transport.preservesAccept
              continuation
              accepted
      | tail tailContinuation =>
          exact accepted }

/-- Symmetric absorption of the second state into the first. -/
def absorbSecondIntoFirst
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State}
    (transport : AcceptingContinuationTransport system second first) :
    AcceptingFrontierTransport
      system
      (first :: second :: rest)
      (first :: rest) :=
  { map :=
      (FrontierCompletion.absorbSecondIntoFirst
        transport.toStructuralTransport).map
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head continuation =>
          exact accepted
      | tail tailContinuation =>
          cases tailContinuation with
          | head continuation =>
              exact
                transport.preservesAccept
                  continuation
                  accepted
          | tail restContinuation =>
              exact accepted }

/--
Structural inclusion of the retained frontier after absorbing the first state
back into the original frontier.
-/
def includeAfterAbsorbFirst
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State} :
    AcceptingFrontierTransport
      system
      (second :: rest)
      (first :: second :: rest) :=
  { map := fun frontier => .tail frontier
    preservesAccept := by
      intro _frontier accepted
      exact accepted }

/--
Structural inclusion of the retained frontier after absorbing the second state
back into the original frontier.
-/
def includeAfterAbsorbSecond
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State} :
    AcceptingFrontierTransport
      system
      (first :: rest)
      (first :: second :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head continuation =>
          .head continuation
      | .tail restContinuation =>
          .tail (.tail restContinuation)
    preservesAccept := by
      intro frontier accepted
      cases frontier with
      | head continuation =>
          exact accepted
      | tail restContinuation =>
          exact accepted }

end AcceptingFrontierTransport
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.FrontierAccept
#print axioms ConstitutiveSearch.SearchSystem.frontierSystem
#print axioms ConstitutiveSearch.FrontierViable
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.expandHead
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.contractExpandedHead
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.absorbFirstIntoSecond
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.absorbSecondIntoFirst
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.includeAfterAbsorbFirst
#print axioms ConstitutiveSearch.AcceptingFrontierTransport.includeAfterAbsorbSecond
/- AXIOM_AUDIT_END -/
