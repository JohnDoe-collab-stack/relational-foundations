import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontierPreservation

/-!
# Operational status read from an available transport

An opened pair remains a two-position frontier until an
acceptance-preserving transport is supplied.  Supplying such a transport does
not merely change a numeric label: it constructs the existing semantic
frontier absorption, whose left case executes the supplied map and whose right
case is retained unchanged.
-/

namespace ConstitutiveSearch

universe uState uContinuation

/-- The retained frontier is calculated from transport availability. -/
def retainedFrontier
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State} :
    Option (AcceptingContinuationTransport system left right) →
      List system.State
  | none => [left, right]
  | some _transport => [right]

/--
The semantic preservation attached to the same status.  Absence keeps both
positions; presence executes the supplied first-into-second absorption.
-/
def outcomePreservation
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right)) :
    AcceptedFrontierPreservation
      system [left, right] (retainedFrontier transport?) :=
  match transport? with
  | none => AcceptedFrontierPreservation.identity system [left, right]
  | some transport =>
      AcceptedFrontierPreservation.absorbFirstIntoSecond transport

/-- Transport an arbitrary frontier continuation according to the status. -/
def carryFrontierContinuation
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right))
    (continuation : FrontierContinuation system [left, right]) :
    FrontierContinuation system (retainedFrontier transport?) :=
  (outcomePreservation transport?).forward.map continuation

/-- Positions are indexed by the retained frontier itself. -/
abbrev StageOperationalPosition
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right)) :=
  Fin (retainedFrontier transport?).length

/-- Width is derived, never supplied independently. -/
def stageOperationalWidth
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right)) : Nat :=
  (retainedFrontier transport?).length

/-- Read the state denoted by an operational position. -/
def operationalStateAt
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    {transport? : Option (AcceptingContinuationTransport system left right)}
    (position : StageOperationalPosition transport?) : system.State :=
  (retainedFrontier transport?).get position

@[simp] theorem retainedFrontier_none
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State} :
    retainedFrontier
      (system := system) (left := left) (right := right) none = [left, right] :=
  rfl

@[simp] theorem retainedFrontier_some
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport : AcceptingContinuationTransport system left right) :
    retainedFrontier (some transport) = [right] :=
  rfl

@[simp] theorem carry_none_eq_identity
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (continuation : FrontierContinuation system [left, right]) :
    carryFrontierContinuation
      (system := system) (left := left) (right := right) none continuation =
        continuation :=
  rfl

@[simp] theorem carry_some_left_eq_map
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport : AcceptingContinuationTransport system left right)
    (continuation : system.Continuation left) :
    carryFrontierContinuation (some transport) (.head continuation) =
      .head (transport.map continuation) :=
  rfl

@[simp] theorem carry_some_right_eq_self
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport : AcceptingContinuationTransport system left right)
    (continuation : system.Continuation right) :
    carryFrontierContinuation (some transport) (.tail (.head continuation)) =
      .head continuation :=
  rfl

/-- Acceptance is transported by the same semantic map. -/
theorem carryFrontierContinuation_preservesAccept
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right))
    (continuation : FrontierContinuation system [left, right])
    (accepted : FrontierAccept system [left, right] continuation) :
    FrontierAccept system (retainedFrontier transport?)
      (carryFrontierContinuation transport? continuation) :=
  (outcomePreservation transport?).forward.preservesAccept continuation accepted

/-- The status preserves frontier viability in both directions. -/
theorem outcomePreservation_viable_iff
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport? : Option (AcceptingContinuationTransport system left right)) :
    FrontierViable system [left, right] ↔
      FrontierViable system (retainedFrontier transport?) :=
  (outcomePreservation transport?).viable_iff

@[simp] theorem pending_width_eq_two
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State} :
    stageOperationalWidth
      (system := system) (left := left) (right := right) none = 2 :=
  rfl

@[simp] theorem reduced_width_eq_one
    {system : SearchSystem.{uState, uContinuation}}
    {left right : system.State}
    (transport : AcceptingContinuationTransport system left right) :
    stageOperationalWidth (some transport) = 1 :=
  rfl

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.retainedFrontier
#print axioms ConstitutiveSearch.outcomePreservation
#print axioms ConstitutiveSearch.carryFrontierContinuation
#print axioms ConstitutiveSearch.StageOperationalPosition
#print axioms ConstitutiveSearch.stageOperationalWidth
#print axioms ConstitutiveSearch.operationalStateAt
#print axioms ConstitutiveSearch.retainedFrontier_none
#print axioms ConstitutiveSearch.retainedFrontier_some
#print axioms ConstitutiveSearch.carry_none_eq_identity
#print axioms ConstitutiveSearch.carry_some_left_eq_map
#print axioms ConstitutiveSearch.carry_some_right_eq_self
#print axioms ConstitutiveSearch.carryFrontierContinuation_preservesAccept
#print axioms ConstitutiveSearch.outcomePreservation_viable_iff
#print axioms ConstitutiveSearch.pending_width_eq_two
#print axioms ConstitutiveSearch.reduced_width_eq_one
/- AXIOM_AUDIT_END -/
