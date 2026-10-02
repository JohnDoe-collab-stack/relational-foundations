import RelationalPerimeter.Computation.ConstitutiveSearch.ContinuationTransport

set_option linter.defProp false
set_option warn.classDefReducibility false

/-!
# Constructive frontier reduction

A search frontier is represented by a finite list of states together with a
proof-relevant completion carried by one state in that list.  The frontier does
not assert which state is completable.  It records only a disjunction of
completion spaces.

An exact binary split expands the head state into two successor states.  A
directional continuation transport can then absorb one successor into the
other.  The composite step preserves every completion constructively and never
asks whether either successor is inhabited.
-/

namespace ConstitutiveSearch

universe uState uCompletion

/--
Proof-relevant disjunction of the completion spaces represented by a finite
frontier.
-/
inductive FrontierCompletion
    {State : Type uState}
    (Completion : State → Type uCompletion) : List State → Type _
  | head
      {state : State}
      {rest : List State} :
      Completion state → FrontierCompletion Completion (state :: rest)
  | tail
      {state : State}
      {rest : List State} :
      FrontierCompletion Completion rest →
        FrontierCompletion Completion (state :: rest)

/-- A solution-preserving transformation between two finite frontiers. -/
abbrev FrontierTransport
    {State : Type uState}
    (Completion : State → Type uCompletion)
    (source target : List State) :=
  ContinuationTransport (FrontierCompletion Completion) source target

namespace FrontierCompletion

/-- A completion of a singleton frontier. -/
def singleton
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {state : State} :
    Completion state → FrontierCompletion Completion [state] :=
  fun completion => .head completion

/--
Expand the head of a frontier through an exact binary split.  Existing tail
completions are preserved unchanged.
-/
def expandHead
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    {rest : List State}
    (splitter : ExactBinarySplit Completion parent left right) :
    FrontierTransport Completion
      (parent :: rest) (left :: right :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head completion =>
          match splitter.split completion with
          | .inl leftCompletion => .head leftCompletion
          | .inr rightCompletion => .tail (.head rightCompletion)
      | .tail tailCompletion => .tail (.tail tailCompletion) }

/--
Absorb the first frontier state into the second when every completion of the
first transports to a completion of the second.
-/
def absorbFirstIntoSecond
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State}
    (transport : ContinuationTransport Completion first second) :
    FrontierTransport Completion
      (first :: second :: rest) (second :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head completion => .head (transport.map completion)
      | .tail tailCompletion => tailCompletion }

/--
Absorb the second frontier state into the first when every completion of the
second transports to a completion of the first.
-/
def absorbSecondIntoFirst
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State}
    (transport : ContinuationTransport Completion second first) :
    FrontierTransport Completion
      (first :: second :: rest) (first :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head completion => .head completion
      | .tail (.head completion) => .head (transport.map completion)
      | .tail (.tail tailCompletion) => .tail tailCompletion }

/--
One constitutive search step: exact OR expansion of the head followed by safe
left-to-right absorption.
-/
def expandThenAbsorbLeft
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    {rest : List State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion left right) :
    FrontierTransport Completion (parent :: rest) (right :: rest) :=
  (expandHead splitter).trans (absorbFirstIntoSecond transport)

/--
Symmetric constitutive search step: exact OR expansion followed by safe
right-to-left absorption.
-/
def expandThenAbsorbRight
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    {rest : List State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion right left) :
    FrontierTransport Completion (parent :: rest) (left :: rest) :=
  (expandHead splitter).trans (absorbSecondIntoFirst transport)

/-- Every constructive frontier step preserves positive completion existence. -/
def transportPreservesExistence
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {source target : List State}
    (transport : FrontierTransport Completion source target) :
    Nonempty (FrontierCompletion Completion source) →
      Nonempty (FrontierCompletion Completion target) :=
  transport.preservesExistence

end FrontierCompletion

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.FrontierCompletion
#print axioms ConstitutiveSearch.FrontierCompletion.expandHead
#print axioms ConstitutiveSearch.FrontierCompletion.absorbFirstIntoSecond
#print axioms ConstitutiveSearch.FrontierCompletion.absorbSecondIntoFirst
#print axioms ConstitutiveSearch.FrontierCompletion.expandThenAbsorbLeft
#print axioms ConstitutiveSearch.FrontierCompletion.expandThenAbsorbRight
/- AXIOM_AUDIT_END -/
