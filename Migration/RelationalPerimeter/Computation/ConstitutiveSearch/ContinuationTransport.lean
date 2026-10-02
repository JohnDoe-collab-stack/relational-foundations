import Init

set_option linter.defProp false
set_option warn.classDefReducibility false

/-!
# Constructive continuation transport

This module starts a generic search layer without assuming a complexity class,
a decision oracle, or a pre-existing global order on search states.

A state is interpreted only through its type of valid terminal completions.
A directional continuation transport is positive data: it maps every completion
of one state to a completion of another state.  It therefore justifies removing
the source side of a binary alternative without deciding whether either side is
inhabited.

The module also isolates an exact binary split.  A parent completion is
constructively decomposed into one of two continuation spaces, and the split is
reversible.  Combining such a split with a directional continuation transport
produces a constructive reduction from every parent completion to the retained
branch.
-/

namespace ConstitutiveSearch

universe uState uCompletion

/--
Positive directional data from the completion space of `source` to the
completion space of `target`.

No injectivity, inverse, decidability, or existence claim is included.  The
only primitive content is the transformation itself.
-/
structure ContinuationTransport
    {State : Type uState}
    (Completion : State → Type uCompletion)
    (source target : State) where
  map : Completion source → Completion target

namespace ContinuationTransport

/-- Every completion space transports to itself. -/
def identity
    {State : Type uState}
    {Completion : State → Type uCompletion}
    (state : State) :
    ContinuationTransport Completion state state :=
  { map := id }

/-- Directional continuation transports compose constructively. -/
def trans
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second third : State}
    (left : ContinuationTransport Completion first second)
    (right : ContinuationTransport Completion second third) :
    ContinuationTransport Completion first third :=
  { map := fun completion => right.map (left.map completion) }

/-- A directional transport preserves positive existence of a completion. -/
def preservesExistence
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {source target : State}
    (transport : ContinuationTransport Completion source target) :
    Nonempty (Completion source) → Nonempty (Completion target)
  | ⟨completion⟩ => ⟨transport.map completion⟩

/--
If the left branch transports into the right branch, every completion of the
binary alternative can be retained on the right.
-/
def absorbLeft
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {left right : State}
    (transport : ContinuationTransport Completion left right) :
    Completion left ⊕ Completion right → Completion right
  | .inl completion => transport.map completion
  | .inr completion => completion

/-- Symmetric absorption when the right branch transports into the left. -/
def absorbRight
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {left right : State}
    (transport : ContinuationTransport Completion right left) :
    Completion left ⊕ Completion right → Completion left
  | .inl completion => completion
  | .inr completion => transport.map completion

end ContinuationTransport

/--
Exact constructive decomposition of one completion space into two continuation
spaces.  This is a structural split, not a proposition saying that one branch
contains a solution.
-/
structure ExactBinarySplit
    {State : Type uState}
    (Completion : State → Type uCompletion)
    (parent left right : State) where
  split : Completion parent → Completion left ⊕ Completion right
  merge : Completion left ⊕ Completion right → Completion parent
  splitMerge :
    (branch : Completion left ⊕ Completion right) →
      split (merge branch) = branch
  mergeSplit :
    (completion : Completion parent) →
      merge (split completion) = completion

namespace ExactBinarySplit

/--
A left-to-right continuation transport eliminates the left side of an exact
binary split while retaining every parent completion constructively.
-/
def eliminateLeft
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion left right) :
    ContinuationTransport Completion parent right :=
  { map := fun completion =>
      transport.absorbLeft (splitter.split completion) }

/--
A right-to-left continuation transport eliminates the right side of an exact
binary split while retaining every parent completion constructively.
-/
def eliminateRight
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion right left) :
    ContinuationTransport Completion parent left :=
  { map := fun completion =>
      transport.absorbRight (splitter.split completion) }

/-- Positive existence at the parent is retained after left absorption. -/
def eliminateLeft_preservesExistence
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion left right) :
    Nonempty (Completion parent) → Nonempty (Completion right) :=
  (splitter.eliminateLeft transport).preservesExistence

/-- Positive existence at the parent is retained after right absorption. -/
def eliminateRight_preservesExistence
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    (splitter : ExactBinarySplit Completion parent left right)
    (transport : ContinuationTransport Completion right left) :
    Nonempty (Completion parent) → Nonempty (Completion left) :=
  (splitter.eliminateRight transport).preservesExistence

end ExactBinarySplit

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ContinuationTransport
#print axioms ConstitutiveSearch.ContinuationTransport.trans
#print axioms ConstitutiveSearch.ContinuationTransport.preservesExistence
#print axioms ConstitutiveSearch.ExactBinarySplit
#print axioms ConstitutiveSearch.ExactBinarySplit.eliminateLeft
#print axioms ConstitutiveSearch.ExactBinarySplit.eliminateRight
/- AXIOM_AUDIT_END -/
