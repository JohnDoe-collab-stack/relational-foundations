import RelationalPerimeter.Computation.ConstitutiveSearch.IrreducibleFrontier

set_option linter.defProp false
set_option warn.classDefReducibility false

/-!
# Constitutive width of a certified frontier reduction

This module lifts the pairwise reduction interface to arbitrary finite source
frontiers without assuming that a global normalizer has already been built.

A certified irreducible frontier reduction contains exactly three pieces of
positive data:

* the retained frontier,
* a continuation-preserving transport from the original frontier to it,
* a proof that the retained frontier is irreducible relative to the supplied
  executable relation search.

The constitutive width of that reduction is then derived as the length of the
retained frontier.  Width is therefore measured only after the structural
reduction has been constructed.  It is not used to define irreducibility or to
choose which states should survive.
-/

namespace ConstitutiveSearch

universe uState uRelation uCompletion

/--
A constructive reduction of any finite frontier to one that is irreducible
relative to a supplied relation search.
-/
structure IrreducibleFrontierReduction
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (source : List State) where
  retained : List State
  transport : FrontierTransport Completion source retained
  irreducible : SearchIrreducible search retained

namespace IrreducibleFrontierReduction

/-- Width is derived from the already constructed retained frontier. -/
def width
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {source : List State}
    (reduction :
      IrreducibleFrontierReduction (Completion := Completion) search source) : Nat :=
  reduction.retained.length

/--
Any frontier already known to be search-irreducible has the identity reduction.
No state is removed merely because a smaller width would be desirable.
-/
def identity
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (source : List State)
    (irreducible : SearchIrreducible search source) :
    IrreducibleFrontierReduction (Completion := Completion) search source :=
  { retained := source
    transport := ContinuationTransport.identity source
    irreducible := irreducible }

/-- The empty frontier has a canonical irreducible reduction of width zero. -/
def empty
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation) :
    IrreducibleFrontierReduction (Completion := Completion) search [] :=
  identity search [] (SearchIrreducible.nil search)

/-- Every singleton frontier has a canonical irreducible reduction of width one. -/
def singleton
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (state : State) :
    IrreducibleFrontierReduction (Completion := Completion) search [state] :=
  identity search [state] (SearchIrreducible.singleton search state)

/--
Every certified pair reduction is already an arbitrary-frontier irreducible
reduction.  No information is lost in this lift.
-/
def ofPair
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {left right : State}
    (pair : PairFrontierReduction (Completion := Completion) search left right) :
    IrreducibleFrontierReduction
      (Completion := Completion) search [left, right] :=
  { retained := pair.retained
    transport := pair.transport
    irreducible := pair.irreducible }

/-- Lifting a pair reduction preserves its derived width definitionally. -/
theorem ofPair_width
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {left right : State}
    (pair : PairFrontierReduction (Completion := Completion) search left right) :
    (ofPair pair).width = pair.width :=
  rfl

/-- Any actual completion of the source frontier survives in the retained one. -/
def mapCompletion
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {source : List State}
    (reduction :
      IrreducibleFrontierReduction (Completion := Completion) search source) :
    FrontierCompletion Completion source →
      FrontierCompletion Completion reduction.retained :=
  reduction.transport.map

/-- Positive existence of a source-frontier completion is preserved. -/
def preservesExistence
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {source : List State}
    (reduction :
      IrreducibleFrontierReduction (Completion := Completion) search source) :
    Nonempty (FrontierCompletion Completion source) →
      Nonempty (FrontierCompletion Completion reduction.retained) :=
  reduction.transport.preservesExistence

end IrreducibleFrontierReduction

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.width
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.identity
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.empty
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.singleton
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.ofPair
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.ofPair_width
#print axioms ConstitutiveSearch.IrreducibleFrontierReduction.preservesExistence
/- AXIOM_AUDIT_END -/
