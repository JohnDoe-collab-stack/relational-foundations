import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCodeValidationCore
import RelationalPerimeter.Computation.ConstitutiveSearch.LocalSearchableCodeExecution

/-!
# Constituted primitive paths

A composed transport can be produced directly from a sequence of already
constituted primitive witnesses, rather than discovered by global closure
search.

This module introduces a nonempty linear path of primitive generator witnesses.
It is purely proof-relevant construction data.

The path compiles deterministically to TransportCode.  When the path is
searchable by an announced primitive RelationSearch:
* compiled code atom count equals path length;
* executable SearchableBy validation performs exactly path.length queries;
* validation succeeds;
* candidate-free local execution performs exactly path.length primitive queries
  and zero composition-candidate inspections.

This separates three layers:
1. constitution of primitive witnesses;
2. executable validation against RelationSearch;
3. local execution of the validated code.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Nonempty linear sequence of already constituted primitive witnesses. -/
inductive ConstitutedPrimitivePath
    {State : Type}
    (Generator : State → State → Type uGenerator) :
    State → State → Type uGenerator where
  | atom
      {source target : State}
      (witness : Generator source target) :
      ConstitutedPrimitivePath
        Generator
        source
        target
  | step
      {source middle target : State}
      (witness : Generator source middle)
      (tail :
        ConstitutedPrimitivePath
          Generator
          middle
          target) :
      ConstitutedPrimitivePath
        Generator
        source
        target

namespace ConstitutedPrimitivePath

/-- Number of constituted primitive witnesses in the path. -/
def length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {source target : State} :
    ConstitutedPrimitivePath
      Generator
      source
      target →
    Nat
  | .atom _ =>
      1
  | .step _ tail =>
      tail.length + 1

/-- Compile the constituted witness path to a right-associated TransportCode. -/
def toTransportCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {source target : State} :
    ConstitutedPrimitivePath
      Generator
      source
      target →
    TransportClosure
      Generator
      source
      target
  | .atom witness =>
      TransportClosure.ofGenerator
        witness
  | .step witness tail =>
      TransportClosure.compose
        (TransportClosure.ofGenerator
          witness)
        tail.toTransportCode

/-- Compiled code atom count is exactly path length. -/
theorem toTransportCode_size
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target) :
    path.toTransportCode.size =
      path.length := by
  induction path with
  | atom witness =>
      rfl
  | step witness tail inductionHypothesis =>
      change
        1 + tail.toTransportCode.size =
          tail.length + 1
      rw [inductionHypothesis]
      exact
        Nat.add_comm
          1
          tail.length

/--
Code-local searchability of a constituted witness path.

Every path edge must be rediscoverable by primitive.find.
-/
def SearchableBy
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    {source target : State} →
      ConstitutedPrimitivePath
        Generator
        source
        target →
      Prop
  | source, target, .atom _ =>
      primitive.find source target ≠
        none
  | source, _, .step (middle := middle) _ tail =>
      primitive.find source middle ≠
          none ∧
        tail.SearchableBy primitive

/-- Path searchability is exactly SearchableBy of its compiled code. -/
theorem toTransportCode_searchable_iff
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target) :
    path.toTransportCode.SearchableBy
        primitive ↔
      path.SearchableBy primitive := by
  induction path with
  | atom witness =>
      rfl
  | @step source middle target witness tail inductionHypothesis =>
      change
        (primitive.find source middle ≠ none ∧
            tail.toTransportCode.SearchableBy primitive) ↔
          (primitive.find source middle ≠ none ∧
            tail.SearchableBy primitive)
      constructor
      · intro searchable
        exact
          ⟨searchable.1,
            inductionHypothesis.mp searchable.2⟩
      · intro searchable
        exact
          ⟨searchable.1,
            inductionHypothesis.mpr searchable.2⟩

/-- Validation query count of the compiled code is exactly path length. -/
theorem validation_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target) :
    (validateSearchableCode
        primitive
        path.toTransportCode).primitiveQueries =
      path.length := by
  calc
    (validateSearchableCode
        primitive
        path.toTransportCode).primitiveQueries
        =
      path.toTransportCode.size :=
        validateSearchableCode_primitiveQueries
          primitive
          path.toTransportCode
    _ =
      path.length :=
        path.toTransportCode_size

/-- Validation succeeds exactly when every constituted edge is searchable. -/
theorem validation_success_iff
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target) :
    (validateSearchableCode
        primitive
        path.toTransportCode).success =
        true ↔
      path.SearchableBy primitive := by
  calc
    (validateSearchableCode
        primitive
        path.toTransportCode).success =
          true
        ↔
      path.toTransportCode.SearchableBy
        primitive :=
          validateSearchableCode_success_iff
            primitive
            path.toTransportCode
    _ ↔
      path.SearchableBy primitive :=
        path.toTransportCode_searchable_iff
          primitive

/--
A searchable constituted path admits candidate-free local execution of its
compiled code.
-/
theorem localSequentialExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target)
    (searchable :
      path.SearchableBy primitive) :
    TransportCode.LocalSequentialExecution
      primitive
      path.toTransportCode := by
  apply
    TransportCode.localSequentialExecution_of_searchable
      primitive
      path.toTransportCode
  exact
    (path.toTransportCode_searchable_iff
      primitive).2
      searchable

/--
End-to-end certificate for a constituted primitive path:
validation succeeds, validation cost is linear in path length, and the compiled
code has candidate-free local execution.
-/
structure EndToEndLocalExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target) : Prop where
  validationSuccess :
    (validateSearchableCode
        primitive
        path.toTransportCode).success =
      true
  validationPrimitiveQueries :
    (validateSearchableCode
        primitive
        path.toTransportCode).primitiveQueries =
      path.length
  localExecution :
    TransportCode.LocalSequentialExecution
      primitive
      path.toTransportCode

/-- Searchable constituted paths satisfy the complete validation/execution chain. -/
theorem endToEndLocalExecution_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (path :
      ConstitutedPrimitivePath
        Generator
        source
        target)
    (searchable :
      path.SearchableBy primitive) :
    EndToEndLocalExecution
      primitive
      path := by
  exact
    { validationSuccess :=
        (path.validation_success_iff
          primitive).2
          searchable
      validationPrimitiveQueries :=
        path.validation_primitiveQueries
          primitive
      localExecution :=
        path.localSequentialExecution
          primitive
          searchable }

end ConstitutedPrimitivePath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.length
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.toTransportCode
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.toTransportCode_size
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.SearchableBy
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.toTransportCode_searchable_iff
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.validation_primitiveQueries
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.validation_success_iff
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.localSequentialExecution
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.EndToEndLocalExecution
#print axioms ConstitutiveSearch.ConstitutedPrimitivePath.endToEndLocalExecution_of_searchable
/- AXIOM_AUDIT_END -/
