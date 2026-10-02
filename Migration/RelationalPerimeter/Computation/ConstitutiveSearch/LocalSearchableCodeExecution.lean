import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCode

/-!
# Candidate-free local execution of searchable transport codes

SearchableTransportCode shows that a constituted code can be converted to a
primitive-hit path without running global closure.

This module fixes the local execution policy completely:
* no intermediate candidate list;
* fuel exactly one on every primitive atom.

For every searchable code, there exists a sequential primitive-hit execution
with exactly one primitive query per atom and zero composition-candidate
inspections.

The execution remains propositionally witnessed.  No nonconstructive choice is
used to extract a path as data from a proof of SearchableBy.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace TransportCode

/--
Candidate-free local execution property for one constituted code.

The witness path is existential, keeping the statement in Prop and avoiding any
choice principle when SearchableBy is itself only propositional evidence.
-/
def LocalSequentialExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) : Prop :=
  ∃ path :
      PrimitiveHitPath
        primitive
        source
        target,
    path.length = code.size ∧
      (path.sequentialStats
          []
          1).primitiveQueries =
        code.size ∧
      (path.sequentialStats
          []
          1).compositionCandidates =
        0

/--
Every searchable constituted code admits the minimal local execution policy.
No global candidate list and no global closure fuel are needed.
-/
theorem localSequentialExecution_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive) :
    LocalSequentialExecution
      primitive
      code := by
  exact
    code.hasSequentialExecution_of_searchable
      primitive
      []
      1
      (by decide)
      searchable

/--
Package, still proposition-valued, saying that the same constituted code both
witnesses genuine global composition need and admits candidate-free local
execution.
-/
def GlobalNeedWithLocalExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) : Prop :=
  PrimitiveHitPath.GlobalCompositionRequired
      primitive
      source
      target ∧
    LocalSequentialExecution
      primitive
      code

/--
A direct primitive miss together with a searchable constituted code of size at
least two simultaneously certifies:
* genuine global composition requirement;
* candidate-free local sequential execution of the same constituted code.
-/
theorem directMiss_searchableCode_hasLocalExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (directMiss :
      primitive.find source target =
        none)
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive)
    (codeSize :
      2 ≤ code.size) :
    GlobalNeedWithLocalExecution
      primitive
      code := by
  constructor
  · exact
      (PrimitiveHitPath.globalCompositionRequired_iff_searchableCode
        primitive
        source
        target).2
        ⟨directMiss,
          ⟨code,
            searchable,
            codeSize⟩⟩
  · exact
      localSequentialExecution_of_searchable
        primitive
        code
        searchable

end TransportCode

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.TransportCode.LocalSequentialExecution
#print axioms ConstitutiveSearch.TransportCode.localSequentialExecution_of_searchable
#print axioms ConstitutiveSearch.TransportCode.GlobalNeedWithLocalExecution
#print axioms ConstitutiveSearch.TransportCode.directMiss_searchableCode_hasLocalExecution
/- AXIOM_AUDIT_END -/
