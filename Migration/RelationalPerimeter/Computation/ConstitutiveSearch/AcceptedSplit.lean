import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptingTransport

/-!
# Exact structural splits with explicit acceptance

An exact split is first an isomorphism of structural continuation spaces.
Acceptance compatibility is stated separately in both directions.
-/

namespace ConstitutiveSearch

/-- Acceptance predicate on the disjoint union of two branch continuation spaces. -/
def BinaryAccept
    (system : SearchSystem)
    {left right : system.State} :
    system.Continuation left ⊕
      system.Continuation right →
      Prop
  | .inl continuation =>
      system.Accept left continuation
  | .inr continuation =>
      system.Accept right continuation

/--
Exact binary decomposition of a structural continuation space with explicit
preservation of acceptance by both split and merge.
-/
structure AcceptingExactBinarySplit
    (system : SearchSystem)
    (parent left right : system.State) where
  split :
    system.Continuation parent →
      system.Continuation left ⊕
        system.Continuation right
  merge :
    system.Continuation left ⊕
        system.Continuation right →
      system.Continuation parent
  splitMerge :
    (branch :
      system.Continuation left ⊕
        system.Continuation right) →
      split (merge branch) = branch
  mergeSplit :
    (continuation : system.Continuation parent) →
      merge (split continuation) = continuation
  splitPreservesAccept :
    (continuation : system.Continuation parent) →
      system.Accept parent continuation →
        BinaryAccept system (split continuation)
  mergePreservesAccept :
    (branch :
      system.Continuation left ⊕
        system.Continuation right) →
      BinaryAccept system branch →
        system.Accept parent (merge branch)

namespace AcceptingExactBinarySplit

/-- Forget acceptance compatibility and retain the exact structural split. -/
def toStructuralSplit
    {system : SearchSystem}
    {parent left right : system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    ExactBinarySplit
      system.Continuation
      parent
      left
      right :=
  { split := splitter.split
    merge := splitter.merge
    splitMerge := splitter.splitMerge
    mergeSplit := splitter.mergeSplit }

/--
A parent is viable exactly when one of the two branches is viable.
-/
theorem viable_iff
    {system : SearchSystem}
    {parent left right : system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    system.Viable parent ↔
      system.Viable left ∨ system.Viable right := by
  constructor
  · intro parentViable
    rcases parentViable with ⟨continuation, accepted⟩
    have branchAccepted :=
      splitter.splitPreservesAccept continuation accepted
    cases branchExact : splitter.split continuation with
    | inl leftContinuation =>
        have leftAccepted :
            system.Accept left leftContinuation := by
          simpa [BinaryAccept, branchExact] using branchAccepted
        exact Or.inl ⟨leftContinuation, leftAccepted⟩
    | inr rightContinuation =>
        have rightAccepted :
            system.Accept right rightContinuation := by
          simpa [BinaryAccept, branchExact] using branchAccepted
        exact Or.inr ⟨rightContinuation, rightAccepted⟩
  · intro branchViable
    cases branchViable with
    | inl leftViable =>
        rcases leftViable with ⟨continuation, accepted⟩
        exact
          ⟨splitter.merge (.inl continuation),
            splitter.mergePreservesAccept
              (.inl continuation)
              accepted⟩
    | inr rightViable =>
        rcases rightViable with ⟨continuation, accepted⟩
        exact
          ⟨splitter.merge (.inr continuation),
            splitter.mergePreservesAccept
              (.inr continuation)
              accepted⟩

end AcceptingExactBinarySplit
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.BinaryAccept
#print axioms ConstitutiveSearch.AcceptingExactBinarySplit
#print axioms ConstitutiveSearch.AcceptingExactBinarySplit.toStructuralSplit
#print axioms ConstitutiveSearch.AcceptingExactBinarySplit.viable_iff
/- AXIOM_AUDIT_END -/
