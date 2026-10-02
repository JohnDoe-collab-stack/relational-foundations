set_option linter.checkUnivs false

/-!
# Search semantics with explicit acceptance

This module separates the space of structurally legal continuations from the
predicate that accepts some of those continuations.

The separation is intentionally minimal.  It does not assume decidability of
acceptance, existence of an accepted continuation, or any relation between
states.
-/

namespace ConstitutiveSearch

universe uState uContinuation

/--
A search system distinguishes structural continuations from their semantic
acceptance predicate.
-/
structure SearchSystem where
  State : Type uState
  Continuation : State → Type uContinuation
  Accept : (state : State) → Continuation state → Prop

namespace SearchSystem

/-- A state is viable when at least one structural continuation is accepted. -/
def Viable
    (system : SearchSystem)
    (state : system.State) : Prop :=
  ∃ continuation : system.Continuation state,
    system.Accept state continuation

/--
The proof-relevant type of accepted continuations.  This is a derived view of
the separated semantics, not the primitive continuation space.
-/
def AcceptedContinuation
    (system : SearchSystem)
    (state : system.State) : Type uContinuation :=
  { continuation : system.Continuation state //
      system.Accept state continuation }

/-- Viability is exactly inhabitation of the derived accepted-continuation type. -/
theorem viable_iff_nonempty_accepted
    (system : SearchSystem)
    (state : system.State) :
    system.Viable state ↔
      Nonempty (system.AcceptedContinuation state) := by
  constructor
  · intro viable
    rcases viable with ⟨continuation, accepted⟩
    exact ⟨⟨continuation, accepted⟩⟩
  · intro inhabited
    cases inhabited with
    | intro accepted =>
        exact ⟨accepted.1, accepted.2⟩

end SearchSystem
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SearchSystem
#print axioms ConstitutiveSearch.SearchSystem.Viable
#print axioms ConstitutiveSearch.SearchSystem.AcceptedContinuation
#print axioms ConstitutiveSearch.SearchSystem.viable_iff_nonempty_accepted
/- AXIOM_AUDIT_END -/
