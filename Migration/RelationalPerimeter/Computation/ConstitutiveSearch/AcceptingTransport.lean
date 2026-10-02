import RelationalPerimeter.Computation.ConstitutiveSearch.SearchSystem
import RelationalPerimeter.Computation.ConstitutiveSearch.ContinuationTransport

/-!
# Acceptance-preserving continuation transports

A transport in this layer is total on the structural continuation space and
carries accepted source continuations to accepted target continuations.

This is stronger than providing only a function between already accepted
witnesses.
-/

namespace ConstitutiveSearch

universe uState uContinuation

/--
A total structural continuation map equipped with an explicit preservation
theorem for acceptance.
-/
structure AcceptingContinuationTransport
    (system : SearchSystem)
    (source target : system.State) where
  map :
    system.Continuation source →
      system.Continuation target
  preservesAccept :
    (continuation : system.Continuation source) →
      system.Accept source continuation →
        system.Accept target (map continuation)

namespace AcceptingContinuationTransport

/-- Identity is acceptance-preserving. -/
def identity
    (system : SearchSystem)
    (state : system.State) :
    AcceptingContinuationTransport system state state :=
  { map := fun continuation => continuation
    preservesAccept := fun _ accepted => accepted }

/-- Acceptance-preserving transports compose constructively. -/
def trans
    {system : SearchSystem}
    {first second third : system.State}
    (left : AcceptingContinuationTransport system first second)
    (right : AcceptingContinuationTransport system second third) :
    AcceptingContinuationTransport system first third :=
  { map := fun continuation =>
      right.map (left.map continuation)
    preservesAccept := by
      intro continuation accepted
      exact
        right.preservesAccept
          (left.map continuation)
          (left.preservesAccept continuation accepted) }

/-- Forget only the acceptance proof and retain the total structural map. -/
def toStructuralTransport
    {system : SearchSystem}
    {source target : system.State}
    (transport : AcceptingContinuationTransport system source target) :
    ContinuationTransport system.Continuation source target :=
  { map := transport.map }

/-- A transport preserves viability in its directional sense. -/
theorem preservesViable
    {system : SearchSystem}
    {source target : system.State}
    (transport : AcceptingContinuationTransport system source target) :
    system.Viable source →
      system.Viable target := by
  intro viable
  rcases viable with ⟨continuation, accepted⟩
  exact
    ⟨transport.map continuation,
      transport.preservesAccept continuation accepted⟩

/--
Every total acceptance-preserving transport induces a transport between the
derived spaces of accepted witnesses.

The converse is deliberately not asserted.
-/
def toAcceptedTransport
    {system : SearchSystem}
    {source target : system.State}
    (transport : AcceptingContinuationTransport system source target) :
    ContinuationTransport
      system.AcceptedContinuation
      source
      target :=
  { map := fun accepted =>
      ⟨transport.map accepted.1,
        transport.preservesAccept accepted.1 accepted.2⟩ }

end AcceptingContinuationTransport
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.AcceptingContinuationTransport
#print axioms ConstitutiveSearch.AcceptingContinuationTransport.identity
#print axioms ConstitutiveSearch.AcceptingContinuationTransport.trans
#print axioms ConstitutiveSearch.AcceptingContinuationTransport.toStructuralTransport
#print axioms ConstitutiveSearch.AcceptingContinuationTransport.preservesViable
#print axioms ConstitutiveSearch.AcceptingContinuationTransport.toAcceptedTransport
/- AXIOM_AUDIT_END -/
