import RelationalPerimeter.Computation.ConstitutiveSearch.AcceptedFrontier

/-!
# Viability-preserving frontier reductions

A frontier reduction is semantically adequate when it transports accepted
continuations forward and keeps every retained continuation interpretable in
the source frontier.  The two directions are independent and need not be
inverse.
-/

namespace ConstitutiveSearch

/--
Two acceptance-preserving frontier transports witnessing equivalence of
frontier viability.
-/
structure AcceptedFrontierPreservation
    (system : SearchSystem)
    (source target : List system.State) where
  forward :
    AcceptingFrontierTransport system source target
  backward :
    AcceptingFrontierTransport system target source

namespace AcceptedFrontierPreservation

/-- Every frontier preserves its own viability. -/
def identity
    (system : SearchSystem)
    (frontier : List system.State) :
    AcceptedFrontierPreservation system frontier frontier :=
  { forward :=
      AcceptingFrontierTransport.identity system frontier
    backward :=
      AcceptingFrontierTransport.identity system frontier }

/-- Viability-preserving frontier reductions compose. -/
def trans
    {system : SearchSystem}
    {first second third : List system.State}
    (left : AcceptedFrontierPreservation system first second)
    (right : AcceptedFrontierPreservation system second third) :
    AcceptedFrontierPreservation system first third :=
  { forward := left.forward.trans right.forward
    backward := right.backward.trans left.backward }

/-- Frontier viability is equivalent across a preservation witness. -/
theorem viable_iff
    {system : SearchSystem}
    {source target : List system.State}
    (preservation : AcceptedFrontierPreservation system source target) :
    FrontierViable system source ↔
      FrontierViable system target := by
  constructor
  · exact preservation.forward.preservesViable
  · exact preservation.backward.preservesViable

/-- Exact head expansion preserves frontier viability in both directions. -/
def expandHead
    {system : SearchSystem}
    {parent left right : system.State}
    {rest : List system.State}
    (splitter : AcceptingExactBinarySplit system parent left right) :
    AcceptedFrontierPreservation
      system
      (parent :: rest)
      (left :: right :: rest) :=
  { forward :=
      AcceptingFrontierTransport.expandHead splitter
    backward :=
      AcceptingFrontierTransport.contractExpandedHead splitter }

/-- Safe first-into-second absorption preserves frontier viability. -/
def absorbFirstIntoSecond
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State}
    (transport : AcceptingContinuationTransport system first second) :
    AcceptedFrontierPreservation
      system
      (first :: second :: rest)
      (second :: rest) :=
  { forward :=
      AcceptingFrontierTransport.absorbFirstIntoSecond transport
    backward :=
      AcceptingFrontierTransport.includeAfterAbsorbFirst }

/-- Safe second-into-first absorption preserves frontier viability. -/
def absorbSecondIntoFirst
    {system : SearchSystem}
    {first second : system.State}
    {rest : List system.State}
    (transport : AcceptingContinuationTransport system second first) :
    AcceptedFrontierPreservation
      system
      (first :: second :: rest)
      (first :: rest) :=
  { forward :=
      AcceptingFrontierTransport.absorbSecondIntoFirst transport
    backward :=
      AcceptingFrontierTransport.includeAfterAbsorbSecond }

end AcceptedFrontierPreservation
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.identity
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.trans
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.viable_iff
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.expandHead
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.absorbFirstIntoSecond
#print axioms ConstitutiveSearch.AcceptedFrontierPreservation.absorbSecondIntoFirst
/- AXIOM_AUDIT_END -/
