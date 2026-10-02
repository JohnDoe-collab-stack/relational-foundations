import RelationalFoundations.FiberTransport
set_option genInjectivity false

namespace RelationalFoundations
universe s r p a w

set_option linter.checkUnivs false in
/-- The two distinguished ports tie realization to the same interpreted signature. -/
structure EquippedQuantity (sig : ConstitutiveSignature.{s,r,p}) (symbol : sig.Symbol)
    (rolePort occurrencePort : sig.Port symbol) where
  interpretation : SignatureInterpretation.{s,r,p,a,w} sig
  Realizes : interpretation.Carrier (sig.portSort symbol rolePort) →
    interpretation.Carrier (sig.portSort symbol occurrencePort) → Type w
  exact : ExactRealization _ _ Realizes
  graph : (Σ role, Σ occurrence, Realizes role occurrence) → interpretation.Witness symbol
  graphRole : ∀ witness, interpretation.incidence symbol (graph witness) rolePort = witness.1
  graphOccurrence : ∀ witness, interpretation.incidence symbol (graph witness) occurrencePort = witness.2.1

@[reducible] def EquippedQuantity.quantity {sig : ConstitutiveSignature.{s,r,p}} {symbol : sig.Symbol}
    {rolePort occurrencePort : sig.Port symbol}
    (q : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort) : StructuralQuantity.{a,a,w} :=
  ⟨_, _, q.Realizes, q.exact⟩

structure EquippedEquiv {sig : ConstitutiveSignature.{s,r,p}} {symbol : sig.Symbol}
    {rolePort occurrencePort : sig.Port symbol}
    (first second : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort) where
  core : ConstitutiveEquiv first.quantity second.quantity
  signature : SignatureTransport first.interpretation second.interpretation
  roleMapExact : ∀ role, core.roles.forward role = (signature.sorts _).forward role
  occurrenceMapExact : ∀ occurrence, core.occurrences.forward occurrence = (signature.sorts _).forward occurrence
  graphExact : ∀ witness, (signature.witnesses symbol).forward (first.graph witness) =
    second.graph (core.witnesses.forward witness)

namespace EquippedEquiv
variable {sig : ConstitutiveSignature.{s,r,p}} {symbol : sig.Symbol}
variable {rolePort occurrencePort : sig.Port symbol}
variable {q₁ q₂ q₃ : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort}

def identity (q : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort) : EquippedEquiv q q :=
  ⟨.identity _, .identity _, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def inverse (f : EquippedEquiv q₁ q₂) : EquippedEquiv q₂ q₁ where
  core := f.core.inverse
  signature := f.signature.inverse
  roleMapExact := ExactTransport.backward_eq_of_forward_eq _ _ f.roleMapExact
  occurrenceMapExact := ExactTransport.backward_eq_of_forward_eq _ _ f.occurrenceMapExact
  graphExact := by
    intro witness
    have eq := f.graphExact (f.core.witnesses.backward witness)
    rw [f.core.witnesses.backwardForward] at eq
    exact (congrArg (f.signature.witnesses symbol).backward eq).symm.trans
      ((f.signature.witnesses symbol).forwardBackward _)

def compose (f : EquippedEquiv q₁ q₂) (g : EquippedEquiv q₂ q₃) : EquippedEquiv q₁ q₃ where
  core := f.core.compose g.core
  signature := f.signature.compose g.signature
  roleMapExact := fun x =>
    (congrArg g.core.roles.forward (f.roleMapExact x)).trans (g.roleMapExact _)
  occurrenceMapExact := fun x =>
    (congrArg g.core.occurrences.forward (f.occurrenceMapExact x)).trans (g.occurrenceMapExact _)
  graphExact := fun witness =>
    (congrArg (g.signature.witnesses symbol).forward (f.graphExact witness)).trans
      (g.graphExact (f.core.witnesses.forward witness))

end EquippedEquiv
end RelationalFoundations
