import RelationalFoundations.MarkedQuantity
set_option genInjectivity false

namespace RelationalFoundations
universe u v w s r p a m

namespace ConstitutiveEquiv
variable {q₁ q₂ q₃ : StructuralQuantity.{u,v,w}}

theorem realizesFiber_total (f : ConstitutiveEquiv q₁ q₂) (role : q₁.Role) (occurrence : q₁.Occurrence)
    (witness : q₁.Realizes role occurrence) :
    (⟨f.roles.forward role, f.occurrences.forward occurrence,
      (f.realizesFiber role occurrence).forward witness⟩ : q₂.Witness) =
      f.witnesses.forward ⟨role, occurrence, witness⟩ :=
  congrArg Subtype.val ((q₂.realizesFiber (f.roles.forward role) (f.occurrences.forward occurrence)).backwardForward
    ((f.witnessFiber role occurrence).forward ((q₁.realizesFiber role occurrence).forward witness)))

theorem realizesFiber_compose (f : ConstitutiveEquiv q₁ q₂) (g : ConstitutiveEquiv q₂ q₃)
    (role : q₁.Role) (occurrence : q₁.Occurrence) (witness : q₁.Realizes role occurrence) :
    ((f.compose g).realizesFiber role occurrence).forward witness =
      (g.realizesFiber (f.roles.forward role) (f.occurrences.forward occurrence)).forward
        ((f.realizesFiber role occurrence).forward witness) := by
  apply (q₃.realizesFiber _ _).forward_injective
  apply Subtype.ext
  exact ((f.compose g).realizesFiber_total role occurrence witness).trans
    ((congrArg g.witnesses.forward (f.realizesFiber_total role occurrence witness)).symm.trans
      (g.realizesFiber_total _ _ _).symm)

theorem realizesFiber_identity (role : q₁.Role) (occurrence : q₁.Occurrence)
    (witness : q₁.Realizes role occurrence) :
    ((identity q₁).realizesFiber role occurrence).forward witness = witness := by
  apply (q₁.realizesFiber role occurrence).forward_injective
  apply Subtype.ext
  exact (identity q₁).realizesFiber_total role occurrence witness
end ConstitutiveEquiv

namespace SignatureTransport
variable {sig : ConstitutiveSignature.{s,r,p}}
variable {q₁ q₂ q₃ q₄ : SignatureInterpretation.{s,r,p,a,w} sig}

theorem compose_assoc_sort (f : SignatureTransport q₁ q₂) (g : SignatureTransport q₂ q₃)
    (h : SignatureTransport q₃ q₄) (sort : sig.SortName) (value : q₁.Carrier sort) :
    (((f.compose g).compose h).sorts sort).forward value =
      ((f.compose (g.compose h)).sorts sort).forward value := rfl

theorem compose_assoc_witness (f : SignatureTransport q₁ q₂) (g : SignatureTransport q₂ q₃)
    (h : SignatureTransport q₃ q₄) (symbol : sig.Symbol) (value : q₁.Witness symbol) :
    (((f.compose g).compose h).witnesses symbol).forward value =
      ((f.compose (g.compose h)).witnesses symbol).forward value := rfl

theorem inverse_sort (f : SignatureTransport q₁ q₂) (sort : sig.SortName) (value : q₁.Carrier sort) :
    (f.inverse.sorts sort).forward ((f.sorts sort).forward value) = value :=
  (f.sorts sort).forwardBackward value

theorem inverse_witness (f : SignatureTransport q₁ q₂) (symbol : sig.Symbol) (value : q₁.Witness symbol) :
    (f.inverse.witnesses symbol).forward ((f.witnesses symbol).forward value) = value :=
  (f.witnesses symbol).forwardBackward value
end SignatureTransport

namespace EquippedEquiv
variable {sig : ConstitutiveSignature.{s,r,p}} {symbol : sig.Symbol}
variable {rolePort occurrencePort : sig.Port symbol}
variable {q₁ q₂ q₃ q₄ : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort}

theorem compose_assoc_witness (f : EquippedEquiv q₁ q₂) (g : EquippedEquiv q₂ q₃)
    (h : EquippedEquiv q₃ q₄) (value : q₁.quantity.Witness) :
    ((f.compose g).compose h).core.witnesses.forward value =
      (f.compose (g.compose h)).core.witnesses.forward value := rfl

theorem left_identity (f : EquippedEquiv q₁ q₂) (value : q₁.quantity.Witness) :
    ((identity q₁).compose f).core.witnesses.forward value = f.core.witnesses.forward value := rfl

theorem right_identity (f : EquippedEquiv q₁ q₂) (value : q₁.quantity.Witness) :
    (f.compose (identity q₂)).core.witnesses.forward value = f.core.witnesses.forward value := rfl

theorem inverse_roundTrip (f : EquippedEquiv q₁ q₂) (value : q₁.quantity.Witness) :
    (f.compose f.inverse).core.witnesses.forward value = value := f.core.witnesses.forwardBackward value

theorem equivalent_refl (q : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort) :
    Nonempty (EquippedEquiv q q) := ⟨identity q⟩
theorem equivalent_symm (h : Nonempty (EquippedEquiv q₁ q₂)) : Nonempty (EquippedEquiv q₂ q₁) :=
  h.elim fun f => ⟨f.inverse⟩
theorem equivalent_trans (h : Nonempty (EquippedEquiv q₁ q₂)) (k : Nonempty (EquippedEquiv q₂ q₃)) :
    Nonempty (EquippedEquiv q₁ q₃) := h.elim fun f => k.elim fun g => ⟨f.compose g⟩
end EquippedEquiv

namespace MarkedQuantityEquiv
variable {sig : ConstitutiveSignature.{s,r,p}} {symbol : sig.Symbol}
variable {rolePort occurrencePort : sig.Port symbol} {marks : DistinguishedSignature.{s,r,p,m} sig}
variable {q₁ q₂ q₃ : MarkedQuantity.{s,r,p,a,w,m} symbol rolePort occurrencePort marks}

theorem equivalent_refl (q : MarkedQuantity.{s,r,p,a,w,m} symbol rolePort occurrencePort marks) :
    Nonempty (MarkedQuantityEquiv q q) := ⟨identity q⟩
theorem equivalent_symm (h : Nonempty (MarkedQuantityEquiv q₁ q₂)) : Nonempty (MarkedQuantityEquiv q₂ q₁) :=
  h.elim fun f => ⟨f.inverse⟩
theorem equivalent_trans (h : Nonempty (MarkedQuantityEquiv q₁ q₂)) (k : Nonempty (MarkedQuantityEquiv q₂ q₃)) :
    Nonempty (MarkedQuantityEquiv q₁ q₃) := h.elim fun f => k.elim fun g => ⟨f.compose g⟩
end MarkedQuantityEquiv
end RelationalFoundations
