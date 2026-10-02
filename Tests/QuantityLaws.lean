import RelationalFoundations
set_option genInjectivity false

namespace RelationalFoundations.QuantityTests

def boolQuantity : StructuralQuantity :=
  ⟨Unit, Unit, fun _ _ => Bool, ⟨.reflexive _, fun _ => false⟩⟩

def unitQuantity : StructuralQuantity :=
  ⟨Unit, Unit, fun _ _ => Unit, ⟨.reflexive _, fun _ => ()⟩⟩

theorem same_carriers_do_not_imply_constitutive_equivalence :
    ConstitutiveEquiv boolQuantity unitQuantity → False := by
  intro f
  have targetEqual : f.witnesses.forward ⟨(), (), false⟩ = f.witnesses.forward ⟨(), (), true⟩ := by
    rcases f.witnesses.forward ⟨(), (), false⟩ with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    rcases f.witnesses.forward ⟨(), (), true⟩ with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl
  have sourceEqual := f.witnesses.forward_injective targetEqual
  have impossible := congrArg (fun w : boolQuantity.Witness => w.2.2) sourceEqual
  cases impossible

def boolIdentity : ConstitutiveEquiv boolQuantity boolQuantity := .identity _

theorem derived_fiber_preserves_each_witness (w : Bool) :
    (boolIdentity.realizesFiber () ()).backward ((boolIdentity.realizesFiber () ()).forward w) = w :=
  (boolIdentity.realizesFiber () ()).forwardBackward w

theorem composed_witnesses_exact (w : Bool) :
    ((boolIdentity.compose boolIdentity).compose boolIdentity).witnesses.forward ⟨(), (), w⟩ =
      (boolIdentity.compose (boolIdentity.compose boolIdentity)).witnesses.forward ⟨(), (), w⟩ :=
  ConstitutiveEquiv.compose_assoc_witness _ _ _ _

def emptySignature : ConstitutiveSignature where
  SortName := Unit
  Symbol := Empty
  Port := fun e => nomatch e
  portSort := fun e => nomatch e

def emptyInterpretation : SignatureInterpretation emptySignature where
  Carrier := fun _ => Unit
  Witness := fun e => nomatch e
  incidence := fun e => nomatch e

def emptySignatureTransport : SignatureTransport emptyInterpretation emptyInterpretation := .identity _

def witnessSignature : ConstitutiveSignature where
  SortName := Unit
  Symbol := Unit
  Port := fun _ => Empty
  portSort := fun _ e => nomatch e

def witnessInterpretation : SignatureInterpretation witnessSignature where
  Carrier := fun _ => Unit
  Witness := fun _ => Bool
  incidence := fun _ _ e => nomatch e

def unpointedSwap : SignatureTransport witnessInterpretation witnessInterpretation where
  sorts := fun _ => .reflexive _
  witnesses := fun _ =>
    ⟨Bool.not, Bool.not, fun w => by cases w <;> rfl, fun w => by cases w <;> rfl⟩
  incidenceExact := fun _ _ e => nomatch e

def witnessMarks : DistinguishedSignature witnessSignature := ⟨Unit, fun _ => ()⟩
def pointedWitness : MarkedInterpretation witnessMarks := ⟨witnessInterpretation, fun _ => false⟩

theorem unpointed_map_fails_distinguished_coherence :
    ¬ ((unpointedSwap.witnesses ()).forward (pointedWitness.distinguished ()) =
      pointedWitness.distinguished ()) := by
  intro eq
  cases eq

theorem instance_quantity_is_equipped :
    Perimetral.equippedQuantity.quantity.Role = Perimetral.presentation.InternalRole := rfl

theorem primitive_junction_is_preserved :
    (Perimetral.circularIdentity.equipped.signature.witnesses Perimetral.Symbol.closing).forward
      Perimetral.presentation.junction = Perimetral.presentation.junction :=
  Perimetral.circularIdentity.preserves Perimetral.Mark.junction

theorem composed_circular_transport_preserves_junction :
    (((Perimetral.circularIdentity.inverse).compose Perimetral.circularIdentity).equipped.signature.witnesses
      Perimetral.Symbol.closing).forward Perimetral.presentation.junction = Perimetral.presentation.junction :=
  ((Perimetral.circularIdentity.inverse).compose Perimetral.circularIdentity).preserves Perimetral.Mark.junction

def completeCoupledTurning :
    (FaithfulContinuation.ofOneStep Perimetral.continuation).CoupledTurning Perimetral.regime :=
  (FaithfulContinuation.ofOneStep Perimetral.continuation).coupledTurning Perimetral.regime

theorem general_residual_recovers_actual_witness :
    (FaithfulContinuation.ofOneStep Perimetral.continuation).generatedStep.witness =
      Perimetral.continuation.witness := FaithfulContinuation.ofOneStep_witness_exact _

def obstructedInterior := ObstructedFormation.attach Perimetral.obstruction (Formation.deployed Perimetral.spine)

theorem obstruction_is_actually_inherited : obstructedInterior.inherited = Perimetral.obstruction :=
  ObstructedFormation.inherited_attach _ _

end RelationalFoundations.QuantityTests
