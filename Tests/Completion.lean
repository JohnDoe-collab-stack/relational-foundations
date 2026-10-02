import RelationalFoundations
set_option genInjectivity false

namespace RelationalFoundations.CompletionTests
open Perimetral
universe u v t i c

def genericCircularQuantity (p : CircularPresentation.{u,v,t,i,c}) := CircularSignature.circularQuantity p

def canonicalSpecification : CircularSpecificationSatisfaction presentation obstruction presentation.interiorConstruction :=
  .canonical _ _

theorem continuation_fails_independent_specification :
    CircularSpecificationSatisfaction presentation obstruction continuation.construction → False :=
  CircularSpecificationSatisfaction.rejectsStrict (continuation.strictExtension continuation.construction_different)

def normativeAdequacy := CircularSpecificationSatisfaction.adequacy presentation obstruction regime

def specification_sound : regime.Admission presentation.interiorConstruction :=
  canonicalSpecification.sound regime

def specification_complete : CircularSpecificationSatisfaction presentation obstruction presentation.interiorConstruction :=
  CircularSpecificationSatisfaction.complete regime regime.canonicalAdmission

/-- The formation graph covers generated formations beyond the perimeter. -/
def outsidePerimeterAdvance : CircularSignature.FormationAdvance presentation :=
  ⟨.free 0, .free 1, continuation.formation, .licensed true⟩

theorem arbitrary_formation_is_preserved :
    ((CircularSignature.circularIdentity presentation).equipped.signature.sorts .formation).forward
      ⟨outsidePerimeterAdvance.target, .formed outsidePerimeterAdvance.previous outsidePerimeterAdvance.step⟩ =
    CircularSignature.incidence presentation .formationAdvance
      (((CircularSignature.circularIdentity presentation).equipped.signature.witnesses .formationAdvance).forward
        ⟨outsidePerimeterAdvance⟩) .right :=
  CircularSignature.preserves_formation_constructor _ _

def outsidePerimeterRecord : CircularSignature.PreservedRecord presentation where
  toFormationAdvance := outsidePerimeterAdvance
  record := .current

theorem arbitrary_record_is_preserved :
    ((CircularSignature.circularIdentity presentation).equipped.signature.sorts .provenance).forward
      ⟨outsidePerimeterRecord.target, .formed outsidePerimeterRecord.previous outsidePerimeterRecord.step,
        .preserved outsidePerimeterRecord.record⟩ =
    CircularSignature.incidence presentation .recordPreserved
      (((CircularSignature.circularIdentity presentation).equipped.signature.witnesses .recordPreserved).forward
        ⟨outsidePerimeterRecord⟩) .right :=
  CircularSignature.preserves_historical_record _ _

theorem generic_junction_preserved :
    ((CircularSignature.circularIdentity presentation).equipped.signature.witnesses .closing).forward
      ⟨presentation.junction⟩ = ⟨presentation.junction⟩ :=
  CircularSignature.preserves_junction _

theorem finite_invariance {n m : Nat} (transport : ExactTransport (Fin n) (Fin m)) : n = m :=
  FiniteInvariance.cardinal_eq transport

theorem quantity_invariance {n m : Nat}
    (first : ExactTransport interiorQuantity.Occurrence (Fin n))
    (second : ExactTransport interiorQuantity.Occurrence (Fin m)) : n = m :=
  FiniteInvariance.quantity_cardinal_eq (.identity _) first second

def producer (node : Node) : Σ target : Node, Next node target := ⟨next node, generatedStep node⟩

theorem iteration_is_actual (n : Nat) :
    ConstitutiveGeneration.iterate presentation.interiorConstruction producer n = iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg
      (fun previous : RootedConstruction Next Node.first =>
        (⟨next previous.endpoint, .extend previous.history (generatedStep previous.endpoint)⟩ :
          RootedConstruction Next Node.first)) ih
end RelationalFoundations.CompletionTests
