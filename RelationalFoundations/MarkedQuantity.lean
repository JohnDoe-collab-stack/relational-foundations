import RelationalFoundations.EquippedQuantity
set_option genInjectivity false

namespace RelationalFoundations
universe s r p a w m

set_option linter.checkUnivs false in
structure MarkedQuantity {sig : ConstitutiveSignature.{s,r,p}}
    (symbol : sig.Symbol) (rolePort occurrencePort : sig.Port symbol)
    (marks : DistinguishedSignature.{s,r,p,m} sig) where
  equipped : EquippedQuantity.{s,r,p,a,w} sig symbol rolePort occurrencePort
  distinguished : (mark : marks.Mark) → equipped.interpretation.Witness (marks.symbol mark)

structure MarkedQuantityEquiv {sig : ConstitutiveSignature.{s,r,p}}
    {symbol : sig.Symbol} {rolePort occurrencePort : sig.Port symbol}
    {marks : DistinguishedSignature.{s,r,p,m} sig}
    (first second : MarkedQuantity.{s,r,p,a,w,m} symbol rolePort occurrencePort marks) where
  equipped : EquippedEquiv first.equipped second.equipped
  preserves : ∀ mark,
    (equipped.signature.witnesses (marks.symbol mark)).forward (first.distinguished mark) =
      second.distinguished mark

namespace MarkedQuantityEquiv
variable {sig : ConstitutiveSignature.{s,r,p}}
variable {symbol : sig.Symbol} {rolePort occurrencePort : sig.Port symbol}
variable {marks : DistinguishedSignature.{s,r,p,m} sig}
variable {q₁ q₂ q₃ : MarkedQuantity.{s,r,p,a,w,m} symbol rolePort occurrencePort marks}

def identity (q : MarkedQuantity.{s,r,p,a,w,m} symbol rolePort occurrencePort marks) : MarkedQuantityEquiv q q :=
  ⟨.identity _, fun _ => rfl⟩

def inverse (f : MarkedQuantityEquiv q₁ q₂) : MarkedQuantityEquiv q₂ q₁ where
  equipped := f.equipped.inverse
  preserves := fun mark =>
    (congrArg (f.equipped.signature.witnesses _).backward (f.preserves mark)).symm.trans
      ((f.equipped.signature.witnesses _).forwardBackward _)

def compose (f : MarkedQuantityEquiv q₁ q₂) (g : MarkedQuantityEquiv q₂ q₃) : MarkedQuantityEquiv q₁ q₃ where
  equipped := f.equipped.compose g.equipped
  preserves := fun mark =>
    (congrArg (g.equipped.signature.witnesses _).forward (f.preserves mark)).trans (g.preserves mark)

end MarkedQuantityEquiv
end RelationalFoundations
