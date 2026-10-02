import RelationalFoundations.ExactTransport
set_option genInjectivity false

namespace RelationalFoundations
universe s r p a w m

set_option linter.checkUnivs false in
/-- An incidence signature. Dependent operations are represented by their typed graphs. -/
structure ConstitutiveSignature where
  SortName : Type s
  Symbol : Type r
  Port : Symbol → Type p
  portSort : (symbol : Symbol) → Port symbol → SortName

set_option linter.checkUnivs false in
structure SignatureInterpretation (sig : ConstitutiveSignature.{s,r,p}) where
  Carrier : sig.SortName → Type a
  Witness : sig.Symbol → Type w
  incidence : (symbol : sig.Symbol) → Witness symbol →
    (port : sig.Port symbol) → Carrier (sig.portSort symbol port)

structure SignatureTransport {sig : ConstitutiveSignature.{s,r,p}}
    (first second : SignatureInterpretation.{s,r,p,a,w} sig) where
  sorts : (sort : sig.SortName) → ExactTransport (first.Carrier sort) (second.Carrier sort)
  witnesses : (symbol : sig.Symbol) → ExactTransport (first.Witness symbol) (second.Witness symbol)
  incidenceExact : ∀ symbol witness port,
    (sorts (sig.portSort symbol port)).forward (first.incidence symbol witness port) =
      second.incidence symbol ((witnesses symbol).forward witness) port

namespace SignatureTransport
variable {sig : ConstitutiveSignature.{s,r,p}}
variable {a₁ a₂ a₃ : SignatureInterpretation.{s,r,p,a,w} sig}

def identity (value : SignatureInterpretation.{s,r,p,a,w} sig) : SignatureTransport value value :=
  ⟨fun _ => .reflexive _, fun _ => .reflexive _, fun _ _ _ => rfl⟩

def inverse (f : SignatureTransport a₁ a₂) : SignatureTransport a₂ a₁ where
  sorts := fun sort => (f.sorts sort).reverse
  witnesses := fun symbol => (f.witnesses symbol).reverse
  incidenceExact := by
    intro symbol witness port
    have eq := f.incidenceExact symbol ((f.witnesses symbol).backward witness) port
    rw [(f.witnesses symbol).backwardForward] at eq
    exact (congrArg (f.sorts _).backward eq).symm.trans
      ((f.sorts _).forwardBackward _)

def compose (f : SignatureTransport a₁ a₂) (g : SignatureTransport a₂ a₃) :
    SignatureTransport a₁ a₃ where
  sorts := fun sort => (f.sorts sort).compose (g.sorts sort)
  witnesses := fun symbol => (f.witnesses symbol).compose (g.witnesses symbol)
  incidenceExact := by
    intro symbol witness port
    exact (congrArg (g.sorts _).forward (f.incidenceExact symbol witness port)).trans
      (g.incidenceExact symbol ((f.witnesses symbol).forward witness) port)

theorem compose_sort_forward (f : SignatureTransport a₁ a₂) (g : SignatureTransport a₂ a₃)
    (sort : sig.SortName) (x : a₁.Carrier sort) :
    ((f.compose g).sorts sort).forward x = (g.sorts sort).forward ((f.sorts sort).forward x) := rfl

end SignatureTransport

structure DistinguishedSignature (sig : ConstitutiveSignature.{s,r,p}) where
  Mark : Type m
  symbol : Mark → sig.Symbol

set_option linter.checkUnivs false in
structure MarkedInterpretation {sig : ConstitutiveSignature.{s,r,p}}
    (marks : DistinguishedSignature.{s,r,p,m} sig) where
  interpretation : SignatureInterpretation.{s,r,p,a,w} sig
  distinguished : (mark : marks.Mark) → interpretation.Witness (marks.symbol mark)

structure MarkedTransport {sig : ConstitutiveSignature.{s,r,p}}
    {marks : DistinguishedSignature.{s,r,p,m} sig}
    (first second : MarkedInterpretation.{s,r,p,a,w,m} marks) where
  transport : SignatureTransport first.interpretation second.interpretation
  preserves : ∀ mark, (transport.witnesses (marks.symbol mark)).forward (first.distinguished mark) =
    second.distinguished mark

namespace MarkedTransport
variable {sig : ConstitutiveSignature.{s,r,p}} {marks : DistinguishedSignature.{s,r,p,m} sig}
variable {a₁ a₂ a₃ : MarkedInterpretation.{s,r,p,a,w,m} marks}

def identity (value : MarkedInterpretation.{s,r,p,a,w,m} marks) : MarkedTransport value value :=
  ⟨.identity _, fun _ => rfl⟩

def inverse (f : MarkedTransport a₁ a₂) : MarkedTransport a₂ a₁ where
  transport := f.transport.inverse
  preserves := fun mark =>
    (congrArg (f.transport.witnesses _).backward (f.preserves mark)).symm.trans
      ((f.transport.witnesses _).forwardBackward _)

def compose (f : MarkedTransport a₁ a₂) (g : MarkedTransport a₂ a₃) : MarkedTransport a₁ a₃ where
  transport := f.transport.compose g.transport
  preserves := fun mark =>
    (congrArg (g.transport.witnesses _).forward (f.preserves mark)).trans (g.preserves mark)

end MarkedTransport
end RelationalFoundations
