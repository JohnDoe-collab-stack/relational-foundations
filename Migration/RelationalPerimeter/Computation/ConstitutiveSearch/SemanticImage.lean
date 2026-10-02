/-!
# Semantic admission of an executed image

The description contains data and predicates, but no preservation proof.
An image value becomes usable as an obligation only with the specification
of its actual preimages. The consumer is generic: no concrete execution or
SAT relation is available here to recover a missing guarantee.
-/
namespace ConstitutiveSearch.SemanticImage

structure Description where
  Source : Type
  Payload : Source → Type
  Target : Type
  Accept : (source : Source) → Payload source → Prop
  TargetAccept : Target → Prop
  action : (source : Source) → Payload source → Target
  canonical : (source : Source) → Payload source
  produced : Source → Target
  reflect : Target → (Sigma fun source => Payload source)
  SourceInvariant : Prop

/-- Admission is separate from membership in the produced image. -/
def Specification (description : Description) (value : description.Target) : Prop :=
  description.SourceInvariant ∧
    (∀ source, description.produced source = value →
      description.action source (description.canonical source) = value ∧
      ∀ payload, description.Accept source payload →
        description.TargetAccept (description.action source payload)) ∧
    (∀ target, description.TargetAccept target →
      description.Accept (description.reflect target).1 (description.reflect target).2)

/-- A dependent consumer of the guarantee, without a richer execution input. -/
def use
    {description : Description} {value : description.Target}
    (specification : Specification description value)
    (source : description.Source)
    (preimage : description.produced source = value)
    (payload : description.Payload source) :
    {result : description.Target //
      result = description.action source payload ∧
      (description.Accept source payload → description.TargetAccept result)} :=
  ⟨description.action source payload, rfl, (specification.2.1 source preimage).2 payload⟩

theorem canonical_exact
    {description : Description} {value : description.Target}
    (specification : Specification description value)
    (source : description.Source) (preimage : description.produced source = value) :
    description.action source (description.canonical source) = value :=
  (specification.2.1 source preimage).1

theorem source_invariant
    {description : Description} {value : description.Target}
    (specification : Specification description value) : description.SourceInvariant :=
  specification.1

/-- Instantiate the specification from independent semantic obligations. -/
theorem certify
    (description : Description)
    (invariant : description.SourceInvariant)
    (canonicalExact : ∀ source,
      description.action source (description.canonical source) = description.produced source)
    (preservation : ∀ source payload, description.Accept source payload →
      description.TargetAccept (description.action source payload))
    (reflection : ∀ target, description.TargetAccept target →
      description.Accept (description.reflect target).1 (description.reflect target).2)
    (value : description.Target) : Specification description value :=
  ⟨invariant, (fun source preimage =>
    ⟨Eq.trans (canonicalExact source) preimage, preservation source⟩), reflection⟩

/-- Semantic admission of specified data; no execution or width is available. -/
structure Admission (description : Description) : Prop where
  invariant : description.SourceInvariant
  canonicalExact : ∀ source,
    description.action source (description.canonical source) = description.produced source
  preservation : ∀ source payload, description.Accept source payload →
    description.TargetAccept (description.action source payload)
  reflection : ∀ target, description.TargetAccept target →
    description.Accept (description.reflect target).1 (description.reflect target).2

theorem Admission.specification {description : Description}
    (admission : Admission description) (value : description.Target) :
    Specification description value :=
  certify description admission.invariant admission.canonicalExact
    admission.preservation admission.reflection value

/-- Image membership and semantic admission are different obligations.
The predicate of production may retain dependent traces; it supplies no semantics. -/
structure AdmittedImageValue (description : Description)
    (Produced : description.Target → Prop) where
  admitted ::
  value : description.Target
  produced : Produced value
  semantics : Specification description value

/-- This generic consumer has no concrete reduction from which to recover evidence. -/
def AdmittedImageValue.transformPayload
    {description : Description} {Produced : description.Target → Prop}
    (obligation : AdmittedImageValue description Produced)
    (source : description.Source) (preimage : description.produced source = obligation.value)
    (payload : description.Payload source) :=
  use obligation.semantics source preimage payload

theorem AdmittedImageValue.sourceInvariant
    {description : Description} {Produced : description.Target → Prop}
    (obligation : AdmittedImageValue description Produced) : description.SourceInvariant :=
  source_invariant obligation.semantics

/-- Obligation equality only forgets proof fields, never identifies source profiles. -/
theorem AdmittedImageValue.eq_of_value_eq
    {description : Description} {Produced : description.Target → Prop}
    {left right : AdmittedImageValue description Produced}
    (same : left.value = right.value) : left = right := by
  cases left with
  | admitted lv lp ls =>
    cases right with
    | admitted rv rp rs =>
      change lv = rv at same
      cases same
      rfl

/-- The family of admitted image values preserves and reflects global viability. -/
theorem viable_iff
    (description : Description)
    (admission : ∀ source, Specification description (description.produced source)) :
    (∃ source payload, description.Accept source payload) ↔
      (∃ target, description.TargetAccept target) := by
  constructor
  · intro viable
    rcases viable with ⟨source, payload, accepted⟩
    exact ⟨description.action source payload,
      ((admission source).2.1 source rfl).2 payload accepted⟩
  · intro viable
    rcases viable with ⟨target, accepted⟩
    let restored := description.reflect target
    exact ⟨restored.1, restored.2, (admission restored.1).2.2 target accepted⟩

end ConstitutiveSearch.SemanticImage
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SemanticImage.Admission
#print axioms ConstitutiveSearch.SemanticImage.Admission.specification
#print axioms ConstitutiveSearch.SemanticImage.AdmittedImageValue
#print axioms ConstitutiveSearch.SemanticImage.AdmittedImageValue.transformPayload
#print axioms ConstitutiveSearch.SemanticImage.AdmittedImageValue.sourceInvariant
#print axioms ConstitutiveSearch.SemanticImage.AdmittedImageValue.eq_of_value_eq

#print axioms ConstitutiveSearch.SemanticImage.Description
#print axioms ConstitutiveSearch.SemanticImage.Specification
#print axioms ConstitutiveSearch.SemanticImage.use
#print axioms ConstitutiveSearch.SemanticImage.canonical_exact
#print axioms ConstitutiveSearch.SemanticImage.source_invariant
#print axioms ConstitutiveSearch.SemanticImage.viable_iff
#print axioms ConstitutiveSearch.SemanticImage.certify
/- AXIOM_AUDIT_END -/
