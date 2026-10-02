import RelationalFoundations.Regime
set_option genInjectivity false

namespace RelationalFoundations
universe u o s g

/-- The specification is an independent input family; adequacy gives only the stated implications. -/
structure NormativeAdequacy {Carrier : Type u} (Occurrence : Carrier → Type o)
    (Specification : Carrier → Type s) (Admission : Carrier → Type g) where
  sound : ∀ candidate, Occurrence candidate → Specification candidate → Admission candidate
  complete : ∀ candidate, Occurrence candidate → Admission candidate → Specification candidate

def globalNormativeAdequacy {Carrier : Type u} (Occurrence : Carrier → Type o)
    (Specification : Carrier → Type s) (Admission : Carrier → Type g)
    (sound : ∀ candidate, Specification candidate → Admission candidate)
    (complete : ∀ candidate, Admission candidate → Specification candidate) :
    NormativeAdequacy Occurrence Specification Admission :=
  ⟨fun candidate _ => sound candidate, fun candidate _ => complete candidate⟩

theorem adequacy_specification_rejected {Carrier : Type u}
    {Occurrence : Carrier → Type o} {Specification : Carrier → Type s} {Admission : Carrier → Type g}
    (adequacy : NormativeAdequacy Occurrence Specification Admission)
    (candidate : Carrier) (occurrence : Occurrence candidate)
    (rejected : Admission candidate → False) : Specification candidate → False :=
  fun specification => rejected (adequacy.sound candidate occurrence specification)

end RelationalFoundations
