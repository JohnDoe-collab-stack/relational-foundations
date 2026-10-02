/-!
# Concrete binary representation size

This module defines an executable binary digit count for natural numbers by
repeated division by two.  The fuel is explicit and structurally decreasing.

The coarse theorem natBitSize n <= n+1 is intentionally weaker than the usual
logarithmic closed form.  It is nevertheless a proved bound on a genuinely
binary representation size, and it is sufficient for a first polynomial cost
envelope without importing an unproved logarithmic estimate.
-/

namespace ConstitutiveSearch

namespace BinaryRepresentation

/-- Number of binary digits generated within an explicit recursion fuel. -/
def natBitSizeCore : Nat → Nat → Nat
  | 0, _ =>
      0
  | fuel + 1, value =>
      if value / 2 = 0 then
        1
      else
        Nat.succ
          (natBitSizeCore
            fuel
            (value / 2))

/-- Executable binary digit count for a natural number. -/
def natBitSize
    (value : Nat) : Nat :=
  natBitSizeCore
    (value + 1)
    value

/-- Core binary-size recursion can never consume more digits than its fuel. -/
theorem natBitSizeCore_le_fuel :
    ∀ (fuel value : Nat),
      natBitSizeCore fuel value ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro value
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      intro value
      unfold natBitSizeCore
      by_cases quotientZero : value / 2 = 0
      · rw [if_pos quotientZero]
        exact
          Nat.succ_le_succ
            (Nat.zero_le fuel)
      · rw [if_neg quotientZero]
        exact
          Nat.succ_le_succ
            (inductionHypothesis
              (value / 2))

/-- Coarse linear upper bound on the concrete binary digit count. -/
theorem natBitSize_le_succ
    (value : Nat) :
    natBitSize value ≤ value + 1 :=
  natBitSizeCore_le_fuel
    (value + 1)
    value

end BinaryRepresentation

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.BinaryRepresentation.natBitSizeCore
#print axioms ConstitutiveSearch.BinaryRepresentation.natBitSize
#print axioms ConstitutiveSearch.BinaryRepresentation.natBitSizeCore_le_fuel
#print axioms ConstitutiveSearch.BinaryRepresentation.natBitSize_le_succ
/- AXIOM_AUDIT_END -/
