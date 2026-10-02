/-!
# Constructive structural lemmas

This module contains the small arithmetic and list identities needed by the
constitutive development when the corresponding library theorem carries an
axiomatic dependency.  Every proof below is structural and computational.
-/

namespace ConstitutiveSearch
namespace Constructive

/-- A natural number is below its maximum with any other natural number. -/
theorem nat_le_max_left :
    ∀ left right : Nat,
      left ≤ Nat.max left right
  | left, right => by
      change left ≤ max left right
      rw [Nat.max_def]
      by_cases leftLe : left ≤ right
      · rw [if_pos leftLe]
        exact leftLe
      · rw [if_neg leftLe]
        exact Nat.le_refl left

/-- The right argument is below the maximum. -/
theorem nat_le_max_right :
    ∀ left right : Nat,
      right ≤ Nat.max left right
  | left, right => by
      change right ≤ max left right
      rw [Nat.max_def]
      by_cases leftLe : left ≤ right
      · rw [if_pos leftLe]
        exact Nat.le_refl right
      · rw [if_neg leftLe]
        exact Nat.le_of_not_ge leftLe

/-- A common upper bound is an upper bound for the maximum. -/
theorem nat_max_le :
    ∀ left right bound : Nat,
      left ≤ bound →
      right ≤ bound →
      Nat.max left right ≤ bound
  | left, right, _, leftLe, rightLe => by
      change max left right ≤ _
      rw [Nat.max_def]
      by_cases leftRight : left ≤ right
      · rw [if_pos leftRight]
        exact rightLe
      · rw [if_neg leftRight]
        exact leftLe

/-- Taking the maximum of a natural number with itself is inert. -/
theorem nat_max_self :
    ∀ value : Nat,
      Nat.max value value = value
  | value => by
      change max value value = value
      rw [Nat.max_def, if_pos (Nat.le_refl value)]

/-- Zero is inert on the right of natural maximum. -/
theorem nat_max_zero :
    ∀ value : Nat,
      Nat.max value 0 = value
  | 0 => rfl
  | Nat.succ value => by
      change max (Nat.succ value) 0 = Nat.succ value
      rw [
        Nat.max_def,
        if_neg (Nat.not_succ_le_zero value)
      ]

/-- Adding two successors is the doubled predecessor plus two. -/
theorem nat_double_add_two
    (value : Nat) :
    (value + value + 1) + 1 =
      (value + 1) + (value + 1) := by
  calc
    (value + value + 1) + 1 =
        (value + (value + 1)) + 1 :=
      congrArg
        (fun total => total + 1)
        (Nat.add_assoc value value 1)
    _ = (value + (1 + value)) + 1 :=
      congrArg
        (fun total => total + 1)
        (congrArg
          (Nat.add value)
          (Nat.add_comm value 1))
    _ = ((value + 1) + value) + 1 :=
      congrArg
        (fun total => total + 1)
        (Nat.add_assoc value 1 value).symm
    _ = (value + 1) + (value + 1) :=
      Nat.add_assoc (value + 1) value 1

/-- Interchange the middle terms of two natural sums. -/
theorem nat_add_pair_swap
    (first second third fourth : Nat) :
    (first + second) + (third + fourth) =
      (first + third) + (second + fourth) := by
  calc
    (first + second) + (third + fourth) =
        first + (second + (third + fourth)) :=
      Nat.add_assoc first second (third + fourth)
    _ = first + ((second + third) + fourth) :=
      congrArg
        (Nat.add first)
        (Nat.add_assoc second third fourth).symm
    _ = first + ((third + second) + fourth) :=
      congrArg
        (Nat.add first)
        (congrArg
          (fun total => total + fourth)
          (Nat.add_comm second third))
    _ = first + (third + (second + fourth)) :=
      congrArg
        (Nat.add first)
        (Nat.add_assoc third second fourth)
    _ = (first + third) + (second + fourth) :=
      (Nat.add_assoc first third (second + fourth)).symm

/-- Associativity of multiplication, proved by recursion on the final factor. -/
theorem nat_mul_assoc
    (first second : Nat) :
    ∀ third : Nat,
      (first * second) * third =
        first * (second * third)
  | 0 => rfl
  | Nat.succ third =>
      calc
        (first * second) * Nat.succ third =
            (first * second) * third + first * second := rfl
        _ = first * (second * third) + first * second :=
          congrArg
            (fun total => total + first * second)
            (nat_mul_assoc first second third)
        _ = first * (second * third + second) :=
          (Nat.mul_add first (second * third) second).symm
        _ = first * (second * Nat.succ third) := rfl

/-- Interchange the middle factors of two natural products. -/
theorem nat_mul_pair_swap
    (first second third fourth : Nat) :
    (first * second) * (third * fourth) =
      (first * third) * (second * fourth) := by
  calc
    (first * second) * (third * fourth) =
        first * (second * (third * fourth)) :=
      nat_mul_assoc first second (third * fourth)
    _ = first * ((second * third) * fourth) :=
      congrArg
        (Nat.mul first)
        (nat_mul_assoc second third fourth).symm
    _ = first * ((third * second) * fourth) :=
      congrArg
        (Nat.mul first)
        (congrArg
          (fun total => total * fourth)
          (Nat.mul_comm second third))
    _ = first * (third * (second * fourth)) :=
      congrArg
        (Nat.mul first)
        (nat_mul_assoc third second fourth)
    _ = (first * third) * (second * fourth) :=
      (nat_mul_assoc first third (second * fourth)).symm

/-- Left addition distributes over multiplication without library automation. -/
theorem nat_add_mul
    (first second : Nat) :
    ∀ factor : Nat,
      (first + second) * factor =
        first * factor + second * factor
  | 0 => rfl
  | Nat.succ factor =>
      calc
        (first + second) * Nat.succ factor =
            (first + second) * factor +
              (first + second) := rfl
        _ = (first * factor + second * factor) +
              (first + second) :=
          congrArg
            (fun total => total + (first + second))
            (nat_add_mul first second factor)
        _ = (first * factor + first) +
              (second * factor + second) :=
          nat_add_pair_swap
            (first * factor)
            (second * factor)
            first
            second
        _ = first * Nat.succ factor +
              second * Nat.succ factor := rfl

/-- Addition of exponents becomes multiplication of natural powers. -/
theorem nat_pow_add
    (base firstExponent : Nat) :
    ∀ secondExponent : Nat,
      base ^ (firstExponent + secondExponent) =
        base ^ firstExponent * base ^ secondExponent
  | 0 => (Nat.mul_one (base ^ firstExponent)).symm
  | Nat.succ secondExponent =>
      Eq.trans
        (congrArg
          (fun value => value * base)
          (nat_pow_add
            base
            firstExponent
            secondExponent))
        (nat_mul_assoc
          (base ^ firstExponent)
          (base ^ secondExponent)
          base)

/-- Multiplication of exponents becomes iterated natural powers. -/
theorem nat_pow_mul
    (base firstExponent : Nat) :
    ∀ secondExponent : Nat,
      base ^ (firstExponent * secondExponent) =
        (base ^ firstExponent) ^ secondExponent
  | 0 => rfl
  | Nat.succ secondExponent =>
      Eq.trans
        (nat_pow_add
          base
          (firstExponent * secondExponent)
          firstExponent)
        (congrArg
          (fun value => value * (base ^ firstExponent))
          (nat_pow_mul
            base
            firstExponent
            secondExponent))

/-- A positive natural distinct from one is at least two. -/
theorem two_le_of_pos_of_ne_one
    {value : Nat}
    (positive : 0 < value)
    (notOne : value ≠ 1) :
    2 ≤ value := by
  cases value with
  | zero => nomatch positive
  | succ predecessor =>
      cases predecessor with
      | zero => exact False.elim (notOne rfl)
      | succ rest =>
          exact
            Nat.succ_le_succ
              (Nat.succ_le_succ
                (Nat.zero_le rest))

/-- No natural number is equal to its successor. -/
theorem nat_ne_add_one :
    ∀ value : Nat,
      value ≠ value + 1
  | 0 => fun impossible => Nat.noConfusion impossible
  | Nat.succ value => fun impossible =>
      nat_ne_add_one
        value
        (Nat.succ.inj impossible)

/-- One is below twice every positive successor. -/
theorem one_le_two_mul_succ
    (value : Nat) :
    1 ≤ 2 * (value + 1) := by
  change
    Nat.succ 0 ≤
      Nat.succ (Nat.succ (2 * value))
  exact
    Nat.succ_le_succ
      (Nat.zero_le
        (Nat.succ (2 * value)))

/--
An executable floor logarithm in base two.

The definition scans the natural input once and increments its result exactly
when the next power-of-two threshold is reached.  It is deliberately local:
the corresponding library theorems currently carry propositional-extensionality
dependencies, whereas this project requires a fully constructive computational core.
-/
def natLog2 : Nat → Nat
  | 0 => 0
  | Nat.succ value =>
      let previous := natLog2 value
      match Nat.ble (2 ^ (previous + 1)) (Nat.succ value) with
      | true => previous + 1
      | false => previous

/-- Every power of two is positive. -/
theorem two_pow_positive
    (exponent : Nat) :
    0 < 2 ^ exponent :=
  Nat.pow_pos Nat.zero_lt_two

/-- Powers of two grow strictly with their exponents. -/
theorem two_pow_strictly_grows
    {smaller larger : Nat}
    (less : smaller < larger) :
    2 ^ smaller < 2 ^ larger := by
  have oneStep :
      2 ^ smaller < 2 ^ (smaller + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
    exact
      Nat.lt_add_of_pos_right
        (two_pow_positive smaller)
  exact
    Nat.lt_of_lt_of_le
      oneStep
      (Nat.pow_le_pow_right
        Nat.zero_lt_two
        less)

/-- Comparing two powers of two reflects comparison of their exponents. -/
theorem exponent_le_of_two_pow_le
    {left right : Nat}
    (powerLe : 2 ^ left ≤ 2 ^ right) :
    left ≤ right := by
  apply Nat.le_of_not_gt
  intro rightLess
  exact
    (Nat.not_le_of_gt
      (two_pow_strictly_grows rightLess))
      powerLe

/-- The power selected by the local logarithm stays below every positive input. -/
theorem two_pow_natLog2_le :
    ∀ {value : Nat},
      value ≠ 0 →
      2 ^ natLog2 value ≤ value := by
  intro value nonzero
  induction value with
  | zero => exact False.elim (nonzero rfl)
  | succ value inductionHypothesis =>
      cases threshold :
          Nat.ble
            (2 ^ (natLog2 value + 1))
            (Nat.succ value) with
      | true =>
          rw [natLog2, threshold]
          exact Nat.le_of_ble_eq_true threshold
      | false =>
          rw [natLog2, threshold]
          cases value with
          | zero => exact Nat.le_refl 1
          | succ predecessor =>
              exact
                Nat.le_trans
                  (inductionHypothesis
                    (fun impossible =>
                      Nat.noConfusion impossible))
                  (Nat.le_succ (Nat.succ predecessor))

/-- Every input lies strictly below the next selected power of two. -/
theorem lt_two_pow_natLog2_succ :
    ∀ value : Nat,
      value < 2 ^ (natLog2 value + 1)
  | 0 => Nat.zero_lt_succ 1
  | Nat.succ value => by
      cases threshold :
          Nat.ble
            (2 ^ (natLog2 value + 1))
            (Nat.succ value) with
      | true =>
        rw [natLog2, threshold]
        have atBoundary :
            Nat.succ value ≤
              2 ^ (natLog2 value + 1) :=
          Nat.succ_le_of_lt
            (lt_two_pow_natLog2_succ value)
        have nextBoundary :
            2 ^ (natLog2 value + 1) <
              2 ^ ((natLog2 value + 1) + 1) := by
          exact
            two_pow_strictly_grows
              (Nat.lt_succ_self
                (natLog2 value + 1))
        exact
          Nat.lt_of_le_of_lt
            atBoundary
            nextBoundary
      | false =>
        rw [natLog2, threshold]
        apply Nat.lt_of_not_ge
        intro reached
        have contradiction :
            Nat.ble
                (2 ^ (natLog2 value + 1))
                (Nat.succ value) = true :=
          Nat.ble_eq_true_of_le reached
        rw [threshold] at contradiction
        exact Bool.noConfusion contradiction

/-- The local logarithm is exact on powers of two. -/
theorem natLog2_two_pow :
    ∀ {exponent : Nat},
      natLog2 (2 ^ exponent) = exponent := by
      intro exponent
      have lowerPower :
          2 ^ natLog2 (2 ^ exponent) ≤
            2 ^ exponent :=
        two_pow_natLog2_le
          (Nat.ne_of_gt
            (two_pow_positive exponent))
      have logLe : natLog2 (2 ^ exponent) ≤ exponent :=
        exponent_le_of_two_pow_le lowerPower
      have exponentLt :
          exponent < natLog2 (2 ^ exponent) + 1 := by
        apply Nat.lt_of_not_ge
        intro nextLeExponent
        have powerLe :
            2 ^ (natLog2 (2 ^ exponent) + 1) ≤
              2 ^ exponent :=
          Nat.pow_le_pow_right
            Nat.zero_lt_two
            nextLeExponent
        exact
          (Nat.not_le_of_gt
            (lt_two_pow_natLog2_succ
              (2 ^ exponent)))
            powerLe
      exact
        Nat.le_antisymm
          logLe
          (Nat.le_of_lt_succ exponentLt)

/-- The local logarithm is monotone. -/
theorem natLog2_mono
    {smaller larger : Nat}
    (positive : smaller ≠ 0)
    (ordered : smaller ≤ larger) :
    natLog2 smaller ≤ natLog2 larger := by
  apply Nat.le_of_not_gt
  intro reverseLog
  have nextLogLe :
      natLog2 larger + 1 ≤ natLog2 smaller :=
    reverseLog
  have nextPowerLe :
      2 ^ (natLog2 larger + 1) ≤
        2 ^ natLog2 smaller :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      nextLogLe
  have selectedLeSmaller :
      2 ^ natLog2 smaller ≤ smaller :=
    two_pow_natLog2_le positive
  have impossibleLe :
      2 ^ (natLog2 larger + 1) ≤ larger :=
    Nat.le_trans
      (Nat.le_trans nextPowerLe selectedLeSmaller)
      ordered
  exact
    (Nat.not_le_of_gt
      (lt_two_pow_natLog2_succ larger))
      impossibleLe

/-- Associativity of list append, proved directly from the list constructors. -/
theorem list_append_assoc
    {α : Type} :
    ∀ first second third : List α,
      (first ++ second) ++ third =
        first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: tail, second, third =>
      congrArg
        (List.cons head)
        (list_append_assoc tail second third)

/-- Mapping distributes over append by structural recursion on the first list. -/
theorem list_map_append
    {α β : Type}
    (mapValue : α → β) :
    ∀ first second : List α,
      (first ++ second).map mapValue =
        first.map mapValue ++ second.map mapValue
  | [], _ => rfl
  | head :: tail, second =>
      congrArg
        (List.cons (mapValue head))
        (list_map_append mapValue tail second)

/-- Mapping twice is one structural map with the composed function. -/
theorem list_map_map
    {α β γ : Type}
    (firstMap : α → β)
    (secondMap : β → γ) :
    ∀ values : List α,
      (values.map firstMap).map secondMap =
        values.map (fun value => secondMap (firstMap value))
  | [] => rfl
  | head :: tail =>
      congrArg
        (List.cons (secondMap (firstMap head)))
        (list_map_map firstMap secondMap tail)

/-- Mapping the identity function leaves a list unchanged. -/
theorem list_map_id
    {α : Type} :
    ∀ values : List α,
      values.map (fun value => value) = values
  | [] => rfl
  | head :: tail =>
      congrArg
        (List.cons head)
        (list_map_id tail)

/-- Replication constructs exactly the requested number of list cells. -/
theorem list_length_replicate
    {α : Type}
    (value : α) :
    ∀ count : Nat,
      (List.replicate count value).length = count
  | 0 => rfl
  | Nat.succ count =>
      congrArg
        Nat.succ
        (list_length_replicate value count)

/-- Constructive inversion of membership in a cons cell. -/
theorem list_mem_cons_cases
    {α : Type}
    {value head : α}
    {tail : List α} :
    value ∈ head :: tail →
      value = head ∨ value ∈ tail
  | .head _ => Or.inl rfl
  | .tail _ member => Or.inr member

/-- The tail-recursive reverse accumulator is reverse followed by its suffix. -/
theorem list_reverseAux_eq_append
    {α : Type} :
    ∀ values suffix : List α,
      List.reverseAux values suffix =
        List.reverseAux values [] ++ suffix
  | [], _ => rfl
  | head :: tail, suffix =>
      calc
        List.reverseAux (head :: tail) suffix =
            List.reverseAux tail (head :: suffix) := rfl
        _ =
            List.reverseAux tail [] ++ (head :: suffix) :=
          list_reverseAux_eq_append tail (head :: suffix)
        _ =
            (List.reverseAux tail [] ++ [head]) ++ suffix :=
          (list_append_assoc
            (List.reverseAux tail [])
            [head]
            suffix).symm
        _ =
            List.reverseAux tail [head] ++ suffix :=
          congrArg
            (fun values => values ++ suffix)
            (list_reverseAux_eq_append tail [head]).symm
        _ =
            List.reverseAux (head :: tail) [] ++ suffix := rfl

/-- Reversing a cons appends the head after the reversed tail. -/
theorem list_reverse_cons
    {α : Type}
    (head : α)
    (tail : List α) :
    (head :: tail).reverse =
      tail.reverse ++ [head] := by
  exact
    list_reverseAux_eq_append
      tail
      [head]

/-- Boolean conjunction is true exactly when both inputs are true. -/
theorem bool_and_eq_true_iff :
    ∀ first second : Bool,
      (first && second) = true ↔
        first = true ∧ second = true
  | false, false =>
      ⟨fun impossible => False.elim (Bool.noConfusion impossible),
        fun equalities => False.elim (Bool.noConfusion equalities.1)⟩
  | false, true =>
      ⟨fun impossible => False.elim (Bool.noConfusion impossible),
        fun equalities => False.elim (Bool.noConfusion equalities.1)⟩
  | true, false =>
      ⟨fun impossible => False.elim (Bool.noConfusion impossible),
        fun equalities => False.elim (Bool.noConfusion equalities.2)⟩
  | true, true =>
      ⟨fun _ => ⟨rfl, rfl⟩,
        fun _ => rfl⟩

end Constructive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Constructive.nat_le_max_left
#print axioms ConstitutiveSearch.Constructive.nat_le_max_right
#print axioms ConstitutiveSearch.Constructive.nat_max_le
#print axioms ConstitutiveSearch.Constructive.nat_max_self
#print axioms ConstitutiveSearch.Constructive.nat_max_zero
#print axioms ConstitutiveSearch.Constructive.nat_double_add_two
#print axioms ConstitutiveSearch.Constructive.nat_add_pair_swap
#print axioms ConstitutiveSearch.Constructive.nat_mul_assoc
#print axioms ConstitutiveSearch.Constructive.nat_mul_pair_swap
#print axioms ConstitutiveSearch.Constructive.nat_add_mul
#print axioms ConstitutiveSearch.Constructive.nat_pow_add
#print axioms ConstitutiveSearch.Constructive.nat_pow_mul
#print axioms ConstitutiveSearch.Constructive.two_le_of_pos_of_ne_one
#print axioms ConstitutiveSearch.Constructive.nat_ne_add_one
#print axioms ConstitutiveSearch.Constructive.one_le_two_mul_succ
#print axioms ConstitutiveSearch.Constructive.natLog2
#print axioms ConstitutiveSearch.Constructive.two_pow_positive
#print axioms ConstitutiveSearch.Constructive.two_pow_strictly_grows
#print axioms ConstitutiveSearch.Constructive.exponent_le_of_two_pow_le
#print axioms ConstitutiveSearch.Constructive.two_pow_natLog2_le
#print axioms ConstitutiveSearch.Constructive.lt_two_pow_natLog2_succ
#print axioms ConstitutiveSearch.Constructive.natLog2_two_pow
#print axioms ConstitutiveSearch.Constructive.natLog2_mono
#print axioms ConstitutiveSearch.Constructive.list_append_assoc
#print axioms ConstitutiveSearch.Constructive.list_map_append
#print axioms ConstitutiveSearch.Constructive.list_map_map
#print axioms ConstitutiveSearch.Constructive.list_map_id
#print axioms ConstitutiveSearch.Constructive.list_length_replicate
#print axioms ConstitutiveSearch.Constructive.list_mem_cons_cases
#print axioms ConstitutiveSearch.Constructive.list_reverseAux_eq_append
#print axioms ConstitutiveSearch.Constructive.list_reverse_cons
#print axioms ConstitutiveSearch.Constructive.bool_and_eq_true_iff
/- AXIOM_AUDIT_END -/
