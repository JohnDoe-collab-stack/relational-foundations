import RelationalFoundations.Cardinalization
import RelationalFoundations.Quantity
set_option genInjectivity false

namespace RelationalFoundations
namespace FiniteInvariance
universe u v w

def swap {A : Type u} [DecidableEq A] (a b x : A) : A :=
  if x = a then b else if x = b then a else x

theorem swap_first {A : Type u} [DecidableEq A] (a b : A) : swap a b a = b := by
  unfold swap
  rw [if_pos rfl]

theorem swap_second {A : Type u} [DecidableEq A] (a b : A) : swap a b b = a := by
  unfold swap
  by_cases eq : b = a
  · rw [if_pos eq]
    exact eq
  · rw [if_neg eq, if_pos rfl]

theorem swap_roundTrip {A : Type u} [DecidableEq A] (a b x : A) : swap a b (swap a b x) = x := by
  by_cases first : x = a
  · cases first
    rw [swap_first, swap_second]
  · by_cases second : x = b
    · cases second
      rw [swap_second, swap_first]
    · have unchanged : swap a b x = x := by
        unfold swap
        rw [if_neg first, if_neg second]
      rw [unchanged, unchanged]

theorem swap_injective {A : Type u} [DecidableEq A] (a b : A) : Function.Injective (swap a b) := by
  intro x y eq
  exact (swap_roundTrip a b x).symm.trans ((congrArg (swap a b) eq).trans (swap_roundTrip a b y))

def zero (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

def predecessor {n : Nat} (x : Fin (n + 1)) (nonzero : x ≠ zero n) : Fin n := by
  rcases x with ⟨value, bound⟩
  cases value with
  | zero => exact False.elim (nonzero rfl)
  | succ value => exact ⟨value, Nat.lt_of_succ_lt_succ bound⟩

theorem successor_predecessor {n : Nat} (x : Fin (n + 1)) (nonzero : x ≠ zero n) :
    (predecessor x nonzero).succ = x := by
  rcases x with ⟨value, bound⟩
  cases value with
  | zero => exact False.elim (nonzero rfl)
  | succ value => rfl

theorem succ_injective {n : Nat} : Function.Injective (@Fin.succ n) := by
  intro x y eq
  exact Fin.ext (Nat.succ.inj (congrArg Fin.val eq))

theorem injection_bound {n m : Nat} (f : Fin n → Fin m) (faithful : Function.Injective f) : n ≤ m := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact Nat.le_refl 0
    | succ n => exact Fin.elim0 (f (zero n))
  | succ m ih =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      let g : Fin (n + 1) → Fin (m + 1) := fun x => swap (zero m) (f (zero n)) (f x)
      have gFaithful : Function.Injective g := fun _ _ eq => faithful (swap_injective (zero m) (f (zero n)) eq)
      have gZero : g (zero n) = zero m := swap_second (zero m) (f (zero n))
      have gSuccNonzero : ∀ x : Fin n, g x.succ ≠ zero m := by
        intro x eq
        have impossible := gFaithful (eq.trans gZero.symm)
        have values : Nat.succ x.val = 0 := congrArg Fin.val impossible
        exact Nat.noConfusion values
      let smaller : Fin n → Fin m := fun x => predecessor (g x.succ) (gSuccNonzero x)
      have smallerFaithful : Function.Injective smaller := by
        intro x y eq
        have images : g x.succ = g y.succ :=
          (successor_predecessor _ (gSuccNonzero x)).symm.trans
            ((congrArg Fin.succ eq).trans (successor_predecessor _ (gSuccNonzero y)))
        exact succ_injective (gFaithful images)
      exact Nat.succ_le_succ (ih smaller smallerFaithful)

theorem cardinal_eq {n m : Nat} (f : ExactTransport (Fin n) (Fin m)) : n = m := by
  apply Nat.le_antisymm
  · exact injection_bound f.forward (fun x y eq =>
      (f.forwardBackward x).symm.trans ((congrArg f.backward eq).trans (f.forwardBackward y)))
  · exact injection_bound f.backward (fun x y eq =>
      (f.backwardForward x).symm.trans ((congrArg f.forward eq).trans (f.backwardForward y)))

theorem quantity_cardinal_eq {q₁ q₂ : StructuralQuantity.{u,v,w}} {n m : Nat}
    (f : ConstitutiveEquiv q₁ q₂) (first : ExactTransport q₁.Occurrence (Fin n))
    (second : ExactTransport q₂.Occurrence (Fin m)) : n = m :=
  cardinal_eq ((first.reverse.compose f.occurrences).compose second)

theorem history_cardinal_eq {State : Type u} {Step : State → State → Type v}
    {a b c d : State} (first : History Step a b) (second : History Step c d)
    (f : ExactTransport (History.Occurrence first) (History.Occurrence second)) : first.length = second.length :=
  cardinal_eq (((first.cardinalTransport).reverse.compose f).compose second.cardinalTransport)
end FiniteInvariance
end RelationalFoundations
