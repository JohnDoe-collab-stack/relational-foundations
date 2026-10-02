import RelationalFoundations
set_option genInjectivity false

namespace RelationalFoundations.Separators

def trivialRealization : ExactRealization Bool Bool (fun _ _ => Unit) :=
  ⟨.reflexive _, fun _ => ()⟩

theorem distinguished_exact_not_rigid : ¬ trivialRealization.RoleRigid := by
  intro rigid
  have impossible := rigid false true ()
  cases impossible

def falseBoundary : ClosingBoundary Bool Unit (fun _ _ => Unit) := ⟨false, ()⟩
def trueBoundary : ClosingBoundary Bool Unit (fun _ _ => Unit) := ⟨true, ()⟩

def uniformFinalTransport : ExactTransport (BoundaryFinalRole falseBoundary) (BoundaryFinalRole trueBoundary) :=
  (BoundaryFinalRole.unitTransport falseBoundary).compose (BoundaryFinalRole.unitTransport trueBoundary).reverse

theorem boundaries_distinct : falseBoundary ≠ trueBoundary := by
  intro eq
  have impossible := congrArg ClosingBoundary.terminal eq
  cases impossible

def swapWitness : ExactTransport Bool Bool :=
  ⟨Bool.not, Bool.not, fun b => by cases b <;> rfl, fun b => by cases b <;> rfl⟩

theorem fiber_transport_not_pointed : swapWitness.forward false ≠ false := by
  intro eq
  cases eq

def branchSwap : ExactTransport (Unit ⊕ Unit) (Unit ⊕ Unit) where
  forward := fun x => match x with | .inl u => .inr u | .inr u => .inl u
  backward := fun x => match x with | .inl u => .inr u | .inr u => .inl u
  forwardBackward := fun x => by cases x <;> rfl
  backwardForward := fun x => by cases x <;> rfl

theorem branches_not_preserved : branchSwap.forward (.inl ()) ≠ .inl () := by
  intro eq
  cases eq

def uninhabitedBoundary : ClosingBoundary Unit Unit (fun _ _ => Empty) := ⟨(), ()⟩
theorem boundary_not_positive :
    (fun _ _ => Empty) uninhabitedBoundary.terminal uninhabitedBoundary.initial → False :=
  fun impossible => nomatch impossible

def loopHistory : History (fun (_ _ : Unit) => Unit) () () := .extend .root ()
def loopPositive : History.Positive (fun (_ _ : Unit) => Unit) () () := ⟨(), .root, ()⟩

theorem loop_has_distinct_vertices : History.initialVertex loopHistory ≠ History.finalVertex loopHistory :=
  History.positive_vertices_distinct loopPositive

open Perimetral

def firstRole : presentation.InternalRole := .here
def secondRole : presentation.InternalRole := .later .here
def thirdRole : presentation.InternalRole := .later (.later .here)

theorem first_second_distinct : firstRole ≠ secondRole := by
  intro eq
  cases eq

theorem constant_readout_not_injective :
    ¬ Function.Injective (fun _ : presentation.InteriorOccurrence => ()) := by
  intro faithful
  have eq := faithful (a₁ := Spine.realize firstRole) (a₂ := Spine.realize secondRole) rfl
  exact first_second_distinct (presentation.interiorRealization.forward_injective eq)

theorem source_target_not_witness_identity :
    (Compatible.licensed true : Next .first .second) ≠ Compatible.licensed false :=
  license_witnesses_distinct

theorem two_new_occurrences_rejected
    (core : Residual.ResidualDeterminationCore Unit Unit Bool ⟨(), fun x => by cases x; rfl⟩) : False := by
  have impossible := core.occurrences_unique false true
  cases impossible

def twoStepHistory : History Next .fourth (.free 1) :=
  .extend (.extend .root (.licensed false : Next .fourth (.free 0))) (.licensed true)

theorem twoStep_new_occurrences_distinct :
    (History.Occurrence.last : History.Occurrence twoStepHistory) ≠ .earlier .last := by
  intro eq
  cases eq

theorem generation_survives_regime_exit :
    (iterate 5).history.length = 8 ∧ (regime.Admission (iterate 5) → False) :=
  ⟨iterate_length 5, iterate_outside_regime 4⟩

theorem current_and_old_records_distinct :
    (Formation.Record.current : Formation.Record continuation.formation) ≠
      .preserved (Formation.Record.current : Formation.Record (Formation.deployed presentation.spine)) :=
  Formation.current_ne_preserved _ _ _

theorem concrete_occurrences_exact :
    (o : presentation.InteriorOccurrence) →
      (forgetting.occurrenceTransport presentation.interiorHistory).backward
        ((forgetting.occurrenceTransport presentation.interiorHistory).forward o) = o :=
  (forgetting.occurrenceTransport presentation.interiorHistory).forwardBackward

inductive TraceOccurrence
  | first | second | third | gap

def permutedRealize : presentation.InternalRole → TraceOccurrence
  | .here => .second
  | .later .here => .first
  | .later (.later .here) => .third

def permutedLocated : TraceOccurrence → History.LocatedStep Next
  | .first => Spine.located secondRole
  | .second => Spine.located firstRole
  | .third => Spine.located thirdRole
  | .gap => ⟨.fourth, .free 0, .licensed false⟩

theorem permuted_local_exact (r : presentation.InternalRole) :
    permutedLocated (permutedRealize r) = Spine.located r := by
  cases r with
  | here => rfl
  | later r => cases r with
    | here => rfl
    | later r => cases r with
      | here => rfl
      | later impossible => cases impossible

def permutedRank : TraceOccurrence → Nat
  | .first => 0
  | .second => 1
  | .third => 2
  | .gap => 3

theorem permuted_order_fails :
    ¬ permutedRank (permutedRealize firstRole) < permutedRank (permutedRealize secondRole) :=
  Nat.not_lt_zero _

def intercalatedRealize : presentation.InternalRole → TraceOccurrence
  | .here => .first
  | .later .here => .second
  | .later (.later .here) => .third

def intercalatedLocated : TraceOccurrence → History.LocatedStep Next
  | .first => Spine.located firstRole
  | .second => Spine.located secondRole
  | .third => Spine.located thirdRole
  | .gap => ⟨.fourth, .free 0, .licensed false⟩

theorem intercalated_local_exact (r : presentation.InternalRole) :
    intercalatedLocated (intercalatedRealize r) = Spine.located r := by
  cases r with
  | here => rfl
  | later r => cases r with
    | here => rfl
    | later r => cases r with
      | here => rfl
      | later impossible => cases impossible

def intercalatedRank : TraceOccurrence → Nat
  | .first => 0
  | .second => 2
  | .third => 3
  | .gap => 1

theorem intercalated_preserves_first_order :
    intercalatedRank (intercalatedRealize firstRole) < intercalatedRank (intercalatedRealize secondRole) := by
  exact Nat.zero_lt_succ 1

theorem intercalated_fails_adjacency :
    intercalatedRank (intercalatedRealize firstRole) + 1 ≠ intercalatedRank (intercalatedRealize secondRole) := by
  intro eq
  have zeroEq : 0 = 1 := Nat.succ.inj eq
  exact Nat.noConfusion zeroEq

def permutedDecode : TraceOccurrence → presentation.InternalRole
  | .first => secondRole
  | .second => firstRole
  | .third => thirdRole
  | .gap => firstRole

theorem permuted_return (role : presentation.InternalRole) : permutedDecode (permutedRealize role) = role := by
  cases role with
  | here => rfl
  | later role => cases role with
    | here => rfl
    | later role => cases role with
      | here => rfl
      | later impossible => cases impossible

theorem permuted_injective : Function.Injective permutedRealize := by
  intro first second eq
  exact (permuted_return first).symm.trans ((congrArg permutedDecode eq).trans (permuted_return second))

def intercalatedDecode : TraceOccurrence → presentation.InternalRole
  | .first => firstRole
  | .second => secondRole
  | .third => thirdRole
  | .gap => firstRole

theorem intercalated_return (role : presentation.InternalRole) : intercalatedDecode (intercalatedRealize role) = role := by
  cases role with
  | here => rfl
  | later role => cases role with
    | here => rfl
    | later role => cases role with
      | here => rfl
      | later impossible => cases impossible

theorem intercalated_injective : Function.Injective intercalatedRealize := by
  intro first second eq
  exact (intercalated_return first).symm.trans ((congrArg intercalatedDecode eq).trans (intercalated_return second))

theorem intercalated_preserves_all_order {first second : presentation.InternalRole}
    (before : Spine.Precedes first second) :
    intercalatedRank (intercalatedRealize first) < intercalatedRank (intercalatedRealize second) := by
  cases before with
  | here_later later => cases later with
    | here => exact Nat.zero_lt_succ 1
    | later later => cases later with
      | here => exact Nat.zero_lt_succ 2
      | later impossible => cases impossible
  | later_later before => cases before with
    | here_later later => cases later with
      | here => exact Nat.lt_succ_self 2
      | later impossible => cases impossible
    | later_later impossible => cases impossible with
      | here_later position => cases position
      | later_later before => cases before

end RelationalFoundations.Separators
