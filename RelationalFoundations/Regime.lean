import RelationalFoundations.History
set_option genInjectivity false

namespace RelationalFoundations
universe u v g a e

structure RootedConstruction {State : Type u} (Step : State → State → Type v) (root : State) where
  endpoint : State
  history : History Step root endpoint

structure StrictExtension {State : Type u} {Step : State → State → Type v} {root : State}
    (old candidate : RootedConstruction Step root) where
  continuation : History.Positive Step old.endpoint candidate.endpoint
  recompose : History.append old.history continuation.toHistory = candidate.history
  different : candidate ≠ old

structure ExactRegime {Carrier : Type u} (canonical : Carrier) where
  Admission : Carrier → Type g
  canonicalAdmission : Admission canonical
  classify : ∀ candidate, Admission candidate → candidate = canonical

namespace ExactRegime
variable {Carrier : Type u} {canonical : Carrier}

def complete (regime : ExactRegime canonical) (candidate : Carrier)
    (eq : candidate = canonical) : regime.Admission candidate :=
  eq.symm ▸ regime.canonicalAdmission

theorem rejects (regime : ExactRegime canonical) {candidate : Carrier}
    (different : candidate ≠ canonical) : regime.Admission candidate → False :=
  fun admission => different (regime.classify candidate admission)

def canonicalOnly (canonical : Carrier) : ExactRegime canonical where
  Admission := fun candidate => PLift (candidate = canonical)
  canonicalAdmission := ⟨rfl⟩
  classify := fun _ witness => witness.down

end ExactRegime

set_option linter.checkUnivs false in
/-- Analysis and obstruction are distinct inputs; circularity supplies neither automatically. -/
structure ObstructedRegime {Carrier : Type u} (canonical : Carrier) where
  Admission : Carrier → Type g
  Attempt : Carrier → Type a
  canonicalAdmission : Admission canonical
  analyze : ∀ candidate, Admission candidate → PLift (candidate = canonical) ⊕ Attempt candidate
  reject : ∀ candidate, Attempt candidate → False

def ObstructedRegime.exact {Carrier : Type u} {canonical : Carrier}
    (regime : ObstructedRegime canonical) : ExactRegime canonical where
  Admission := regime.Admission
  canonicalAdmission := regime.canonicalAdmission
  classify := fun candidate witness =>
    match regime.analyze candidate witness with
    | .inl eq => eq.down
    | .inr attempt => False.elim (regime.reject candidate attempt)

structure PoleObstruction where
  Pole : Type e
  left : Pole
  right : Pole
  rejectsIdentification : left = right → False

structure BilateralTotalization (obstruction : PoleObstruction.{e}) : Type e where
  identified : obstruction.left = obstruction.right

theorem PoleObstruction.rejectTotalization (o : PoleObstruction.{e}) :
    BilateralTotalization o → False := fun attempt => o.rejectsIdentification attempt.identified

end RelationalFoundations
