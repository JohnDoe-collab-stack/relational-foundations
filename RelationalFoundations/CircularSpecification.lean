import RelationalFoundations.Cardinalization
import RelationalFoundations.NormativeAdequacy
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c g e

/-- Local constitution is an actual canonical extension, with its actual witnesses. -/
structure ConstitutivePrefix {State : Type u} {Step : State → State → Type v} {root : State}
    (old candidate : RootedConstruction Step root) where
  continuation : History Step old.endpoint candidate.endpoint
  recompose : History.append old.history continuation = candidate.history

namespace ConstitutivePrefix
variable {State : Type u} {Step : State → State → Type v} {root : State}
variable {old candidate : RootedConstruction Step root}

def identity (old : RootedConstruction Step root) : ConstitutivePrefix old old := ⟨.root, rfl⟩

theorem positive_different (extension : ConstitutivePrefix old candidate)
    (positive : History.Positive Step old.endpoint candidate.endpoint)
    (positiveExact : extension.continuation = positive.toHistory) : candidate ≠ old := by
  intro eq
  have lengths := congrArg (fun value : RootedConstruction Step root => value.history.length) eq
  have recomposed := congrArg History.length extension.recompose
  rw [History.length_append, positiveExact] at recomposed
  have cancelled : old.history.length + positive.toHistory.length = old.history.length :=
    recomposed.trans lengths
  cases positive with
  | mk predecessor history witness =>
    change old.history.length + (history.length + 1) = old.history.length at cancelled
    have positiveLength : old.history.length < old.history.length + (history.length + 1) :=
      Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    exact Nat.ne_of_gt positiveLength cancelled

def asStrict (extension : ConstitutivePrefix old candidate)
    (positive : History.Positive Step old.endpoint candidate.endpoint)
    (positiveExact : extension.continuation = positive.toHistory) : StrictExtension old candidate :=
  ⟨positive, (congrArg (History.append old.history) positiveExact.symm).trans extension.recompose,
    extension.positive_different positive positiveExact⟩
end ConstitutivePrefix

/-- Closure is an independent obligation on strict extensions, with no admission field. -/
abbrev CircularClosureMeaning (p : CircularPresentation.{u,v,t,i,c})
    (obstruction : PoleObstruction.{e}) (candidate : RootedConstruction p.Next p.start) :=
  StrictExtension p.interiorConstruction candidate → BilateralTotalization obstruction

structure CircularSpecificationSatisfaction (p : CircularPresentation.{u,v,t,i,c})
    (obstruction : PoleObstruction.{e}) (candidate : RootedConstruction p.Next p.start) where
  localConstitution : ConstitutivePrefix p.interiorConstruction candidate
  trajectory : CircularClosureMeaning p obstruction candidate

namespace CircularSpecificationSatisfaction
variable {p : CircularPresentation.{u,v,t,i,c}} {obstruction : PoleObstruction.{e}}

def canonical (p : CircularPresentation.{u,v,t,i,c}) (obstruction : PoleObstruction.{e}) :
    CircularSpecificationSatisfaction p obstruction p.interiorConstruction :=
  ⟨.identity _, fun strict => False.elim (strict.different rfl)⟩

theorem classify {candidate : RootedConstruction p.Next p.start}
    (satisfaction : CircularSpecificationSatisfaction p obstruction candidate) :
    candidate = p.interiorConstruction := by
  rcases candidate with ⟨endpoint, history⟩
  rcases satisfaction.localConstitution with ⟨suffix, recompose⟩
  cases suffix with
  | root =>
    change p.interiorHistory = history at recompose
    cases recompose
    rfl
  | extend previous witness =>
    let extension : ConstitutivePrefix p.interiorConstruction ⟨endpoint, history⟩ :=
      ⟨.extend previous witness, recompose⟩
    exact False.elim (obstruction.rejectTotalization
      (satisfaction.trajectory (extension.asStrict ⟨_, previous, witness⟩ rfl)))

def sound {candidate : RootedConstruction p.Next p.start}
    (regime : ExactRegime.{max u v,g} p.interiorConstruction)
    (satisfaction : CircularSpecificationSatisfaction p obstruction candidate) : regime.Admission candidate :=
  regime.complete candidate satisfaction.classify

def complete {candidate : RootedConstruction p.Next p.start}
    (regime : ExactRegime.{max u v,g} p.interiorConstruction) (admission : regime.Admission candidate) :
    CircularSpecificationSatisfaction p obstruction candidate :=
  (regime.classify candidate admission).symm ▸ canonical p obstruction

theorem rejectsStrict {candidate : RootedConstruction p.Next p.start}
    (strict : StrictExtension p.interiorConstruction candidate) :
    CircularSpecificationSatisfaction p obstruction candidate → False :=
  fun satisfaction => obstruction.rejectTotalization (satisfaction.trajectory strict)

def adequacy (p : CircularPresentation.{u,v,t,i,c}) (obstruction : PoleObstruction.{e})
    (regime : ExactRegime.{max u v,g} p.interiorConstruction) :
    NormativeAdequacy (fun candidate => History.Occurrence candidate.history)
      (CircularSpecificationSatisfaction p obstruction) regime.Admission :=
  globalNormativeAdequacy _ _ _ (fun _ => sound regime) (fun _ => complete regime)
end CircularSpecificationSatisfaction
end RelationalFoundations
