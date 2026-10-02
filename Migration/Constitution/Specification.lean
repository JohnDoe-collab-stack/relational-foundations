import Constitution.FinalInterpretation
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Independent circular specification -/

/- `CircularClosureMeaning` states the trajectory-level closure obligation
   independently of `CircularRefinement`: every strict constitutive extension
   of the canonical perimeter deployment must determine a total loop. -/
abbrev CircularClosureMeaning
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  StrictConstitutivePrefix (perimeterDeployment P) history → P.TotalLoop

/- The canonical deployment satisfies the closure meaning because there is no
   strict constitutive prefix from it to itself. -/
def perimeterDeployment_closureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (perimeterDeployment P) :=
  fun strict =>
    False.elim (strictPrefix_ne strict rfl)

/- The freely generated one-step continuation fails the independent closure
   meaning directly: its canonical strict continuation would force a total
   loop, which the presentation rejects. -/
theorem oneStepAfterPerimeter_notClosureMeaning
    (P : CircularPresentation) :
    CircularClosureMeaning P (oneStepAfterPerimeter P) → False :=
  fun meaning =>
    P.rejectTotalLoop (meaning (oneStepAfterPerimeterStrict P))

/- Satisfaction of the independent circular specification has exactly two
   primitive components: minimal local exactness and trajectory closure. -/
structure CircularSpecificationSatisfaction
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  «local» : ExactNonClosingRealization P history
  trajectory : CircularClosureMeaning P history

/- Positive canonical model of the independent specification. -/
def perimeterDeployment_specificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (perimeterDeployment P) :=
  { «local» := (identityPerimeterExtension P).toExactNonClosingRealization
    trajectory := perimeterDeployment_closureMeaning P }

/- Negative canonical model: local exactness remains available, but the
   trajectory component of the same independent specification is impossible. -/
theorem oneStepAfterPerimeter_notSpecificationSatisfaction
    (P : CircularPresentation) :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False :=
  fun satisfaction =>
    oneStepAfterPerimeter_notClosureMeaning P satisfaction.trajectory

/- Carrier completeness of the independent specification: any satisfying rooted
   generated history is necessarily the canonical perimeter deployment.  The
   local component reconstructs a perimeter extension.  A positive suffix is
   excluded directly by the independent trajectory meaning and the total-loop
   obstruction. -/
theorem CircularSpecificationSatisfaction.eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    history = perimeterDeployment P := by
  let extension : PerimeterExtension P history :=
    satisfaction.«local».toPerimeterExtension
  cases History.appendRootOrPositive
      (perimeterHistory P) extension.continuation with
  | inl rootData =>
      rcases rootData with ⟨endpointEquality, continuationEquality⟩
      exact rootedGeneratedHistory_ext endpointEquality.down
        ((heq_of_eq extension.recompose.symm).trans
          continuationEquality.down)
  | inr positiveData =>
      rcases positiveData with ⟨positive, continuationEquality⟩
      let strict :
          StrictConstitutivePrefix (perimeterDeployment P) history :=
        { continuation := positive
          historyExact := by
            exact
              (congrArg
                (History.append (perimeterHistory P))
                continuationEquality.down.symm).trans extension.recompose }
      exact False.elim
        (P.rejectTotalLoop (satisfaction.trajectory strict))


end StrongPerimetralTurning
