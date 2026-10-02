import Constitution.ConcreteInterpretation
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Typed regime-exit diagnostics

The exact concrete interpretation and the circular-refinement regime are kept
as distinct type families on the same rooted-history carrier. The perimetral
structures below compose the abstract diagnostic with the additional positive
witness explaining its geometric origin. -/

def ExactConcreteRealization
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (history : RootedGeneratedHistory P) : Type _ :=
  ExactHistoryInterpretation
    A history.history (A.realizeHistory history.history)

abbrev ConcreteRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ :=
  AbstractSegmentedTurning.RegimeExit
    (ExactConcreteRealization A) (CircularRefinement P)

structure PerimetralRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) where
  exit : ConcreteRegimeExit P A
  extendsPerimeter :
    StrictConstitutivePrefix (perimeterDeployment P) exit.candidate

namespace PerimetralRegimeExit

def toRegimeExit
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (exit : PerimetralRegimeExit P A) :
    ConcreteRegimeExit P A :=
  exit.exit

end PerimetralRegimeExit


abbrev UniformConcreteRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :=
  AbstractSegmentedTurning.UniformRegimeExit
    (Carrier := RootedGeneratedHistory P)
    (ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P)
    (fun (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P)
        (candidate : RootedGeneratedHistory P) =>
      ExactConcreteRealization A candidate)
    (CircularRefinement P)

structure UniformPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) where
  exit : UniformConcreteRegimeExit.{uE, uI, uK, uD, uP, uEnd, uLoop,
    vA, vB, vC, vF, vG, vH, vJ} P
  extendsPerimeter :
    StrictConstitutivePrefix (perimeterDeployment P) exit.candidate

namespace UniformPerimetralRegimeExit

def toUniformRegimeExit
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P) :
    UniformConcreteRegimeExit.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P :=
  exit.exit

def atImplementation
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    PerimetralRegimeExit P A :=
  { exit :=
      { candidate := exit.exit.candidate
        faithful := exit.exit.faithful A
        inadmissible := exit.exit.inadmissible }
    extendsPerimeter := exit.extendsPerimeter }

@[simp] theorem at_forget
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    { candidate := exit.exit.candidate
      faithful := exit.exit.faithful A
      inadmissible := exit.exit.inadmissible } =
      (atImplementation exit A).toRegimeExit := by
  rfl

@[simp] theorem at_forget_named
    {P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}}
    (exit : UniformPerimetralRegimeExit P)
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    AbstractSegmentedTurning.UniformRegimeExit.atImplementation
        (toUniformRegimeExit exit) A =
      PerimetralRegimeExit.toRegimeExit
        (atImplementation exit A) := by
  rfl

end UniformPerimetralRegimeExit

def oneStepUniformPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :
    UniformPerimetralRegimeExit P :=
  { exit :=
      { candidate := oneStepAfterPerimeter P
        faithful := fun A =>
          exactlyInterpretHistory A (oneStepAfterPerimeter P).history
        inadmissible := oneStepAfterPerimeter_notCircularRefinement P }
    extendsPerimeter := oneStepAfterPerimeterStrict P }

def oneStepPerimetralRegimeExit
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop})
    (A : ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
      vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P) :
    PerimetralRegimeExit P A :=
  UniformPerimetralRegimeExit.atImplementation
    (oneStepUniformPerimetralRegimeExit P) A

def oneStepConcreteRegimeExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ConcreteRegimeExit P A :=
  (oneStepPerimetralRegimeExit P A).toRegimeExit

/- A history-level alignment specification is a type-valued predicate on rooted
   generated histories.  This remains independent of any particular regime. -/
abbrev HistoryAlignmentSpec
    (P : CircularPresentation) :=
  RootedGeneratedHistory P → Type _

/- The first concrete normative-adequacy instance keeps the occurrence index
   required by the generic interface, while adequacy itself is global and
   constant along occurrences: regime membership and specification satisfaction
   imply each other on the same rooted-history carrier. -/
def circularNormativeAdequacy
    (P : CircularPresentation) :
    NormativeAdequacy P where
  AlignmentSpec := HistoryAlignmentSpec P
  RegimeAdequateAtOccurrence :=
    fun S R H _occurrence =>
      (R H → S H) × (S H → R H)

/- Soundness and regime completeness provide adequacy at every occurrence of
   the same history.  No occurrence projection is introduced. -/
def circularRefinement_adequateAlong
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) :
    AdequateAlong
      (circularNormativeAdequacy P)
      (CircularSpecificationSatisfaction P)
      (CircularRefinement P)
      history :=
  fun _occurrence =>
    ⟨circularRefinement_soundSpecification,
      circularSpecification_complete⟩

/- The canonical one-step regime exit becomes specification-relative by pairing
   the existing faithful concrete realization and regime rejection with the
   already established adequacy of the circular regime to the independent
   specification. -/
def oneStepSpecRelativeHistoryExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    SpecRelativeHistoryExit
      (circularNormativeAdequacy P)
      (CircularSpecificationSatisfaction P)
      (CircularRefinement P)
      (ExactConcreteRealization A) :=
  { exit := oneStepConcreteRegimeExit P A
    adequacy :=
      circularRefinement_adequateAlong P (oneStepAfterPerimeter P) }

/- The semantic failure of the candidate remains independent of the regime-exit
   rejection.  It is inherited directly from the autonomous specification. -/
theorem oneStepSpecRelativeHistoryExit_notSpecification
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    CircularSpecificationSatisfaction P
      (oneStepSpecRelativeHistoryExit P A).exit.candidate → False := by
  change
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False
  exact oneStepAfterPerimeter_notSpecificationSatisfaction P

inductive ConcreteFaithfulPartialPath
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    (remaining : PerimeterSpine P.Compatible node) →
    (data : FreeConstitution P (.within remaining)) →
    (difference : BoundaryDifference P data) →
    (history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))) →
    Type _
  | root :
      ConcreteFaithfulPartialPath P A P.perimeter
        FreeConstitution.root BoundaryDifference.initial
        (.root : History A.ConcreteStep
          (A.stateAt (initialPositive P)) (A.stateAt (initialPositive P)))
  | advance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {data : FreeConstitution P (.within (.advance compatible tail))}
      {difference : BoundaryDifference P data}
      {history : History A.ConcreteStep
        (A.stateAt (initialPositive P))
        (A.stateAt
          (positiveAtRemaining P (.advance compatible tail) data difference))} :
      ConcreteFaithfulPartialPath P A
        (.advance compatible tail) data difference history →
      ConcreteFaithfulPartialPath P A tail
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.1
        (canonicalTarget
          (positiveAtRemaining P (.advance compatible tail) data difference)).2.2
        (.extend history
          (A.concreteStep
            (positiveAtRemaining P (.advance compatible tail) data difference)))

structure ReconstructedFaithfulPartialPath
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (remaining : PerimeterSpine P.Compatible node)
    (data : FreeConstitution P (.within remaining))
    (difference : BoundaryDifference P data)
    (history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))) where
  freeHistory : GeneratedHistory (initialPositive P)
    (positiveAtRemaining P remaining data difference)
  freePartialPath : FreePartialPath P remaining data difference freeHistory
  historyExact : A.realizeHistory freeHistory = history

namespace ConcreteFaithfulPartialPath

def reconstruct
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {remaining : PerimeterSpine P.Compatible node}
    {data : FreeConstitution P (.within remaining)}
    {difference : BoundaryDifference P data}
    {history : History A.ConcreteStep
      (A.stateAt (initialPositive P))
      (A.stateAt (positiveAtRemaining P remaining data difference))} :
    ConcreteFaithfulPartialPath P A remaining data difference history →
      ReconstructedFaithfulPartialPath P A
        remaining data difference history
  | .root =>
      { freeHistory := .root
        freePartialPath := .root
        historyExact := rfl }
  | @advance _ _ node nextNode compatible tail data difference history previous =>
      let prior := reconstruct previous
      { freeHistory := .extend prior.freeHistory
          (generatedStepOfFreeK
            (positiveAtRemaining P (.advance compatible tail) data difference))
        freePartialPath := .advance prior.freePartialPath
        historyExact := by
          change History.extend
            (A.realizeHistory prior.freeHistory) (A.concreteStep _) =
            History.extend history (A.concreteStep _)
          rw [prior.historyExact] }

end ConcreteFaithfulPartialPath

structure ConcreteFaithfulPartialRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) where
  node : LocalNode
    P.Explicit P.Implicit P.Compatible P.Difference P.Provenance
  remaining : PerimeterSpine P.Compatible node
  data : FreeConstitution P (.within remaining)
  difference : BoundaryDifference P data
  concreteHistory : History A.ConcreteStep
    (A.stateAt (initialPositive P))
    (A.stateAt (positiveAtRemaining P remaining data difference))
  derivation : ConcreteFaithfulPartialPath P A
    remaining data difference concreteHistory

structure FaithfulPartialInterpretation
    {P : CircularPresentation}
    (A : ConcreteContinuationAlgebra P)
    (concrete : ConcreteFaithfulPartialRealization P A) where
  history : RootedGeneratedHistory P
  freePartial : FreePartialRealization P history
  interpretedHistory : History A.ConcreteStep
    (A.stateAt (initialPositive P)) (A.stateAt history.endpoint)
  concreteHistoryExact : HEq interpretedHistory concrete.concreteHistory
  interpretation : ExactHistoryInterpretation A
    history.history interpretedHistory

def interpretEveryFaithfulPartialRealization
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (concrete : ConcreteFaithfulPartialRealization P A) :
    FaithfulPartialInterpretation A concrete := by
  let reconstructed := concrete.derivation.reconstruct
  let freeHistory := reconstructed.freeHistory
  let rooted : RootedGeneratedHistory P :=
    ⟨positiveAtRemaining P concrete.remaining concrete.data concrete.difference,
      freeHistory⟩
  exact
    { history := rooted
      freePartial := .ofPath reconstructed.freePartialPath
      interpretedHistory := A.realizeHistory freeHistory
      concreteHistoryExact := heq_of_eq reconstructed.historyExact
      interpretation := exactlyInterpretHistory A freeHistory }


end StrongPerimetralTurning
