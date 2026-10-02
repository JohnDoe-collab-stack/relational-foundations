import SegmentedResidualRole
import Constitution.HistoryAPI
import AbstractSegmentedTurning
import ExactTypeTransport

/- The proposition-valued definitions below are intentionally transparent,
   and the independent input families intentionally keep distinct universes. -/
set_option linter.defProp false
set_option linter.checkUnivs false


set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Positive circular presentation -/

structure LocalNode
    (Explicit : Type uE)
    (Implicit : Type uI)
    (Compatible : Implicit → Explicit → Type uK)
    (Difference : Type uD)
    (Provenance : Difference → Type uP) where
  explicit : Explicit
  implicit : Implicit
  difference : Difference
  provenance : Provenance difference
  internallyCompatible : Compatible implicit explicit

inductive PerimeterSpine
    {Explicit : Type uE}
    {Implicit : Type uI}
    (Compatible : Implicit → Explicit → Type uK)
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    LocalNode Explicit Implicit Compatible Difference Provenance → Type _
  | boundary
      (node : LocalNode Explicit Implicit Compatible Difference Provenance) :
      PerimeterSpine Compatible node
  | advance
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      (nextCompatible : Compatible node.implicit nextNode.explicit)
      (tail : PerimeterSpine Compatible nextNode) :
      PerimeterSpine Compatible node

namespace PerimeterSpine

def startNode
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    (_ : PerimeterSpine Compatible node) :
    LocalNode Explicit Implicit Compatible Difference Provenance :=
  node

def finalNode
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} :
    PerimeterSpine Compatible node →
      LocalNode Explicit Implicit Compatible Difference Provenance
  | .boundary node => node
  | .advance _ tail => finalNode tail

end PerimeterSpine

inductive NonClosingPosition
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    PerimeterSpine Compatible node → Type _
  | here
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode} :
      NonClosingPosition (.advance nextCompatible tail)
  | later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode} :
      NonClosingPosition tail →
      NonClosingPosition (.advance nextCompatible tail)

/- Structural precedence between non-closing positions.  The relation carries
   only order information: no rank, distance, contiguity, or realization data
   is encoded here. -/
theorem NonClosingPosition.later.inj
    {Explicit : Type uE} {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK} {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node nextNode : LocalNode Explicit Implicit Compatible Difference Provenance}
    {nextCompatible : Compatible node.implicit nextNode.explicit}
    {tail : PerimeterSpine Compatible nextNode} {first second : NonClosingPosition tail}
    (eq : NonClosingPosition.later (nextCompatible := nextCompatible) first = .later second) : first = second := by
  cases eq
  rfl

inductive NonClosingPrecedes
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    (remaining : PerimeterSpine Compatible node) →
    NonClosingPosition remaining →
    NonClosingPosition remaining →
    Prop
  | here_later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      (position : NonClosingPosition tail) :
      NonClosingPrecedes
        (.advance nextCompatible tail)
        .here
        (.later position)
  | later_later
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      {first second : NonClosingPosition tail} :
      NonClosingPrecedes tail first second →
      NonClosingPrecedes
        (.advance nextCompatible tail)
        (.later first)
        (.later second)


/- Immediate structural adjacency between non-closing positions.  Unlike
   `NonClosingPrecedes`, this relation is not transitive: it records exactly
   one canonical successor step in the perimeter spine. -/
inductive NonClosingNext
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP} :
    {node : LocalNode Explicit Implicit Compatible Difference Provenance} →
    (remaining : PerimeterSpine Compatible node) →
    NonClosingPosition remaining →
    NonClosingPosition remaining →
    Prop
  | here_next
      {node nextNode thirdNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {firstCompatible : Compatible node.implicit nextNode.explicit}
      {secondCompatible : Compatible nextNode.implicit thirdNode.explicit}
      {tail : PerimeterSpine Compatible thirdNode} :
      NonClosingNext
        (.advance firstCompatible (.advance secondCompatible tail))
        .here
        (.later .here)
  | later_next
      {node nextNode :
        LocalNode Explicit Implicit Compatible Difference Provenance}
      {nextCompatible : Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine Compatible nextNode}
      {first second : NonClosingPosition tail} :
      NonClosingNext tail first second →
      NonClosingNext
        (.advance nextCompatible tail)
        (.later first)
        (.later second)

namespace NonClosingPrecedes

theorem ne
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    {remaining : PerimeterSpine Compatible node}
    {first second : NonClosingPosition remaining}
    (precedes : NonClosingPrecedes remaining first second) : first ≠ second := by
  induction precedes with
  | here_later _ =>
      intro equality
      cases equality
  | later_later _ inductionHypothesis =>
      intro equality
      exact inductionHypothesis (NonClosingPosition.later.inj equality)

end NonClosingPrecedes

namespace NonClosingNext

theorem toPrecedes
    {Explicit : Type uE}
    {Implicit : Type uI}
    {Compatible : Implicit → Explicit → Type uK}
    {Difference : Type uD}
    {Provenance : Difference → Type uP}
    {node : LocalNode Explicit Implicit Compatible Difference Provenance}
    {remaining : PerimeterSpine Compatible node}
    {first second : NonClosingPosition remaining}
    (next : NonClosingNext remaining first second) :
    NonClosingPrecedes remaining first second := by
  induction next with
  | here_next => exact .here_later .here
  | later_next _ inductionHypothesis =>
      exact .later_later inductionHypothesis

end NonClosingNext


structure CircularPresentation where
  Explicit : Type uE
  Implicit : Type uI
  Compatible : Implicit → Explicit → Type uK
  Difference : Type uD
  Provenance : Difference → Type uP
  initialNode :
    LocalNode Explicit Implicit Compatible Difference Provenance
  perimeter : PerimeterSpine Compatible initialNode
  perimeterPositive : NonClosingPosition perimeter
  finalJunction :
    Compatible perimeter.finalNode.implicit initialNode.explicit
  Endpoint : Type uEnd
  leftEndpoint : Endpoint
  rightEndpoint : Endpoint
  leftPole : Difference → Endpoint
  rightPole : Difference → Endpoint
  initialLeftPole :
    leftPole initialNode.difference = leftEndpoint
  initialRightPole :
    rightPole initialNode.difference = rightEndpoint
  TotalLoop : Type uLoop
  closeFromIdentification : leftEndpoint = rightEndpoint → TotalLoop
  loopContractsInitialDifference :
    TotalLoop →
      leftPole initialNode.difference = rightPole initialNode.difference
  rejectInitialContraction :
    (provenance : Provenance initialNode.difference) →
    leftPole initialNode.difference = rightPole initialNode.difference → False

namespace CircularPresentation

def rejectTotalLoop (P : CircularPresentation) : P.TotalLoop → False :=
  fun loop =>
    P.rejectInitialContraction
      P.initialNode.provenance
      (P.loopContractsInitialDifference loop)

def endpointsSeparated (P : CircularPresentation) :
    P.leftEndpoint ≠ P.rightEndpoint :=
  fun equality => P.rejectTotalLoop (P.closeFromIdentification equality)

end CircularPresentation

/- The initial failure of contraction is retained as positive, proof-relevant
   data.  It will be stored in the root boundary code and inherited by every
   code produced from it. -/
structure PositiveClosureObstruction (P : CircularPresentation) where
  provenance : P.Provenance P.initialNode.difference
  rejectsContraction :
    P.leftPole P.initialNode.difference =
      P.rightPole P.initialNode.difference → False

def CircularPresentation.positiveClosureObstruction
    (P : CircularPresentation) : PositiveClosureObstruction P :=
  { provenance := P.initialNode.provenance
    rejectsContraction := P.rejectInitialContraction P.initialNode.provenance }

inductive FinalRequirement (P : CircularPresentation) : Type
  | distinguished : FinalRequirement P

def finalRequirementContractible
    (P : CircularPresentation) :
    SegmentedResidualRole.ContractibleRole (FinalRequirement P) :=
  { center := .distinguished
    contracts := fun requirement => by
      cases requirement
      rfl }

def FinalJunctionCompatibility (P : CircularPresentation) : Type _ :=
  P.Compatible
    P.perimeter.finalNode.implicit
    P.initialNode.explicit

/- This witness separates raw closing compatibility from contraction: a
   junction may be positively present while the two endpoints remain apart. -/
structure RawJunctionWithSeparatedEndpoints
    (P : CircularPresentation) where
  junction : FinalJunctionCompatibility P
  separated : P.leftEndpoint ≠ P.rightEndpoint

def CircularRequirement (P : CircularPresentation) : Type _ :=
  NonClosingPosition P.perimeter ⊕ FinalRequirement P

structure ExplicitTotalization (P : CircularPresentation) where
  common : P.Explicit
  commonIsCurrent : common = P.initialNode.explicit
  reconstruct : P.Explicit → P.Endpoint
  reconstructsLeft : reconstruct common = P.leftEndpoint
  reconstructsRight : reconstruct common = P.rightEndpoint

structure ImplicitTotalization (P : CircularPresentation) where
  absorb : P.Endpoint → P.Implicit
  reconstruct : P.Implicit → P.Endpoint
  absorbsLeftAsCurrent : absorb P.leftEndpoint = P.initialNode.implicit
  absorbsRightAsCurrent : absorb P.rightEndpoint = P.initialNode.implicit
  leftRoundTrip : reconstruct (absorb P.leftEndpoint) = P.leftEndpoint
  rightRoundTrip : reconstruct (absorb P.rightEndpoint) = P.rightEndpoint

/- These two kernels isolate the exact operational data used by the rejection
   proofs.  The public totalizations remain stronger semantic structures: the
   explicit one additionally identifies its common value with the current
   explicit value, while the implicit one identifies both absorbed endpoints
   with the current implicit value. -/
structure ExplicitContractionKernel (P : CircularPresentation) where
  common : P.Explicit
  reconstruct : P.Explicit → P.Endpoint
  reconstructsLeft : reconstruct common = P.leftEndpoint
  reconstructsRight : reconstruct common = P.rightEndpoint

structure ImplicitContractionKernel (P : CircularPresentation) where
  absorb : P.Endpoint → P.Implicit
  reconstruct : P.Implicit → P.Endpoint
  absorbsCoincide : absorb P.leftEndpoint = absorb P.rightEndpoint
  leftRoundTrip : reconstruct (absorb P.leftEndpoint) = P.leftEndpoint
  rightRoundTrip : reconstruct (absorb P.rightEndpoint) = P.rightEndpoint

namespace ExplicitTotalization

def toContractionKernel
    {P : CircularPresentation}
    (totalization : ExplicitTotalization P) :
    ExplicitContractionKernel P :=
  { common := totalization.common
    reconstruct := totalization.reconstruct
    reconstructsLeft := totalization.reconstructsLeft
    reconstructsRight := totalization.reconstructsRight }

end ExplicitTotalization

namespace ImplicitTotalization

def toContractionKernel
    {P : CircularPresentation}
    (totalization : ImplicitTotalization P) :
    ImplicitContractionKernel P :=
  { absorb := totalization.absorb
    reconstruct := totalization.reconstruct
    absorbsCoincide :=
      totalization.absorbsLeftAsCurrent.trans
        totalization.absorbsRightAsCurrent.symm
    leftRoundTrip := totalization.leftRoundTrip
    rightRoundTrip := totalization.rightRoundTrip }

end ImplicitTotalization

structure ContractedClosureDifference (P : CircularPresentation) where
  difference : P.Difference
  isInitialDifference : difference = P.initialNode.difference
  provenance : P.Provenance difference
  poleContraction : P.leftPole difference = P.rightPole difference

namespace ContractedClosureDifference

def initialProvenance
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.Provenance P.initialNode.difference :=
  cast (congrArg P.Provenance contracted.isInitialDifference)
    contracted.provenance

def initialPoleContraction
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.leftPole P.initialNode.difference =
      P.rightPole P.initialNode.difference :=
  (congrArg P.leftPole contracted.isInitialDifference).symm.trans
    (contracted.poleContraction.trans
      (congrArg P.rightPole contracted.isInitialDifference))

def endpointContraction
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) :
    P.leftEndpoint = P.rightEndpoint :=
  P.initialLeftPole.symm.trans
    (contracted.initialPoleContraction.trans P.initialRightPole)

def toTotalLoop
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) : P.TotalLoop :=
  P.closeFromIdentification contracted.endpointContraction

def reject
    {P : CircularPresentation}
    (contracted : ContractedClosureDifference P) : False :=
  P.rejectInitialContraction
    contracted.initialProvenance
    contracted.initialPoleContraction

end ContractedClosureDifference

def explicitKernelContractsClosureDifference
    {P : CircularPresentation}
    (kernel : ExplicitContractionKernel P) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := P.initialNode.provenance
    poleContraction :=
      P.initialLeftPole.trans
        ((kernel.reconstructsLeft.symm.trans
          kernel.reconstructsRight).trans
          P.initialRightPole.symm) }

def implicitKernelContractsClosureDifference
    {P : CircularPresentation}
    (kernel : ImplicitContractionKernel P) :
    ContractedClosureDifference P :=
  { difference := P.initialNode.difference
    isInitialDifference := rfl
    provenance := P.initialNode.provenance
    poleContraction :=
      P.initialLeftPole.trans
        ((kernel.leftRoundTrip.symm.trans
          ((congrArg kernel.reconstruct kernel.absorbsCoincide).trans
            kernel.rightRoundTrip)).trans
          P.initialRightPole.symm) }

def explicitContractionKernelRejected
    {P : CircularPresentation} : ExplicitContractionKernel P → False :=
  fun kernel => (explicitKernelContractsClosureDifference kernel).reject

def implicitContractionKernelRejected
    {P : CircularPresentation} : ImplicitContractionKernel P → False :=
  fun kernel => (implicitKernelContractsClosureDifference kernel).reject

def explicitTotalizationContractsClosureDifference
    {P : CircularPresentation}
    (totalization : ExplicitTotalization P) :
    ContractedClosureDifference P :=
  explicitKernelContractsClosureDifference totalization.toContractionKernel

def implicitTotalizationContractsClosureDifference
    {P : CircularPresentation}
    (totalization : ImplicitTotalization P) :
    ContractedClosureDifference P :=
  implicitKernelContractsClosureDifference totalization.toContractionKernel

def explicitTotalizationRejected
    {P : CircularPresentation} : ExplicitTotalization P → False :=
  fun totalization =>
    (explicitTotalizationContractsClosureDifference totalization).reject

def implicitTotalizationRejected
    {P : CircularPresentation} : ImplicitTotalization P → False :=
  fun totalization =>
    (implicitTotalizationContractsClosureDifference totalization).reject


end StrongPerimetralTurning
