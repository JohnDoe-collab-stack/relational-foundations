import Constitution.Presentation
set_option linter.defProp false
set_option linter.checkUnivs false
set_option genInjectivity false

namespace StrongPerimetralTurning
universe uE uI uK uD uP uN uEnd uLoop uA uB uV uSpec uAdequacy uRegime uFaithful vA vB vC vF vG vH vJ
/-! ## Returned readings and intrinsic free construction -/

inductive FreeTail : Type
  | first
  | next : FreeTail → FreeTail

theorem FreeTail.next.inj {left right : FreeTail} (eq : FreeTail.next left = .next right) : left = right := by
  cases eq
  rfl

inductive PerimeterCursor (P : CircularPresentation) : Type _
  | within
      {node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      (remaining : PerimeterSpine P.Compatible node) : PerimeterCursor P
  | beyond : FreeTail → PerimeterCursor P

def advanceCursor {P : CircularPresentation} :
    PerimeterCursor P → PerimeterCursor P
  | .within (.advance _ tail) => .within tail
  | .within (.boundary _) => .beyond .first
  | .beyond tail => .beyond (.next tail)

inductive CursorAdvance (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | withinAdvance
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      (nextCompatible : P.Compatible node.implicit nextNode.explicit)
      (tail : PerimeterSpine P.Compatible nextNode) :
      CursorAdvance P
        (.within (.advance nextCompatible tail))
        (.within tail)
  | leaveBoundary
      (node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance) :
      CursorAdvance P (.within (.boundary node)) (.beyond .first)
  | beyondAdvance
      (tail : FreeTail) :
      CursorAdvance P (.beyond tail) (.beyond (.next tail))

inductive PositiveCursorAdvance (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | one : CursorAdvance P a b → PositiveCursorAdvance P a b
  | followedBy :
      PositiveCursorAdvance P a b →
      CursorAdvance P b c →
      PositiveCursorAdvance P a c

def cursorAdvanceGraph
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    CursorAdvance P cursor (advanceCursor cursor) :=
  match cursor with
  | .within (.boundary node) => .leaveBoundary node
  | .within (.advance compatible tail) =>
      .withinAdvance compatible tail
  | .beyond tail => .beyondAdvance tail

inductive StructuralDepth : Type
  | root
  | next : StructuralDepth → StructuralDepth

theorem StructuralDepth.next.inj {first second : StructuralDepth} (eq : StructuralDepth.next first = .next second) : first = second := by
  cases eq
  rfl

inductive ProperStructuralDepth : StructuralDepth → StructuralDepth → Type
  | direct (depth : StructuralDepth) :
      ProperStructuralDepth depth (.next depth)
  | later : ProperStructuralDepth shallower deeper →
      ProperStructuralDepth shallower (.next deeper)

inductive PositiveUnaryExtension : Type
  | one
  | more : PositiveUnaryExtension → PositiveUnaryExtension

def PositiveUnaryExtension.applyDepth :
    PositiveUnaryExtension → StructuralDepth → StructuralDepth
  | .one, depth => .next depth
  | .more extension, depth => .next (extension.applyDepth depth)

def PositiveUnaryExtension.applyDepth_next
    (extension : PositiveUnaryExtension)
    (depth : StructuralDepth) :
    extension.applyDepth (.next depth) =
      .next (extension.applyDepth depth) := by
  induction extension with
  | one => rfl
  | more extension inductionHypothesis =>
      exact congrArg StructuralDepth.next inductionHypothesis

def PositiveUnaryExtension.applyDepth_ne_self :
    (depth : StructuralDepth) → (extension : PositiveUnaryExtension) →
      extension.applyDepth depth = depth → False
  | .root, .one, equality => nomatch equality
  | .root, .more _extension, equality => nomatch equality
  | .next depth, extension, equality =>
      PositiveUnaryExtension.applyDepth_ne_self depth extension
        (StructuralDepth.next.inj
          ((extension.applyDepth_next depth).symm.trans equality))

namespace ProperStructuralDepth

def toPositiveExtension
    {shallower deeper : StructuralDepth} :
    ProperStructuralDepth shallower deeper →
      Σ extension : PositiveUnaryExtension,
        PLift (deeper = extension.applyDepth shallower)
  | .direct _ => ⟨.one, ⟨rfl⟩⟩
  | .later proper =>
      let result := proper.toPositiveExtension
      ⟨.more result.1,
        ⟨congrArg StructuralDepth.next result.2.down⟩⟩

def trans : ProperStructuralDepth a b → ProperStructuralDepth b c →
    ProperStructuralDepth a c
  | left, .direct _ => .later left
  | left, .later right => .later (trans left right)

theorem irreflexive
    (depth : StructuralDepth) : ProperStructuralDepth depth depth → False :=
  fun proper =>
    let result := proper.toPositiveExtension
    result.1.applyDepth_ne_self depth result.2.down.symm

end ProperStructuralDepth

def spineDepth
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} :
    PerimeterSpine P.Compatible node → StructuralDepth
  | .boundary _ => .root
  | .advance _ tail => .next (spineDepth tail)

inductive ProperSpineSuffix
    {P : CircularPresentation} :
    {sourceNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    PerimeterSpine P.Compatible sourceNode →
    {targetNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance} →
    PerimeterSpine P.Compatible targetNode → Type _
  | direct
      {node nextNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode} :
      ProperSpineSuffix (.advance compatible tail) tail
  | later
      {node nextNode targetNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {compatible : P.Compatible node.implicit nextNode.explicit}
      {tail : PerimeterSpine P.Compatible nextNode}
      {target : PerimeterSpine P.Compatible targetNode} :
      ProperSpineSuffix tail target →
      ProperSpineSuffix (.advance compatible tail) target

namespace ProperSpineSuffix

def toStructuralDepth
    {P : CircularPresentation}
    {sourceNode targetNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {source : PerimeterSpine P.Compatible sourceNode}
    {target : PerimeterSpine P.Compatible targetNode} :
    ProperSpineSuffix source target →
      ProperStructuralDepth (spineDepth target) (spineDepth source)
  | .direct => .direct _
  | .later suffix => .later suffix.toStructuralDepth

def trans
    {P : CircularPresentation}
    {aNode bNode cNode : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    {a : PerimeterSpine P.Compatible aNode}
    {b : PerimeterSpine P.Compatible bNode}
    {c : PerimeterSpine P.Compatible cNode} :
    ProperSpineSuffix a b → ProperSpineSuffix b c →
      ProperSpineSuffix a c
  | .direct, right => .later right
  | .later left, right => .later (trans left right)

theorem irreflexive
    {P : CircularPresentation}
    {node : LocalNode
      P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
    (spine : PerimeterSpine P.Compatible node) :
    ProperSpineSuffix spine spine → False :=
  fun suffix => ProperStructuralDepth.irreflexive _ suffix.toStructuralDepth

end ProperSpineSuffix

inductive ProperFreeTail : FreeTail → FreeTail → Type
  | direct (tail : FreeTail) : ProperFreeTail tail (.next tail)
  | later : ProperFreeTail source target →
      ProperFreeTail source (.next target)

namespace ProperFreeTail

def applyTail :
    PositiveUnaryExtension → FreeTail → FreeTail
  | .one, tail => .next tail
  | .more extension, tail => .next (applyTail extension tail)

def applyTail_next
    (extension : PositiveUnaryExtension)
    (tail : FreeTail) :
    applyTail extension (.next tail) = .next (applyTail extension tail) := by
  induction extension with
  | one => rfl
  | more extension inductionHypothesis =>
      exact congrArg FreeTail.next inductionHypothesis

def applyTail_ne_self :
    (tail : FreeTail) → (extension : PositiveUnaryExtension) →
      applyTail extension tail = tail → False
  | .first, .one, equality => nomatch equality
  | .first, .more _extension, equality => nomatch equality
  | .next tail, extension, equality =>
      applyTail_ne_self tail extension
        (FreeTail.next.inj
          ((applyTail_next extension tail).symm.trans equality))

def toPositiveExtension
    {source target : FreeTail} : ProperFreeTail source target →
    Σ extension : PositiveUnaryExtension,
      PLift (target = applyTail extension source)
  | .direct _ => ⟨.one, ⟨rfl⟩⟩
  | .later proper =>
      let result := proper.toPositiveExtension
      ⟨.more result.1, ⟨congrArg FreeTail.next result.2.down⟩⟩

def trans : ProperFreeTail a b → ProperFreeTail b c → ProperFreeTail a c
  | left, .direct _ => .later left
  | left, .later right => .later (trans left right)

theorem irreflexive (tail : FreeTail) : ProperFreeTail tail tail → False :=
  fun proper =>
    let result := proper.toPositiveExtension
    applyTail_ne_self tail result.1 result.2.down.symm

end ProperFreeTail

inductive CursorFuture (P : CircularPresentation) :
    PerimeterCursor P → PerimeterCursor P → Type _
  | withinSuffix
      {sourceNode targetNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {source : PerimeterSpine P.Compatible sourceNode}
      {target : PerimeterSpine P.Compatible targetNode} :
      ProperSpineSuffix source target →
      CursorFuture P (.within source) (.within target)
  | withinBeyond
      {sourceNode : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance}
      {source : PerimeterSpine P.Compatible sourceNode}
      (tail : FreeTail) : CursorFuture P (.within source) (.beyond tail)
  | beyondTail
      {source target : FreeTail} :
      ProperFreeTail source target →
      CursorFuture P (.beyond source) (.beyond target)

namespace CursorFuture

inductive Measure : Type
  | within : StructuralDepth → Measure
  | beyond : FreeTail → Measure

def measure
    {P : CircularPresentation} : PerimeterCursor P → Measure
  | .within spine => .within (spineDepth spine)
  | .beyond tail => .beyond tail

inductive ProperMeasure : Measure → Measure → Type
  | within
      {source target : StructuralDepth} :
      ProperStructuralDepth target source →
        ProperMeasure (.within source) (.within target)
  | cross
      (source : StructuralDepth) (target : FreeTail) :
      ProperMeasure (.within source) (.beyond target)
  | beyond
      {source target : FreeTail} :
      ProperFreeTail source target →
        ProperMeasure (.beyond source) (.beyond target)

namespace ProperMeasure

theorem irreflexive (point : Measure) : ProperMeasure point point → False := by
  cases point with
  | within depth =>
      intro later
      cases later with
      | within deeper => exact ProperStructuralDepth.irreflexive depth deeper
  | beyond tail =>
      intro later
      cases later with
      | beyond deeper => exact ProperFreeTail.irreflexive tail deeper

end ProperMeasure

def toProperMeasure
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    CursorFuture P source target → ProperMeasure (measure source) (measure target)
  | .withinSuffix suffix => .within suffix.toStructuralDepth
  | .withinBeyond tail => .cross _ tail
  | .beyondTail later => .beyond later

def trans
    {P : CircularPresentation}
    {a b c : PerimeterCursor P} :
    CursorFuture P a b → CursorFuture P b c → CursorFuture P a c
  | .withinSuffix left, .withinSuffix right =>
      .withinSuffix (ProperSpineSuffix.trans left right)
  | .withinSuffix _, .withinBeyond tail => .withinBeyond tail
  | .withinBeyond _, @CursorFuture.beyondTail _ _ target right =>
      .withinBeyond target
  | .beyondTail left, .beyondTail right =>
      .beyondTail (ProperFreeTail.trans left right)

theorem irreflexive
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CursorFuture P cursor cursor → False :=
  fun future => ProperMeasure.irreflexive (measure cursor) future.toProperMeasure

end CursorFuture

def CursorAdvance.toFuture
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    CursorAdvance P source target → CursorFuture P source target
  | .withinAdvance _ _ => .withinSuffix .direct
  | .leaveBoundary _ => .withinBeyond .first
  | .beyondAdvance tail => .beyondTail (.direct tail)

def PositiveCursorAdvance.toFuture
    {P : CircularPresentation}
    {source target : PerimeterCursor P} :
    PositiveCursorAdvance P source target → CursorFuture P source target
  | .one step => step.toFuture
  | .followedBy previous step => previous.toFuture.trans step.toFuture

theorem positiveCursorAdvance_irreflexive
    {P : CircularPresentation}
    {cursor : PerimeterCursor P} :
    PositiveCursorAdvance P cursor cursor → False :=
  fun positive => CursorFuture.irreflexive cursor positive.toFuture

inductive ReturnedExplicit (P : CircularPresentation) : Type _
  | source : P.Explicit → ReturnedExplicit P
  | formed : PerimeterCursor P → ReturnedExplicit P

inductive ReturnedImplicit (P : CircularPresentation) : Type _
  | source : P.Implicit → ReturnedImplicit P
  | formed : PerimeterCursor P → ReturnedImplicit P

inductive ReturnedCompatible (P : CircularPresentation) :
    ReturnedImplicit P → ReturnedExplicit P → Type _
  | source
      {i : P.Implicit} {e : P.Explicit} :
      P.Compatible i e → ReturnedCompatible P (.source i) (.source e)
  | formedInternal (cursor : PerimeterCursor P) :
      ReturnedCompatible P (.formed cursor) (.formed cursor)
  | leaveBoundary
      (node : LocalNode
        P.Explicit P.Implicit P.Compatible P.Difference P.Provenance) :
      ReturnedCompatible P
        (.source node.implicit) (.formed (.beyond .first))
  | beyondAdvance (tail : FreeTail) :
      ReturnedCompatible P
        (.formed (.beyond tail)) (.formed (.beyond (.next tail)))

def explicitAt {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedExplicit P :=
  match cursor with
  | .within remaining => .source remaining.startNode.explicit
  | .beyond tail => .formed (.beyond tail)

def implicitAt {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedImplicit P :=
  match cursor with
  | .within remaining => .source remaining.startNode.implicit
  | .beyond tail => .formed (.beyond tail)

def CompatibleExplicitation
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _ :=
  Σ e : ReturnedExplicit P, ReturnedCompatible P (implicitAt cursor) e

def internalCompatibleAt
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedCompatible P (implicitAt cursor) (explicitAt cursor) :=
  match cursor with
  | .within remaining => .source remaining.startNode.internallyCompatible
  | .beyond tail => .formedInternal (.beyond tail)

def currentCompatibleExplicitation
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CompatibleExplicitation P cursor :=
  ⟨explicitAt cursor, internalCompatibleAt cursor⟩

def stepCompatibleAt
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedCompatible P
      (implicitAt cursor) (explicitAt (advanceCursor cursor)) :=
  match cursor with
  | .within (.boundary node) => .leaveBoundary node
  | .within (@PerimeterSpine.advance _ _ _ _ _ node nextNode compatible _tail) =>
      show ReturnedCompatible P
        (.source node.implicit) (.source nextNode.explicit)
      from .source compatible
  | .beyond tail => .beyondAdvance tail

def successorCompatibleExplicitation
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) : CompatibleExplicitation P cursor :=
  ⟨explicitAt (advanceCursor cursor), stepCompatibleAt cursor⟩

inductive ReturnedDifference (P : CircularPresentation) : Type _
  | source : P.Difference → ReturnedDifference P
  | free : FreeTail → ReturnedDifference P

inductive ReturnedProvenance (P : CircularPresentation) :
    ReturnedDifference P → Type _
  | source
      {g : P.Difference} :
      P.Provenance g → ReturnedProvenance P (.source g)
  | free (tail : FreeTail) : ReturnedProvenance P (.free tail)

def differenceAtCursor {P : CircularPresentation}
    (cursor : PerimeterCursor P) : ReturnedDifference P :=
  match cursor with
  | .within remaining => .source remaining.startNode.difference
  | .beyond tail => .free tail

def provenanceAtCursor
    {P : CircularPresentation}
    (cursor : PerimeterCursor P) :
    ReturnedProvenance P (differenceAtCursor cursor) :=
  match cursor with
  | .within remaining => .source remaining.startNode.provenance
  | .beyond tail => .free tail

inductive FreeKAtom
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _
  | explicitPole
  | implicitPole
  | currentDifference
  | admissible : CompatibleExplicitation P cursor → FreeKAtom P cursor

structure FreeKAlgebra
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) where
  Carrier : Type uA
  explicitPole : Carrier
  implicitPole : Carrier
  currentDifference : Carrier
  admissible : CompatibleExplicitation P cursor → Carrier

def FreeKAtom.fold
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (A : FreeKAlgebra P cursor) : FreeKAtom P cursor → A.Carrier
  | .explicitPole => A.explicitPole
  | .implicitPole => A.implicitPole
  | .currentDifference => A.currentDifference
  | .admissible x => A.admissible x

/- Lean does not accept a mutually inductive family whose indices mention
   another member of the same mutual block.  The Lean-legal primitive encoding
   therefore puts the exact boundary code and exact free layer in the indices
   of `FreeConstitutionCore`.  The public dependent families below expose this
   stored data without weakening it to an external proposition. -/
inductive BoundaryDifferenceCode
    (P : CircularPresentation) : PerimeterCursor P → Type _
  | initial
      (obstruction : PositiveClosureObstruction P) :
      BoundaryDifferenceCode P (.within P.perimeter)
  | afterFormation
      {cursor : PerimeterCursor P}
      (integratedDifference : BoundaryDifferenceCode P cursor)
      (formationTerm : FreeKAtom P cursor)
      (formationTermIsSuccessor :
        formationTerm =
          .admissible (successorCompatibleExplicitation cursor)) :
      BoundaryDifferenceCode P (advanceCursor cursor)

namespace BoundaryDifferenceCode

def inheritedClosureObstruction
    {P : CircularPresentation} :
    {cursor : PerimeterCursor P} →
      BoundaryDifferenceCode P cursor → PositiveClosureObstruction P
  | _, .initial obstruction => obstruction
  | _, .afterFormation previous _ _ =>
      previous.inheritedClosureObstruction

end BoundaryDifferenceCode

structure FreeKCore
    (P : CircularPresentation)
    (cursor : PerimeterCursor P)
    (currentDifference : BoundaryDifferenceCode P cursor) where
  formationTerm : FreeKAtom P cursor
  formationTermIsSuccessor :
    formationTerm =
      .admissible (successorCompatibleExplicitation cursor)
  integratedClosureObstruction : PositiveClosureObstruction P
  integratedClosureObstructionIsCurrent :
    integratedClosureObstruction =
      currentDifference.inheritedClosureObstruction
  integratedProvenance :
    ReturnedProvenance P (differenceAtCursor cursor)
  integratedProvenanceIsCurrent :
    integratedProvenance = provenanceAtCursor cursor

inductive FreeConstitutionCore
    (P : CircularPresentation) :
    (cursor : PerimeterCursor P) → BoundaryDifferenceCode P cursor → Type _
  | root :
      FreeConstitutionCore P (.within P.perimeter)
        (.initial P.positiveClosureObstruction)
  | formed
      {cursor : PerimeterCursor P}
      {currentDifference : BoundaryDifferenceCode P cursor}
      (previous : FreeConstitutionCore P cursor currentDifference)
      (layer : FreeKCore P cursor currentDifference) :
      FreeConstitutionCore P (advanceCursor cursor)
        (.afterFormation currentDifference
          layer.formationTerm layer.formationTermIsSuccessor)

def FreeConstitution
    (P : CircularPresentation)
    (cursor : PerimeterCursor P) : Type _ :=
  Σ currentDifference : BoundaryDifferenceCode P cursor,
    FreeConstitutionCore P cursor currentDifference

namespace FreeConstitution

def root {P : CircularPresentation} :
    FreeConstitution P (.within P.perimeter) :=
  ⟨.initial P.positiveClosureObstruction, .root⟩

end FreeConstitution

inductive BoundaryDifference
    (P : CircularPresentation) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type
  | exact
      {cursor : PerimeterCursor P}
      {data : FreeConstitution P cursor} :
      BoundaryDifference P data

namespace BoundaryDifference

def initial {P : CircularPresentation} :
    BoundaryDifference P FreeConstitution.root :=
  .exact

end BoundaryDifference

structure FreeK
    (P : CircularPresentation)
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (_currentDifference : BoundaryDifference P previous) where
  core : FreeKCore P cursor previous.1

namespace FreeK

def canonical
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {currentDifference : BoundaryDifference P previous}
    (formationTerm : FreeKAtom P cursor)
    (formationTermIsSuccessor :
      formationTerm =
        .admissible (successorCompatibleExplicitation cursor)) :
    FreeK P previous currentDifference :=
  { core :=
      { formationTerm := formationTerm
        formationTermIsSuccessor := formationTermIsSuccessor
        integratedClosureObstruction :=
          previous.1.inheritedClosureObstruction
        integratedClosureObstructionIsCurrent := rfl
        integratedProvenance := provenanceAtCursor cursor
        integratedProvenanceIsCurrent := rfl } }

end FreeK

def FreeConstitution.formed
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    FreeConstitution P (advanceCursor cursor) :=
  ⟨.afterFormation previous.1
      (FreeKCore.formationTerm layer.core)
      (FreeKCore.formationTermIsSuccessor layer.core),
    .formed previous.2 layer.core⟩

@[simp] theorem FreeConstitution.formed_boundaryCode_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).1 =
      .afterFormation previous.1
        (FreeKCore.formationTerm layer.core)
        (FreeKCore.formationTermIsSuccessor layer.core) :=
  rfl

@[simp] theorem FreeConstitution.formed_core_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).2 =
      FreeConstitutionCore.formed previous.2 layer.core :=
  rfl

@[simp] theorem FreeConstitution.root_inheritedClosureObstruction_exact
    {P : CircularPresentation} :
    (FreeConstitution.root (P := P)).1.inheritedClosureObstruction =
      P.positiveClosureObstruction :=
  rfl

@[simp] theorem FreeConstitution.formed_inheritedClosureObstruction_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    BoundaryDifferenceCode.inheritedClosureObstruction
        (FreeConstitution.formed previous currentDifference layer).1 =
      BoundaryDifferenceCode.inheritedClosureObstruction previous.1 :=
  rfl

@[simp] theorem FreeConstitution.formed_integratedClosureObstruction_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    layer.core.integratedClosureObstruction =
      previous.1.inheritedClosureObstruction :=
  layer.core.integratedClosureObstructionIsCurrent

@[simp] theorem FreeConstitution.formed_integratedProvenance_exact
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (currentDifference : BoundaryDifference P previous)
    (layer : FreeK P previous currentDifference) :
    (FreeConstitution.formed previous currentDifference layer).2 =
      FreeConstitutionCore.formed previous.2 layer.core ∧
    layer.core.integratedProvenance = provenanceAtCursor cursor :=
  ⟨rfl, layer.core.integratedProvenanceIsCurrent⟩

def BoundaryDifference.afterFormation
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    (previous : FreeConstitution P cursor)
    (integratedDifference : BoundaryDifference P previous)
    (layer : FreeK P previous integratedDifference) :
    BoundaryDifference P
      (FreeConstitution.formed previous integratedDifference layer) :=
  .exact

def FreeK.formationTerm
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous} :
    FreeK P previous difference → FreeKAtom P cursor :=
  fun layer => FreeKCore.formationTerm layer.core

theorem FreeK.formationTerm_is_successor
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    {difference : BoundaryDifference P previous}
    (layer : FreeK P previous difference) :
    layer.formationTerm =
      .admissible (successorCompatibleExplicitation cursor) :=
  FreeKCore.formationTermIsSuccessor layer.core

def FreeConstitutionSpace (P : CircularPresentation) : Type _ :=
  Σ cursor : PerimeterCursor P, FreeConstitution P cursor

inductive FormationRecord (P : CircularPresentation) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type _
  | current
      {cursor}
      {previous : FreeConstitution P cursor}
      {currentDifference : BoundaryDifference P previous}
      {layer : FreeK P previous currentDifference} :
      FormationRecord P
        (FreeConstitution.formed previous currentDifference layer)
  | preserved
      {cursor}
      {previous : FreeConstitution P cursor}
      {currentDifference : BoundaryDifference P previous}
      {layer : FreeK P previous currentDifference} :
      FormationRecord P previous →
      FormationRecord P
        (FreeConstitution.formed previous currentDifference layer)

def PositiveConstitution (P : CircularPresentation) : Type _ :=
  Σ cursor : PerimeterCursor P,
    Σ data : FreeConstitution P cursor, BoundaryDifference P data

def initialPositive (P : CircularPresentation) : PositiveConstitution P :=
  ⟨.within P.perimeter, .root, .initial⟩

def explicitRead {P : CircularPresentation}
    (d : PositiveConstitution P) : ReturnedExplicit P := explicitAt d.1

def implicitRead {P : CircularPresentation}
    (d : PositiveConstitution P) : ReturnedImplicit P := implicitAt d.1

def boundaryDifferenceReadout
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {data : FreeConstitution P cursor}
    (_ : BoundaryDifference P data) : ReturnedDifference P :=
  differenceAtCursor cursor

def boundaryProvenanceReadout
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {data : FreeConstitution P cursor}
    (_ : BoundaryDifference P data) :
    ReturnedProvenance P (differenceAtCursor cursor) :=
  provenanceAtCursor cursor

/- A historical provenance record is indexed by the complete positive origin,
   not merely by its returned readings.  Two origins with coincident readings
   therefore remain different indices.  `integrated` records the exact layer
   that consumed the origin's boundary difference; `preserved` carries this
   record through every later formation. -/
inductive HistoricalProvenanceRecord
    (P : CircularPresentation)
    (origin : PositiveConstitution P) :
    {cursor : PerimeterCursor P} → FreeConstitution P cursor → Type _
  | atOrigin :
      HistoricalProvenanceRecord P origin origin.2.1
  | integrated
      {layer : FreeK P origin.2.1 origin.2.2} :
      HistoricalProvenanceRecord P origin
        (FreeConstitution.formed origin.2.1 origin.2.2 layer)
  | preserved
      {cursor : PerimeterCursor P}
      {previous : FreeConstitution P cursor}
      {difference : BoundaryDifference P previous}
      {layer : FreeK P previous difference} :
      HistoricalProvenanceRecord P origin previous →
      HistoricalProvenanceRecord P origin
        (FreeConstitution.formed previous difference layer)

namespace HistoricalProvenanceRecord

def recordedDifference
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (_record : HistoricalProvenanceRecord P origin targetData) :
    ReturnedDifference P :=
  boundaryDifferenceReadout origin.2.2

def recordedProvenance
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (record : HistoricalProvenanceRecord P origin targetData) :
    ReturnedProvenance P record.recordedDifference :=
  match record with
  | .atOrigin => boundaryProvenanceReadout origin.2.2
  | .integrated (layer := layer) => layer.core.integratedProvenance
  | .preserved previousRecord => previousRecord.recordedProvenance

theorem recordedProvenance_is_origin
    {P : CircularPresentation}
    {origin : PositiveConstitution P}
    {cursor : PerimeterCursor P}
    {targetData : FreeConstitution P cursor}
    (record : HistoricalProvenanceRecord P origin targetData) :
    record.recordedProvenance =
      boundaryProvenanceReadout origin.2.2 := by
  cases record with
  | atOrigin => rfl
  | integrated =>
      exact FreeKCore.integratedProvenanceIsCurrent _
  | preserved previousRecord =>
      exact recordedProvenance_is_origin previousRecord

end HistoricalProvenanceRecord

def canonicalFreeLayer
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FreeK P source.2.1 source.2.2 :=
  .canonical
    (.admissible (successorCompatibleExplicitation source.1)) rfl

def successorFormationTerm
    {P : CircularPresentation}
    (source : PositiveConstitution P) : FreeKAtom P source.1 :=
  .admissible (successorCompatibleExplicitation source.1)

def formationSyntax
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ :=
  FreeKAtom P source.1

structure FreeLayerApplication
    (P : CircularPresentation)
    (source : PositiveConstitution P) where
  algebra : FreeKAlgebra.{uA} P source.1
  realize : FreeKAtom P source.1 → algebra.Carrier
  realizesExplicitPole : realize .explicitPole = algebra.explicitPole
  realizesImplicitPole : realize .implicitPole = algebra.implicitPole
  realizesCurrentDifference :
    realize .currentDifference = algebra.currentDifference
  realizesAdmissible :
    (x : CompatibleExplicitation P source.1) →
      realize (.admissible x) = algebra.admissible x

theorem FreeLayerApplication.realize_eq_fold
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (application : FreeLayerApplication P source)
    (atom : FreeKAtom P source.1) :
    application.realize atom = FreeKAtom.fold application.algebra atom := by
  cases atom with
  | explicitPole => exact application.realizesExplicitPole
  | implicitPole => exact application.realizesImplicitPole
  | currentDifference => exact application.realizesCurrentDifference
  | admissible compatible => exact application.realizesAdmissible compatible

def canonicalFreeLayerApplication
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FreeLayerApplication P source :=
  { algebra :=
      { Carrier := FreeKAtom P source.1
        explicitPole := .explicitPole
        implicitPole := .implicitPole
        currentDifference := .currentDifference
        admissible := .admissible }
    realize := fun atom =>
      FreeKAtom.fold
        { Carrier := FreeKAtom P source.1
          explicitPole := .explicitPole
          implicitPole := .implicitPole
          currentDifference := .currentDifference
          admissible := .admissible }
        atom
    realizesExplicitPole := rfl
    realizesImplicitPole := rfl
    realizesCurrentDifference := rfl
    realizesAdmissible := fun _ => rfl }

def formationEliminator
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (application : FreeLayerApplication P source) :
    formationSyntax source → application.algebra.Carrier :=
  application.realize

theorem formationEliminator_is_free_fold
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (application : FreeLayerApplication P source)
    (atom : formationSyntax source) :
    formationEliminator source application atom =
      FreeKAtom.fold application.algebra atom :=
  application.realize_eq_fold atom

@[simp] theorem canonicalFormationEliminator_exact
    {P : CircularPresentation}
    (source : PositiveConstitution P)
    (atom : formationSyntax source) :
    formationEliminator source (canonicalFreeLayerApplication source) atom =
      atom := by
  cases atom <;> rfl

theorem canonicalFreeLayer_is_free_elimination
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    (canonicalFreeLayer source).formationTerm =
      formationEliminator source (canonicalFreeLayerApplication source)
        (successorFormationTerm source) :=
  (canonicalFormationEliminator_exact source
    (successorFormationTerm source)).symm

def constitutionOf
    {P : CircularPresentation}
    (d : PositiveConstitution P) : FreeConstitutionSpace P :=
  ⟨advanceCursor d.1,
    .formed d.2.1 d.2.2 (canonicalFreeLayer d)⟩

def boundaryDifferenceOf
    {P : CircularPresentation}
    (d : PositiveConstitution P) :
    BoundaryDifference P (constitutionOf d).2 :=
  .afterFormation d.2.1 d.2.2 (canonicalFreeLayer d)

def canonicalTarget
    {P : CircularPresentation}
    (d : PositiveConstitution P) : PositiveConstitution P :=
  ⟨(constitutionOf d).1, (constitutionOf d).2, boundaryDifferenceOf d⟩

@[simp] theorem canonicalTarget_inheritedClosureObstruction_exact
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    (canonicalTarget source).2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction :=
  rfl

structure IntegratedDifferenceRecord
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {previous : FreeConstitution P cursor}
    (g : BoundaryDifference P previous)
    (target : FreeConstitution P (advanceCursor cursor)) : Type _ where
  layer : FreeK P previous g
  targetIsFormation : target = FreeConstitution.formed previous g layer

def Integrates
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ :=
  IntegratedDifferenceRecord source.2.2 (canonicalTarget source).2.1

namespace HistoricalProvenanceRecord

def ofIntegration
    {P : CircularPresentation}
    {source : PositiveConstitution P}
    (integration : Integrates source) :
    HistoricalProvenanceRecord P source (canonicalTarget source).2.1 := by
  exact Eq.mp
    (congrArg
      (fun targetData => HistoricalProvenanceRecord P source targetData)
      integration.targetIsFormation.symm)
    (HistoricalProvenanceRecord.integrated
      (layer := integration.layer))

end HistoricalProvenanceRecord

structure PreservesProvenance
    {P : CircularPresentation}
    (source target : PositiveConstitution P) : Type _ where
  targetIsCanonical : target = canonicalTarget source
  integrated : Integrates source

namespace PreservesProvenance

def inscribedInTarget
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    HistoricalProvenanceRecord P source target.2.1 := by
  cases preserves.targetIsCanonical
  exact HistoricalProvenanceRecord.ofIntegration preserves.integrated

def exactProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    ReturnedProvenance P (boundaryDifferenceReadout source.2.2) :=
  preserves.inscribedInTarget.recordedProvenance

theorem exactProvenance_is_origin
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (preserves : PreservesProvenance source target) :
    preserves.exactProvenance =
      boundaryProvenanceReadout source.2.2 :=
  preserves.inscribedInTarget.recordedProvenance_is_origin

end PreservesProvenance

def canonicalPreservesProvenance
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    PreservesProvenance source (canonicalTarget source) :=
  { targetIsCanonical := rfl
    integrated :=
      { layer := canonicalFreeLayer source
        targetIsFormation := rfl } }

def canonicalSourceProvenanceInscribed
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    HistoricalProvenanceRecord P source (canonicalTarget source).2.1 :=
  HistoricalProvenanceRecord.ofIntegration
    (canonicalPreservesProvenance source).integrated

structure RecoveredImmediateOrigin
    (P : CircularPresentation)
    {cursor : PerimeterCursor P}
    (target : FreeConstitution P cursor) where
  origin : PositiveConstitution P
  record : HistoricalProvenanceRecord P origin target

def recoverImmediateOriginFromFormation
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {target : FreeConstitution P cursor}
    (formed : FormationRecord P target) :
    RecoveredImmediateOrigin P target := by
  cases formed with
  | @current cursor previous difference layer =>
      exact
        { origin := ⟨cursor, previous, difference⟩
          record := .integrated }
  | @preserved cursor previous difference layer old =>
      exact
        { origin := ⟨cursor, previous, difference⟩
          record := .integrated }

def RecoveredImmediateOrigin.provenance
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {target : FreeConstitution P cursor}
    (recovered : RecoveredImmediateOrigin P target) :
    ReturnedProvenance P recovered.record.recordedDifference :=
  recovered.record.recordedProvenance

structure ContinuesDifference
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  targetBoundaryIsNext :
    (canonicalTarget source).2.2 = boundaryDifferenceOf source

def preserveRecordIntoCanonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FormationRecord P source.2.1 →
      FormationRecord P (canonicalTarget source).2.1 := by
  intro old
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .preserved old

def currentRecordInCanonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    FormationRecord P (canonicalTarget source).2.1 := by
  change FormationRecord P
    (FreeConstitution.formed source.2.1 source.2.2
      (canonicalFreeLayer source))
  exact .current

structure FreshBoundaryDifference
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  continuation : ContinuesDifference source
  freshRecord : FormationRecord P (canonicalTarget source).2.1
  freshRecordIsCurrent :
    freshRecord = currentRecordInCanonicalTarget source
  notPreservedOld :
    (oldRecord : FormationRecord P source.2.1) →
      freshRecord ≠ preserveRecordIntoCanonicalTarget source oldRecord

/- The positive obstruction is not merely carried beside the formation.  The
   free layer consumes that exact obstruction, and the boundary code produced
   by the layer inherits it unchanged. -/
structure IntegratesClosureObstruction
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  integratedByFormation :
    (canonicalFreeLayer source).core.integratedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction
  inheritedByTarget :
    (canonicalTarget source).2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction

structure CanonicalGeneratedLaws
    {P : CircularPresentation}
    (source : PositiveConstitution P) : Type _ where
  compatibility :
    ReturnedCompatible P
      (implicitRead source) (explicitRead (canonicalTarget source))
  compatibilityIsCanonical :
    compatibility = stepCompatibleAt source.1
  preservesProvenance :
    PreservesProvenance source (canonicalTarget source)
  integratesClosureObstruction : IntegratesClosureObstruction source
  continuesDifference : ContinuesDifference source
  freshBoundaryDifference : FreshBoundaryDifference source

structure GeneratedStep
    {P : CircularPresentation}
    (source target : PositiveConstitution P) : Type _ where
  formedByFreeLayer : target = canonicalTarget source
  laws : CanonicalGeneratedLaws source

namespace GeneratedStep

def compatibility
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    ReturnedCompatible P (implicitRead source) (explicitRead target) := by
  cases step.formedByFreeLayer
  exact step.laws.compatibility

theorem compatibilityWitnessExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HEq step.compatibility (stepCompatibleAt source.1) := by
  cases step.formedByFreeLayer
  exact heq_of_eq step.laws.compatibilityIsCanonical

theorem rejectsAlternativeCompatibility
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target)
    (alternative :
      ReturnedCompatible P (implicitRead source) (explicitRead target))
    (alternativeIsSeparated :
      HEq alternative (stepCompatibleAt source.1) → False) :
    step.compatibility ≠ alternative := by
  intro equality
  exact alternativeIsSeparated
    ((heq_of_eq equality.symm).trans step.compatibilityWitnessExact)

def integratesCurrentDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : Integrates source :=
  step.laws.preservesProvenance.integrated

def preservesProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    PreservesProvenance source target := by
  cases step.formedByFreeLayer
  exact step.laws.preservesProvenance

theorem provenanceWitnessExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    step.preservesProvenance.exactProvenance =
      boundaryProvenanceReadout source.2.2 :=
  step.preservesProvenance.exactProvenance_is_origin

def sourceProvenanceInscribedInTarget
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HistoricalProvenanceRecord P source target.2.1 :=
  step.preservesProvenance.inscribedInTarget

def currentFormationRecord
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    FormationRecord P target.2.1 := by
  cases step.formedByFreeLayer
  exact step.laws.freshBoundaryDifference.freshRecord

theorem currentFormationRecord_is_current
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    HEq step.currentFormationRecord
      (currentRecordInCanonicalTarget source) := by
  cases step.formedByFreeLayer
  exact heq_of_eq
    step.laws.freshBoundaryDifference.freshRecordIsCurrent

theorem rejectsAlternativeProvenance
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target)
    (alternative :
      ReturnedProvenance P (boundaryDifferenceReadout source.2.2))
    (alternativeIsSeparated :
      alternative ≠ boundaryProvenanceReadout source.2.2) :
    step.preservesProvenance.exactProvenance ≠ alternative := by
  intro equality
  exact alternativeIsSeparated
    (equality.symm.trans step.provenanceWitnessExact)

def continuesDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : ContinuesDifference source :=
  step.laws.continuesDifference

def integratesClosureObstruction
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    IntegratesClosureObstruction source :=
  step.laws.integratesClosureObstruction

theorem inheritedClosureObstructionExact
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) :
    target.2.1.1.inheritedClosureObstruction =
      source.2.1.1.inheritedClosureObstruction := by
  cases step.formedByFreeLayer
  exact step.laws.integratesClosureObstruction.inheritedByTarget

def freshBoundaryDifference
    {P : CircularPresentation}
    {source target : PositiveConstitution P}
    (step : GeneratedStep source target) : FreshBoundaryDifference source :=
  step.laws.freshBoundaryDifference

end GeneratedStep

def generatedStepOfFreeK
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    GeneratedStep source (canonicalTarget source) :=
  { formedByFreeLayer := rfl
    laws :=
      { compatibility := stepCompatibleAt source.1
        compatibilityIsCanonical := rfl
        preservesProvenance := canonicalPreservesProvenance source
        integratesClosureObstruction :=
          { integratedByFormation := rfl
            inheritedByTarget := rfl }
        continuesDifference := { targetBoundaryIsNext := rfl }
        freshBoundaryDifference :=
          { continuation := { targetBoundaryIsNext := rfl }
            freshRecord := currentRecordInCanonicalTarget source
            freshRecordIsCurrent := rfl
            notPreservedOld := by
              intro old equality
              cases equality } } }

def generate
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    Σ target : PositiveConstitution P, GeneratedStep source target :=
  ⟨canonicalTarget source, generatedStepOfFreeK source⟩


end StrongPerimetralTurning
