import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.StructuralGlobalContextRelation

namespace DeepPreservationRegression
open ConstitutiveSearch ConstitutiveSearch.SAT

/-- The actual relation with its formula agreement erased, retaining structural data. -/
structure DecisionsOnlyFlip {root : Cnf} (var : Var)
    (source target : GeneratedStructuralBranchContext root) where
  decisionsExact : target.context.decisions = flipStructuralDecisionsAt var source.context.decisions

def DecisionsOnlyFlip.map {root : Cnf} {var : Var}
    {source target : GeneratedStructuralBranchContext root}
    (relation : DecisionsOnlyFlip var source target)
    (c : GeneratedStructuralBranchContinuation source) : GeneratedStructuralBranchContinuation target :=
  ⟨Assignment.flipAt var c.1,
    relation.decisionsExact.symm ▸ StructuralDecisionsHold.flipAt c.2 var⟩

def parent : GeneratedStructuralBranchContext [[Literal.negative 0]] :=
  .root [[Literal.negative 0]]

def source := parent.child 0 false True.intro

def target := parent.child 0 true True.intro

theorem structuralRelation : DecisionsOnlyFlip 0 source target := ⟨rfl⟩

def acceptedSource : GeneratedStructuralBranchContinuation source :=
  ⟨fun _ => false, ⟨rfl, True.intro⟩⟩

theorem sourceAccepted : GeneratedStructuralBranchAccept source acceptedSource :=
  Satisfies.nil

theorem mappedSourceNotAccepted :
    ¬ GeneratedStructuralBranchAccept target (structuralRelation.map acceptedSource) := by
  intro accepted
  change Satisfies (Assignment.flipAt 0 (fun _ => false)) [[Literal.negative 0]] at accepted
  cases accepted with
  | cons head _ =>
    change (false : Bool) = true at head
    cases head

/-- The erased formula guarantee cannot be recovered from structural agreement alone. -/
theorem noUniversalPreservation :
    ¬ (∀ c : GeneratedStructuralBranchContinuation source,
      GeneratedStructuralBranchAccept source c →
      GeneratedStructuralBranchAccept target (structuralRelation.map c)) := by
  intro preservation
  exact mappedSourceNotAccepted (preservation acceptedSource sourceAccepted)

/-- This is a real obstruction to the original relation, not a missing field name. -/
theorem fullRelationImpossible : ¬ Nonempty (GeneratedStructuralFlipAtRelation 0 source target) := by
  intro existsRelation
  rcases existsRelation with ⟨relation⟩
  have preserved := relation.mapContinuation_accept acceptedSource sourceAccepted
  have same : relation.mapContinuation acceptedSource = structuralRelation.map acceptedSource :=
    Subtype.ext rfl
  exact mappedSourceNotAccepted (same ▸ preserved)

end DeepPreservationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms DeepPreservationRegression.DecisionsOnlyFlip
#print axioms DeepPreservationRegression.DecisionsOnlyFlip.map
#print axioms DeepPreservationRegression.parent
#print axioms DeepPreservationRegression.source
#print axioms DeepPreservationRegression.target
#print axioms DeepPreservationRegression.structuralRelation
#print axioms DeepPreservationRegression.acceptedSource
#print axioms DeepPreservationRegression.sourceAccepted
#print axioms DeepPreservationRegression.mappedSourceNotAccepted
#print axioms DeepPreservationRegression.noUniversalPreservation
#print axioms DeepPreservationRegression.fullRelationImpossible
/- AXIOM_AUDIT_END -/
