import RelationalFoundations.GroupingNormalization
import RelationalFoundations.ExactTransport
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping
universe v
namespace Rules
variable (old : Rules.{0}) {A : Type v} (code : ExactTransport A old.State)

theorem lifted_heq {X Y : Type} {x : X} {y : Y} (same : HEq x y) :
    HEq (ULift.up x : ULift.{v} X) (ULift.up y : ULift.{v} Y) := by
  cases same
  rfl

def ReindexedStep (x y : A) := ULift.{v} (old.Step (code.forward x) (code.forward y))

def reindexedEntry (x : A) (entry : (z : old.State) × old.Step (code.forward x) z) :
    (y : A) × ReindexedStep old code x y :=
  ⟨code.backward entry.1, ⟨(code.backwardForward entry.1).symm ▸ entry.2⟩⟩

theorem reindexed_member {x : A} (entry : (z : old.State) × old.Step (code.forward x) z)
    (entries : List ((z : old.State) × old.Step (code.forward x) z))
    (member : entry ∈ entries) :
    reindexedEntry old code x entry ∈ entries.map (reindexedEntry old code x) := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head => exact List.Mem.head _
      | tail _ tailMember => exact List.Mem.tail _ (ih tailMember)

def reindexedTrace {x y : old.State} : Trace old.Step x y →
    Trace (ReindexedStep old code) (code.backward x) (code.backward y)
  | .nil _ => .nil _
  | .cons step tail =>
      .cons ⟨(code.backwardForward _).symm ▸
        (code.backwardForward _).symm ▸ step⟩ (reindexedTrace tail)

def reindex : Rules.{v} where
  State := A
  Step := ReindexedStep old code
  rank := fun x => old.rank (code.forward x)
  choices := fun x => (old.choices (code.forward x)).map (reindexedEntry old code x)
  locate := by
    intro x y step
    obtain ⟨entry, member, same⟩ := old.locate step.down
    have equality := eq_of_heq same
    cases equality
    have member' := reindexed_member old code _ _ member
    have targetSame := code.forwardBackward y
    refine ⟨reindexedEntry old code x ⟨code.forward y, step.down⟩, member', ?_⟩
    apply heq_of_eq
    apply Sigma.ext targetSame
    exact lifted_heq (eqRec_heq (code.backwardForward (code.forward y)).symm step.down)
  decreases := fun step => old.decreases step.down
  diamond := by
    intro x y z first second
    let joined := old.diamond first.down second.down
    have left := reindexedTrace old code joined.left
    have right := reindexedTrace old code joined.right
    rw [code.forwardBackward y] at left
    rw [code.forwardBackward z] at right
    exact ⟨code.backward joined.target, left, right⟩

theorem reindex_normal (x : A) :
    (old.reindex code).normal x = code.backward (old.normal (code.forward x)) := by
  let produced := old.normalize (code.forward x)
  have traced := reindexedTrace old code produced.trace
  rw [code.forwardBackward x] at traced
  have terminal : (old.reindex code).Terminal (code.backward produced.target) := by
    intro y step
    exact produced.terminal ((code.backwardForward produced.target) ▸ step.down)
  exact ((old.reindex code).normal_trace traced).trans
    ((old.reindex code).normal_terminal _ terminal)
end Rules
end RelationalFoundations.CertifiedGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Rules.reindexedTrace
#print axioms RelationalFoundations.CertifiedGrouping.Rules.reindex
#print axioms RelationalFoundations.CertifiedGrouping.Rules.reindex_normal
/- AXIOM_AUDIT_END -/
