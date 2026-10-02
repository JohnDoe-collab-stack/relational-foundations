import RelationalFoundations.InteriorDelimitation
import RelationalFoundations.Generation
import RelationalFoundations.Residual
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c

/-- Positive generation data, independent of the primitive closing relation. -/
structure OneStepContinuation (p : CircularPresentation.{u,v,t,i,c}) where
  target : p.Node
  witness : p.Next p.spine.finalNode target

namespace OneStepContinuation
variable {p : CircularPresentation.{u,v,t,i,c}} (s : OneStepContinuation p)

def history : History p.Next p.start s.target := .extend p.interiorHistory s.witness
abbrev Occurrence := History.Occurrence s.history

def old (o : p.InteriorOccurrence) : s.Occurrence := .earlier o
def fresh (_ : Unit) : s.Occurrence := .last

def label : s.Occurrence → p.FullRole
  | .last => .inr .final
  | .earlier o => .inl (Spine.decode p.spine o)

theorem label_faithful : Function.Injective s.label := by
  intro a b eq
  cases a with
  | last =>
    cases b with
    | last => rfl
    | earlier b => cases eq
  | earlier a =>
    cases b with
    | last => cases eq
    | earlier b =>
      exact congrArg History.Occurrence.earlier
        (p.interiorRealization.backward_injective (Sum.inl.inj eq))

def residualRole : Residual.ContractibleRole p.FinalRole :=
  ⟨.final, BoundaryFinalRole.contracts⟩

def exactInternal : Residual.ExactInternalRealization p.InternalRole p.InteriorOccurrence :=
  ⟨Spine.realize, Spine.decode p.spine, Spine.realize_decode p.spine, Spine.decode_realize⟩

def faithfulExtension : Residual.FaithfulExtension p.InternalRole p.FinalRole
    p.InteriorOccurrence Unit s.Occurrence (exactInternal (p := p)) (residualRole (p := p)) where
  embedOld := s.old
  embedNew := s.fresh
  oldNewDisjoint := fun _ _ eq => by cases eq
  embedNewInjective := fun a b _ => by cases a; cases b; rfl
  label := s.label
  preservesInternal := fun r => congrArg Sum.inl (Spine.decode_realize r)
  labelFaithful := s.label_faithful

theorem fresh_is_residual (n : Unit) : s.label (s.fresh n) = .inr BoundaryFinalRole.final :=
  s.faithfulExtension.newOccurrence_label_is_residual n

def formation : Formation p.Next p.start s.target :=
  .formed (Formation.deployed p.spine) s.witness

theorem formation_history_exact : s.formation.toHistory = s.history :=
  congrArg (fun h => History.extend h s.witness) (Formation.deployed_exact p.spine)

/-- The final relation is witnessed by this continuation's generated occurrence. -/
structure FinalRealizes (r : p.FinalRole) (o : s.Occurrence) : Type (max u v) where
  roleExact : r = .final
  occurrenceExact : o = s.fresh ()
  stepExact : o.locatedStep = ⟨p.spine.finalNode, s.target, s.witness⟩

def freshRealization : s.FinalRealizes .final (s.fresh ()) := ⟨rfl, rfl, rfl⟩

inductive RealizesFull : p.FullRole → s.Occurrence → Type (max u v)
  | internal (r : p.InternalRole) (o : p.InteriorOccurrence)
      (w : p.InteriorRealizes r o) : RealizesFull (.inl r) (s.old o)
  | final (r : p.FinalRole) (o : s.Occurrence)
      (w : s.FinalRealizes r o) : RealizesFull (.inr r) o

def everyOccurrenceRealized (o : s.Occurrence) : s.RealizesFull (s.label o) o :=
  match o with
  | .last => .final _ _ s.freshRealization
  | .earlier old => .internal _ old (p.interiorRealization.inverseAgreement old)

theorem old_not_final (o : p.InteriorOccurrence) :
    s.FinalRealizes .final (s.old o) → False := by
  intro w
  cases w.occurrenceExact

theorem realization_rigid {r : p.FullRole} {o : s.Occurrence}
    (w : s.RealizesFull r o) : r = s.label o := by
  cases w with
  | internal r old agreement => exact congrArg Sum.inl (p.interior_role_rigid r old agreement)
  | final r o agreement =>
    rw [agreement.occurrenceExact]
    exact congrArg Sum.inr agreement.roleExact

end OneStepContinuation
end RelationalFoundations
