import RelationalFoundations.Presentation
import RelationalFoundations.ExactRealization
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c
namespace CircularPresentation
variable (p : CircularPresentation.{u,v,t,i,c})

/-- A distinguished occurrence and exact conservation of its actual relational step. -/
structure InteriorRealizes (role : p.InternalRole) (o : p.InteriorOccurrence) : Type (max u v) where
  occurrenceExact : Spine.realize role = o
  stepExact : o.locatedStep = Spine.located role

def interiorRealization : ExactRealization p.InternalRole p.InteriorOccurrence p.InteriorRealizes where
  transport := p.spine.positionTransport
  agreement := fun role => ⟨rfl, Spine.located_realize role⟩

theorem interior_role_rigid : p.interiorRealization.RoleRigid := by
  intro r o w
  exact (Spine.decode_realize r).symm.trans
    (congrArg (Spine.decode p.spine) w.occurrenceExact)

inductive RealizesInteriorFull : p.FullRole → p.InteriorOccurrence → Type (max u v)
  | internal (r : p.InternalRole) (o : p.InteriorOccurrence)
      (agreement : p.InteriorRealizes r o) : RealizesInteriorFull (.inl r) o

def everyInteriorRealized (o : p.InteriorOccurrence) :
    p.RealizesInteriorFull (p.classify o) o :=
  .internal _ _ (p.interiorRealization.inverseAgreement o)

theorem noFinalInterior (o : p.InteriorOccurrence) :
    p.RealizesInteriorFull (.inr BoundaryFinalRole.final) o → False := by
  intro impossible
  cases impossible

theorem fullRole_rigid {r : p.FullRole} {o : p.InteriorOccurrence}
    (agreement : p.RealizesInteriorFull r o) : r = p.classify o := by
  cases agreement with
  | internal r o agreement => exact congrArg Sum.inl (p.interior_role_rigid r o agreement)

/-- A theorem-produced certificate; final exclusion is not an input assumption. -/
structure InteriorDelimitation where
  exact : ExactRealization p.InternalRole p.InteriorOccurrence p.InteriorRealizes
  occurrenceRole : (o : p.InteriorOccurrence) → p.RealizesInteriorFull (p.classify o) o
  excludesFinal : (o : p.InteriorOccurrence) →
    p.RealizesInteriorFull (.inr BoundaryFinalRole.final) o → False
  rigid : ∀ {r o}, p.RealizesInteriorFull r o → r = p.classify o
  exhaustive : (r : p.FullRole) →
    (∃ internal, r = .inl internal) ∨ r = .inr BoundaryFinalRole.final

def delimitInterior : p.InteriorDelimitation :=
  ⟨p.interiorRealization, p.everyInteriorRealized, p.noFinalInterior,
    p.fullRole_rigid, p.fullRole_cases⟩

end CircularPresentation
end RelationalFoundations
