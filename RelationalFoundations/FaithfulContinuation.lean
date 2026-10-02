import RelationalFoundations.BoundaryInterpretation
set_option genInjectivity false

namespace RelationalFoundations
universe u v t i c

/-- The old/new embeddings are the actual history embeddings, not arbitrary parallel carriers. -/
structure FaithfulContinuation (p : CircularPresentation.{u,v,t,i,c})
    {target : p.Node} (positive : History.Positive p.Next p.spine.finalNode target) where
  label : History.Occurrence (History.append p.interiorHistory positive.toHistory) → p.FullRole
  faithful : Function.Injective label
  preserves : ∀ role,
    label (History.embedLeftOccurrence (Spine.realize role) positive.toHistory) = .inl role

namespace FaithfulContinuation
variable {p : CircularPresentation.{u,v,t,i,c}} {target : p.Node}
variable {positive : History.Positive p.Next p.spine.finalNode target}

def extension (context : FaithfulContinuation p positive) :
    Residual.FaithfulExtension p.InternalRole p.FinalRole p.InteriorOccurrence
      (History.Occurrence positive.toHistory)
      (History.Occurrence (History.append p.interiorHistory positive.toHistory))
      (OneStepContinuation.exactInternal (p := p)) (OneStepContinuation.residualRole (p := p)) where
  embedOld := fun old => History.embedLeftOccurrence old positive.toHistory
  embedNew := History.embedRightOccurrence p.interiorHistory
  oldNewDisjoint := fun old new => History.leftRightDisjoint old new
  embedNewInjective := History.embedRightOccurrence_injective p.interiorHistory
  label := context.label
  preservesInternal := context.preserves
  labelFaithful := context.faithful

theorem residual_label (context : FaithfulContinuation p positive)
    (new : History.Occurrence positive.toHistory) :
    context.label (History.embedRightOccurrence p.interiorHistory new) = .inr BoundaryFinalRole.final :=
  context.extension.newOccurrence_label_is_residual new

def exactlyOne (context : FaithfulContinuation p positive) : History.ExactlyOne positive.toHistory :=
  History.exactlyOneOfPositiveAndUnique positive context.extension.newOccurrences_unique

def generatedStep (context : FaithfulContinuation p positive) : OneStepContinuation p :=
  ⟨target, context.exactlyOne.step⟩

theorem history_exact (context : FaithfulContinuation p positive) :
    History.append p.interiorHistory positive.toHistory = context.generatedStep.history := by
  rw [context.exactlyOne.history_exact]
  rfl

def interpretation (context : FaithfulContinuation p positive) : BoundaryInterpretation context.generatedStep :=
  .ofContinuation context.generatedStep

theorem interpreted_history_exact (context : FaithfulContinuation p positive) :
    context.interpretation.formation.toHistory = History.append p.interiorHistory positive.toHistory :=
  context.interpretation.formation_history_exact.trans context.history_exact.symm

def ofOneStep (s : OneStepContinuation p) : FaithfulContinuation p ⟨_, .root, s.witness⟩ where
  label := s.label
  faithful := s.label_faithful
  preserves := fun role => congrArg Sum.inl (Spine.decode_realize role)

theorem ofOneStep_witness_exact (s : OneStepContinuation p) :
    (ofOneStep s).generatedStep.witness = s.witness := rfl

end FaithfulContinuation
end RelationalFoundations
