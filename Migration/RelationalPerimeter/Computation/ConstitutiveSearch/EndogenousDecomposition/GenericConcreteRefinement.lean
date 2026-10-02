import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GenericConstitutiveTraversal

/-!
Data-level refinement of the generic exploration by the measured concrete
exploration. The equality includes endpoints, the discovered variable and
relation, the tested prefix, and the number of attempts, not only success.
-/

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT StrongPerimetralTurning

def discoveryAsGeneric (index : Nat)
    (discovery : EndogenousFlipDiscovery (distinctGrowingDiscoveryRoot index)) :
    concreteConstitutiveOperationalInterface.LocalDiscovery index :=
  ⟨((scheduleFromDiscovery discovery).entry.source,
    (scheduleFromDiscovery discovery).entry.target),
    ⟨discovery.var, discovery.relation⟩⟩

def recordedAsGeneric (index : Nat)
    (recorded : RecordedDiscoveryOutcome (distinctGrowingDiscoveryRoot index)) :
    concreteConstitutiveOperationalInterface.Exploration index :=
  ⟨recorded.discovered?.map (discoveryAsGeneric index),
    recorded.testedCandidates, recorded.attempts⟩

theorem concreteDiscover_measured (index candidate : Nat) :
    concreteOperationalDiscover index candidate =
      (tryMeasuredCandidate (distinctGrowingDiscoveryRoot index) candidate).produced?.map
        (fun produced => discoveryAsGeneric index ⟨candidate, produced.discovery⟩) := by
  have same := tryMeasuredCandidate_exact (distinctGrowingDiscoveryRoot index) candidate
  unfold MeasuredCandidateRun.result at same
  unfold concreteOperationalDiscover
  rw [← same]
  cases (tryMeasuredCandidate (distinctGrowingDiscoveryRoot index) candidate).produced? <;> rfl

/-- The generic explorer and the concrete instrumented explorer return the same data. -/
theorem genericExploration_refined (index : Nat) (candidates : List Var) :
    concreteConstitutiveOperationalInterface.explore index candidates =
      recordedAsGeneric index
        (exploreRecordedCandidates (distinctGrowingDiscoveryRoot index) candidates) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    erw [ConstitutiveOperationalInterface.explore.eq_def]
    dsimp only
    erw [concreteDiscover_measured, exploreRecordedCandidates]
    cases (tryMeasuredCandidate (distinctGrowingDiscoveryRoot index) candidate).produced? with
    | none => erw [ih]; rfl
    | some produced => rfl

/-- Realization and extraction agree before either explorer is run. -/
theorem genericStageDiscovery_refined (depth : Nat) :
    concreteConstitutiveOperationalInterface.discoverState (constitutedEndpoint depth) =
      recordedAsGeneric (constitutedSearchIndex depth)
        (stageRecordedDiscoveryRun depth).outcome :=
  genericExploration_refined _ _

/-- Every discovery retained by an executed stage is the generic explorer's result. -/
theorem executedStage_genericDiscovery {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (concreteConstitutiveOperationalInterface.discoverState
      (constitutedEndpoint (depth + 1))).result =
        some (discoveryAsGeneric (constitutedSearchIndex (depth + 1)) run.discovery) := by
  rw [genericStageDiscovery_refined]
  change ((stageRecordedDiscoveryRun (depth + 1)).outcome.discovered?.map _) = _
  rw [run.discoveryExact]
  rfl

/-- The generic action is precisely the action of the code returned and applied. -/
theorem executedStage_genericAction {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    run.application.output.1 =
      Assignment.flipAt run.discovery.var input.assignment := by
  have applied := sequentialStage_next_from_input run
  rw [run.nextAssignmentExact, run.scheduleExact] at applied
  exact applied

/-- The equality also holds at the endpoint actually retained by generation. -/
theorem executedStage_producedGenericDiscovery
    {depth : Nat} {input : SequentialAssignment depth} (run : SequentialStageRun depth input) :
    HEq (concreteConstitutiveOperationalInterface.discoverState run.generation.target).result
      (some (discoveryAsGeneric (constitutedSearchIndex (depth + 1)) run.discovery)) := by
  rw [run.generation.targetExact]
  exact heq_of_eq (executedStage_genericDiscovery run)

/-- Refinement evidence follows every stage of the executed history. -/
inductive GenericRefinedHistory :
    {depth count : Nat} → {input : SequentialAssignment depth} →
      SequentialHistory depth input count → Prop where
  | nil (depth : Nat) (input : SequentialAssignment depth) :
      GenericRefinedHistory (.nil depth input)
  | step {depth count : Nat} {input : SequentialAssignment depth}
      (head : SequentialStageRun depth input)
      (tail : SequentialHistory (depth + 1) head.next count)
      (headExact : HEq
        (concreteConstitutiveOperationalInterface.discoverState head.generation.target).result
        (some (discoveryAsGeneric (constitutedSearchIndex (depth + 1)) head.discovery)))
      (tailExact : GenericRefinedHistory tail) : GenericRefinedHistory (.step head tail)

theorem executedHistory_genericRefinement {depth count : Nat}
    {input : SequentialAssignment depth} (history : SequentialHistory depth input count) :
    GenericRefinedHistory history := by
  induction history with
  | nil depth input => exact .nil depth input
  | step head tail ih => exact .step head tail (executedStage_producedGenericDiscovery head) ih

namespace ConstitutiveOperationalInterface

/-- Append discovered histories without composing their local operational endpoints. -/
def DiscoveredHistory.append (I : ConstitutiveOperationalInterface)
    {source middle target : I.ConstitutiveState}
    {first : History I.ConstitutiveGenerator source middle}
    {second : History I.ConstitutiveGenerator middle target}
    (left : I.DiscoveredHistory first) (right : I.DiscoveredHistory second) :
    I.DiscoveredHistory (first.append second) :=
  match right with
  | .root => left
  | .extend step previous relation found =>
    .extend step (DiscoveredHistory.append I left previous) relation found

/-- Evidence stores precisely the witnesses returned by generic discovery. -/
theorem discoverHistory_of_discovered (I : ConstitutiveOperationalInterface)
    {source target : I.ConstitutiveState}
    {history : History I.ConstitutiveGenerator source target}
    (discovered : I.DiscoveredHistory history) : I.discoverHistory history = some discovered := by
  induction discovered with
  | root => rfl
  | extend step previous relation found ih =>
    rw [discoverHistory, ih]
    dsimp only
    split
    · rename_i failed
      rw [found] at failed
      cases failed
    · rename_i returned returnedExact
      have same : returned = relation := Option.some.inj (Eq.trans returnedExact.symm found)
      cases same
      rfl

end ConstitutiveOperationalInterface

/-- Retain the produced generator; only its endpoint index is transported. -/
def CanonicalStageGeneration.asGenericStep {depth : Nat} (generation : CanonicalStageGeneration depth) :
    GeneratedStep (constitutedEndpoint depth) (constitutedEndpoint (depth + 1)) :=
  Eq.rec (motive := fun target _ => GeneratedStep (constitutedEndpoint depth) target)
    generation.generated generation.targetExact

def CanonicalGeneratedHistory.asGeneric : {depth count : Nat} →
    CanonicalGeneratedHistory depth count →
    History GeneratedStep (constitutedEndpoint depth) (constitutedEndpoint (advancedDepth depth count))
  | _, _, .nil _ => .root
  | _, _, .step generation tail =>
    History.append (.extend .root generation.asGenericStep) tail.asGeneric

/-- Forget operational fields, retaining exactly the generators stored by execution. -/
def SequentialHistory.generatedHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → CanonicalGeneratedHistory depth count
  | _, _, _, .nil depth _ => .nil depth
  | _, _, _, .step head tail => .step head.generation tail.generatedHistory

theorem executedGeneratedHistory_retains_generators {depth count : Nat}
    (generated : CanonicalGeneratedHistory depth count) (input : SequentialAssignment depth) :
    (executeGeneratedHistory generated input).generatedHistory = generated := by
  induction generated with
  | nil => rfl
  | step generation tail ih =>
    change CanonicalGeneratedHistory.step generation
      (executeGeneratedHistory tail _).generatedHistory = .step generation tail
    rw [ih]

/-- Populate the generic history with the very discoveries retained by execution. -/
def SequentialHistory.genericDiscovered : {depth count : Nat} → {input : SequentialAssignment depth} →
    (history : SequentialHistory depth input count) →
    concreteConstitutiveOperationalInterface.DiscoveredHistory history.generatedHistory.asGeneric
  | _, _, _, .nil _ _ => .root
  | depth, _, _, .step head tail =>
    ConstitutiveOperationalInterface.DiscoveredHistory.append concreteConstitutiveOperationalInterface
      (.extend head.generation.asGenericStep .root
        (discoveryAsGeneric (constitutedSearchIndex (depth + 1)) head.discovery)
        (executedStage_genericDiscovery head)) tail.genericDiscovered

theorem executedHistory_genericTraversal {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    concreteConstitutiveOperationalInterface.discoverHistory history.generatedHistory.asGeneric =
      some history.genericDiscovered :=
  ConstitutiveOperationalInterface.discoverHistory_of_discovered _ _

/-- The discovered and executed action changes the incoming assignment.
This is about the produced operational object, not an artificial requirement
that every subsequent Boolean decision must change. -/
theorem executedStage_output_not_input {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : run.application.output.1 ≠ input.assignment := by
  intro unchanged
  have action := executedStage_genericAction run
  have assignmentSame := Eq.trans action.symm unchanged
  have bitSame := congrArg (fun assignment : Assignment => assignment run.discovery.var) assignmentSame
  unfold Assignment.flipAt at bitSame
  rw [if_pos rfl] at bitSame
  cases value : input.assignment run.discovery.var <;> rw [value] at bitSame <;> cases bitSame

theorem executedStage_next_not_input {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : run.next.assignment ≠ input.assignment := by
  rw [run.nextAssignmentExact]
  exact executedStage_output_not_input run

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.discoveryAsGeneric
#print axioms ConstitutiveSearch.EndogenousDecomposition.recordedAsGeneric
#print axioms ConstitutiveSearch.EndogenousDecomposition.concreteDiscover_measured
#print axioms ConstitutiveSearch.EndogenousDecomposition.genericExploration_refined
#print axioms ConstitutiveSearch.EndogenousDecomposition.genericStageDiscovery_refined
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStage_genericDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStage_genericAction
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStage_producedGenericDiscovery
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_genericRefinement
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.DiscoveredHistory.append
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalInterface.discoverHistory_of_discovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.CanonicalStageGeneration.asGenericStep
#print axioms ConstitutiveSearch.EndogenousDecomposition.CanonicalGeneratedHistory.asGeneric
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.generatedHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedGeneratedHistory_retains_generators
#print axioms ConstitutiveSearch.EndogenousDecomposition.SequentialHistory.genericDiscovered
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedHistory_genericTraversal
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStage_output_not_input
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStage_next_not_input
/- AXIOM_AUDIT_END -/
