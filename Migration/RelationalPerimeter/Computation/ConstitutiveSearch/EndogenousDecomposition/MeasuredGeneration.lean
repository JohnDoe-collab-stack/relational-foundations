import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.GeneratedHistoryExecution

namespace ConstitutiveSearch.EndogenousDecomposition

open StrongPerimetralTurning StrongPerimetralTurning.Example

/-- Generation-call counts are emitted by the producer, not inferred from a
finished stage. They are not a count of all internal representation operations. -/
structure ConstitutiveInitializationRun (depth : Nat) where
  history : RootedGeneratedHistory examplePresentation
  historyExact : history = constitutedHistory depth
  generateCalls : Nat
  appendedSteps : Nat
  provenanceUnits : Nat
  certificatesProduced : Nat
  perimeterDeployments : Nat

def initializeConstitutiveHistory : (depth : Nat) → ConstitutiveInitializationRun depth
  | 0 => ⟨perimeterDeployment examplePresentation, rfl, 0, 0, 0, 0, 1⟩
  | depth + 1 =>
    let prior := initializeConstitutiveHistory depth
    let produced := generate prior.history.endpoint
    { history := appendGenerated prior.history produced
      historyExact := by
        change appendGenerated prior.history (generate prior.history.endpoint) = _
        rw [prior.historyExact]
        rfl
      generateCalls := prior.generateCalls + 1
      appendedSteps := prior.appendedSteps + 1
      provenanceUnits := prior.provenanceUnits + 1
      certificatesProduced := prior.certificatesProduced + 1
      perimeterDeployments := prior.perimeterDeployments }

theorem initializeConstitutiveHistory_counts (depth : Nat) :
    (initializeConstitutiveHistory depth).generateCalls = depth ∧
    (initializeConstitutiveHistory depth).appendedSteps = depth ∧
    (initializeConstitutiveHistory depth).perimeterDeployments = 1 := by
  induction depth with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ depth ih =>
    exact ⟨congrArg (fun n => n + 1) ih.1, congrArg (fun n => n + 1) ih.2.1, ih.2.2⟩

theorem initializeConstitutiveHistory_material_counts (depth : Nat) :
    (initializeConstitutiveHistory depth).provenanceUnits = depth ∧
      (initializeConstitutiveHistory depth).certificatesProduced = depth := by
  induction depth with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth ih =>
      exact ⟨congrArg (fun n => n + 1) ih.1, congrArg (fun n => n + 1) ih.2⟩

structure ConstitutiveProductionRun (depth count : Nat) where
  history : CanonicalGeneratedHistory depth count
  historyExact : history = produceCanonicalGeneratedHistory depth count
  generateCalls : Nat
  appendedSteps : Nat
  provenanceUnits : Nat
  certificatesProduced : Nat

/-- Every recursive producer consumes its predecessor's actual target. -/
def produceMeasuredConstitutiveHistory (depth count : Nat)
    (source : PositiveConstitution examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    ConstitutiveProductionRun depth count :=
  match count with
  | 0 => ⟨.nil depth, rfl, 0, 0, 0, 0⟩
  | count + 1 =>
    let generated := generateCanonicalStageFromSource source sourceExact
    let tail := produceMeasuredConstitutiveHistory (depth + 1) count generated.target generated.targetExact
    { history := .step generated tail.history
      historyExact := by
        rw [tail.historyExact]
        dsimp only [generated]
        rw [generateCanonicalStageFromSource_exact]
        rfl
      generateCalls := tail.generateCalls + generated.generateCalls
      appendedSteps := tail.appendedSteps + generated.generatedSteps
      provenanceUnits := tail.provenanceUnits + generated.provenanceUnits
      certificatesProduced := tail.certificatesProduced + generated.certificatesProduced }

theorem produceMeasuredConstitutiveHistory_counts (depth count : Nat)
    (source : PositiveConstitution examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    (produceMeasuredConstitutiveHistory depth count source sourceExact).generateCalls = count ∧
    (produceMeasuredConstitutiveHistory depth count source sourceExact).appendedSteps = count := by
  induction count generalizing depth source with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    let generated := generateCanonicalStageFromSource source sourceExact
    have tail := ih (depth + 1) generated.target generated.targetExact
    exact ⟨congrArg (fun n => n + 1) tail.1, congrArg (fun n => n + 1) tail.2⟩

theorem produceMeasuredConstitutiveHistory_material_counts (depth count : Nat)
    (source : PositiveConstitution examplePresentation)
    (sourceExact : source = (constructStage depth).history.endpoint) :
    (produceMeasuredConstitutiveHistory depth count source sourceExact).provenanceUnits = count ∧
      (produceMeasuredConstitutiveHistory depth count source sourceExact).certificatesProduced = count := by
  induction count generalizing depth source with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    let generated := generateCanonicalStageFromSource source sourceExact
    have tail := ih (depth + 1) generated.target generated.targetExact
    exact ⟨congrArg (fun n => n + 1) tail.1, congrArg (fun n => n + 1) tail.2⟩

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.initializeConstitutiveHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.initializeConstitutiveHistory_counts
#print axioms ConstitutiveSearch.EndogenousDecomposition.initializeConstitutiveHistory_material_counts
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceMeasuredConstitutiveHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceMeasuredConstitutiveHistory_counts
#print axioms ConstitutiveSearch.EndogenousDecomposition.produceMeasuredConstitutiveHistory_material_counts
/- AXIOM_AUDIT_END -/
