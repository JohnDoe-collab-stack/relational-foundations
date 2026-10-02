import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredStateConstruction
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

namespace ConstitutiveSearch.EndogenousDecomposition

open SAT

structure MeasuredRelationRun {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) where
  result : Option (GeneratedStructuralFlipAtRelation selected source target)
  formulaTransform : ComparisonWork
  formulaComparison : ComparisonWork
  historyTransform : ComparisonWork
  historyComparison : ComparisonWork

def MeasuredRelationRun.work {root : Cnf} {selected : Var}
    {source target : GeneratedStructuralBranchContext root}
    (run : MeasuredRelationRun selected source target) : ComparisonWork :=
  ((run.formulaTransform.add run.formulaComparison).add run.historyTransform).add
    run.historyComparison

/-- Every branch uses the result of the very comparison which emits its work. -/
def searchMeasuredRelation {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) :
    MeasuredRelationRun selected source target :=
  let flippedFormula := flipMeasuredCnf selected source.context.formula
  let formulas := compareMeasuredCnf target.context.formula flippedFormula.value
  match formulas.result with
  | .isFalse _ => ⟨none, flippedFormula.work, formulas.work, .zero, .zero⟩
  | .isTrue sameFormula =>
    let flippedHistory := flipMeasuredHistory selected source.context.decisions
    let histories := compareMeasuredHistory target.context.decisions flippedHistory.value
    match histories.result with
    | .isFalse _ =>
      ⟨none, flippedFormula.work, formulas.work, flippedHistory.work, histories.work⟩
    | .isTrue sameHistory =>
      ⟨some ⟨Eq.trans sameFormula flippedFormula.valueExact,
        Eq.trans sameHistory flippedHistory.valueExact⟩,
        flippedFormula.work, formulas.work, flippedHistory.work, histories.work⟩

theorem searchMeasuredRelation_exact {root : Cnf} (selected : Var)
    (source target : GeneratedStructuralBranchContext root) :
    (searchMeasuredRelation selected source target).result =
      (generatedStructuralFlipAtSearch root selected).find source target := by
  unfold searchMeasuredRelation
  dsimp only
  split
  · rename_i different _
    have mismatch : target.context.formula ≠ Cnf.flipAt selected source.context.formula := by
      intro same
      exact different (Eq.trans same (flipMeasuredCnf selected source.context.formula).valueExact.symm)
    dsimp only [generatedStructuralFlipAtSearch]
    rw [dif_neg mismatch]
  · rename_i same _
    have formulaExact := Eq.trans same (flipMeasuredCnf selected source.context.formula).valueExact
    split
    · rename_i different _
      have mismatch : target.context.decisions ≠
          flipStructuralDecisionsAt selected source.context.decisions := by
        intro equal
        exact different (Eq.trans equal
          (flipMeasuredHistory selected source.context.decisions).valueExact.symm)
      dsimp only [generatedStructuralFlipAtSearch]
      rw [dif_pos formulaExact, dif_neg mismatch]
    · rename_i sameHistory _
      have historyExact := Eq.trans sameHistory
        (flipMeasuredHistory selected source.context.decisions).valueExact
      dsimp only [generatedStructuralFlipAtSearch]
      rw [dif_pos formulaExact, dif_pos historyExact]

def searchMeasuredRelationFromData {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) :
    MeasuredRelationRun selected source target :=
  let searched := searchMeasuredRelation selected left.value right.value
  let reindexedSource := Eq.rec
    (motive := fun source _ => MeasuredRelationRun selected source right.value)
    searched left.valueExact
  Eq.rec (motive := fun target _ => MeasuredRelationRun selected source target)
    reindexedSource right.valueExact

theorem searchMeasuredRelationFromData_exact {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) :
    (searchMeasuredRelationFromData selected left right).result =
      (generatedStructuralFlipAtSearch root selected).find source target := by
  cases left with
  | mk left leftExact leftWork =>
    cases leftExact
    cases right with
    | mk right rightExact rightWork =>
      cases rightExact
      exact searchMeasuredRelation_exact selected _ _

theorem searchMeasuredRelationFromData_preserves_work {root : Cnf} (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (left : MeasuredValue source) (right : MeasuredValue target) :
    (searchMeasuredRelationFromData selected left right).work =
      (searchMeasuredRelation selected left.value right.value).work := by
  cases left with
  | mk left leftExact leftWork =>
    cases leftExact
    cases right with
    | mk right rightExact rightWork => cases rightExact; rfl

/-- Successful discovery retains the endpoints produced while trying its variable. -/
structure ProducedFlipCandidate {root : Cnf}
    (state : GeneratedStructuralBranchContext root) (candidate : Var) where
  discovery : CandidateFlipDiscovery state candidate
  source : MeasuredValue (state.child candidate false discovery.fresh)
  target : MeasuredValue (state.child candidate true discovery.fresh)

def ProducedFlipCandidate.entry {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {candidate : Var}
    (produced : ProducedFlipCandidate state candidate) : ConstitutedLocalWitness root :=
  { var := candidate
    source := produced.source.value
    target := produced.target.value
    relation := by
      rw [produced.source.valueExact, produced.target.valueExact]
      exact produced.discovery.relation }

theorem ProducedFlipCandidate.entry_exact {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {candidate : Var}
    (produced : ProducedFlipCandidate state candidate) :
    produced.entry = (scheduleFromDiscovery ⟨candidate, produced.discovery⟩).entry := by
  cases produced with
  | mk discovery source target =>
    cases source with
    | mk source sourceExact sourceWork =>
      cases sourceExact
      cases target with
      | mk target targetExact targetWork => cases targetExact; rfl

structure MeasuredCandidateRun {root : Cnf}
    (state : GeneratedStructuralBranchContext root) (candidate : Var) where
  produced? : Option (ProducedFlipCandidate state candidate)
  freshnessWork : ComparisonWork
  constructionWork : ComparisonWork
  relationWork : ComparisonWork

def MeasuredCandidateRun.result {root : Cnf}
    {state : GeneratedStructuralBranchContext root} {candidate : Var}
    (run : MeasuredCandidateRun state candidate) : Option (CandidateFlipDiscovery state candidate) :=
  run.produced?.map (fun produced => produced.discovery)

/-- Freshness is checked before any endpoints or relations are constructed. -/
def tryMeasuredCandidate {root : Cnf}
    (state : GeneratedStructuralBranchContext root) (candidate : Var) :
    MeasuredCandidateRun state candidate :=
  let freshness := checkMeasuredFreshness candidate state.context.decisions
  match fresh : freshness.value with
  | false => ⟨none, freshness.work, .zero, .zero⟩
  | true =>
    let checked := structuralDecisionsAvoid_of_check_true candidate state.context.decisions
      (Eq.trans freshness.valueExact.symm fresh)
    let left := constructMeasuredChild state candidate false checked
    let right := constructMeasuredChild state candidate true checked
    let searched := searchMeasuredRelationFromData candidate left right
    match searched.result with
    | none => ⟨none, freshness.work, left.work.add right.work, searched.work⟩
    | some relation =>
      ⟨some ⟨⟨checked, relation⟩, left, right⟩,
        freshness.work, left.work.add right.work, searched.work⟩

theorem tryMeasuredCandidate_exact {root : Cnf}
    (state : GeneratedStructuralBranchContext root) (candidate : Var) :
    (tryMeasuredCandidate state candidate).result = tryEndogenousFlipCandidate state candidate := by
  unfold MeasuredCandidateRun.result
  unfold tryEndogenousFlipCandidate
  split
  · rename_i failed
    unfold tryMeasuredCandidate
    dsimp only
    split
    · rfl
    · rename_i success
      have check := Eq.trans (checkMeasuredFreshness candidate state.context.decisions).valueExact.symm success
      rw [failed] at check
      cases check
  · rename_i success
    unfold tryMeasuredCandidate
    dsimp only
    split
    · rename_i failed
      have check := Eq.trans (checkMeasuredFreshness candidate state.context.decisions).valueExact.symm failed
      rw [success] at check
      cases check
    · rw [searchMeasuredRelationFromData_exact]
      split <;> rename_i returned <;> rw [returned] <;> rfl

end ConstitutiveSearch.EndogenousDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelation_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.tryMeasuredCandidate
#print axioms ConstitutiveSearch.EndogenousDecomposition.tryMeasuredCandidate_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelationFromData
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelationFromData_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.searchMeasuredRelationFromData_preserves_work
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedFlipCandidate.entry
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedFlipCandidate.entry_exact
/- AXIOM_AUDIT_END -/
