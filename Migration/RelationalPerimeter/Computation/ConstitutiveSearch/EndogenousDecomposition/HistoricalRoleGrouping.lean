import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
open SAT RelationalFoundations RelationalFoundations.CertifiedGrouping

/-- The old executed heads are shared verbatim. At its end, the inclusion uses
a positively supplied profile of the newly produced suffix. Existing licences
are retained; a pending head may receive a newly supplied local licence. -/
inductive Historical :
    {oldCount newCount : Nat} → {source : CausalConstitutiveState} →
    {oldRun : CausalConstitutiveExecutionHistory oldCount source} →
    {newRun : CausalConstitutiveExecutionHistory newCount source} →
    {oldRoles : RelationalConstitutiveRoleHistory oldRun} →
    {newRoles : RelationalConstitutiveRoleHistory newRun} →
    RoleStatus.History oldRoles → RoleStatus.History newRoles → Type 2 where
  | suffix {newCount : Nat} {source : CausalConstitutiveState}
      {newRun : CausalConstitutiveExecutionHistory newCount source}
      {newRoles : RelationalConstitutiveRoleHistory newRun}
      (history : RoleStatus.History newRoles) (produced : RoleOccurrenceProfile newRoles) :
      Historical (.nil (state := source)) history
  | same {oldCount newCount : Nat} {source : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution source}
      {oldRun : CausalConstitutiveExecutionHistory oldCount head.next}
      {newRun : CausalConstitutiveExecutionHistory newCount head.next}
      {role : RelationalConstitutiveRoleStage head}
      {oldRoles : RelationalConstitutiveRoleHistory oldRun} {newRoles : RelationalConstitutiveRoleHistory newRun}
      {old : RoleStatus.History oldRoles} {new : RoleStatus.History newRoles}
      (status : RoleStatus.Status role) (rest : Historical old new) :
      Historical (oldRoles := .step role oldRoles) (newRoles := .step role newRoles)
        (.step status old) (.step status new)
  | license {oldCount newCount : Nat} {source : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution source}
      {oldRun : CausalConstitutiveExecutionHistory oldCount head.next}
      {newRun : CausalConstitutiveExecutionHistory newCount head.next}
      {role : RelationalConstitutiveRoleStage head}
      {oldRoles : RelationalConstitutiveRoleHistory oldRun} {newRoles : RelationalConstitutiveRoleHistory newRun}
      {old : RoleStatus.History oldRoles} {new : RoleStatus.History newRoles}
      (transport : AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
        (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right))
      (rest : Historical old new) :
      Historical (oldRoles := .step role oldRoles) (newRoles := .step role newRoles)
        (.step none old) (.step (some transport) new)
  | composed {firstCount middleCount lastCount : Nat} {source : CausalConstitutiveState}
      {firstRun : CausalConstitutiveExecutionHistory firstCount source}
      {middleRun : CausalConstitutiveExecutionHistory middleCount source}
      {lastRun : CausalConstitutiveExecutionHistory lastCount source}
      {firstRoles : RelationalConstitutiveRoleHistory firstRun}
      {middleRoles : RelationalConstitutiveRoleHistory middleRun}
      {lastRoles : RelationalConstitutiveRoleHistory lastRun}
      {first : RoleStatus.History firstRoles} {middle : RoleStatus.History middleRoles} {last : RoleStatus.History lastRoles}
      (one : Historical first middle) (two : Historical middle last) : Historical first last

namespace Historical
variable {oldCount newCount : Nat} {source : CausalConstitutiveState}
    {oldRun : CausalConstitutiveExecutionHistory oldCount source}
    {newRun : CausalConstitutiveExecutionHistory newCount source}
    {oldRoles : RelationalConstitutiveRoleHistory oldRun} {newRoles : RelationalConstitutiveRoleHistory newRun}
    {old : RoleStatus.History oldRoles} {new : RoleStatus.History newRoles}

def embedding : {oldCount newCount : Nat} → {source : CausalConstitutiveState} →
    {oldRun : CausalConstitutiveExecutionHistory oldCount source} →
    {newRun : CausalConstitutiveExecutionHistory newCount source} →
    {oldRoles : RelationalConstitutiveRoleHistory oldRun} → {newRoles : RelationalConstitutiveRoleHistory newRun} →
    {old : RoleStatus.History oldRoles} → {new : RoleStatus.History newRoles} → 
    Historical old new → RoleOccurrenceProfile oldRoles → RoleOccurrenceProfile newRoles
  | _, _, _, _, _, _, _, _, _, .suffix _ produced, _ => produced
  | _, _, _, _, _, _, _, _, _, .same _ rest, p => (p.1, embedding rest p.2)
  | _, _, _, _, _, _, _, _, _, .license _ rest, p => (p.1, embedding rest p.2)
  | _, _, _, _, _, _, _, _, _, .composed one two, p => embedding two (embedding one p)

def codedEmbedding : {oldCount newCount : Nat} → {source : CausalConstitutiveState} →
    {oldRun : CausalConstitutiveExecutionHistory oldCount source} →
    {newRun : CausalConstitutiveExecutionHistory newCount source} →
    {oldRoles : RelationalConstitutiveRoleHistory oldRun} → {newRoles : RelationalConstitutiveRoleHistory newRun} →
    {old : RoleStatus.History oldRoles} → {new : RoleStatus.History newRoles} → 
    Historical old new → Binary.Profile (roleShape oldRoles) → Binary.Profile (roleShape newRoles)
  | _, _, _, _, _, _, _, _, _, .suffix _ produced, _ => encode _ produced
  | _, _, _, _, _, _, _, _, _, .same _ rest, p => (p.1, codedEmbedding rest p.2)
  | _, _, _, _, _, _, _, _, _, .license _ rest, p => (p.1, codedEmbedding rest p.2)
  | _, _, _, _, _, _, _, _, _, .composed one two, p => codedEmbedding two (codedEmbedding one p)


theorem code_embedding (extension : Historical old new) (p : RoleOccurrenceProfile oldRoles) :
    encode newRoles (extension.embedding p) = extension.codedEmbedding (encode oldRoles p) := by
  induction extension with
  | suffix => rfl
  | same status rest ih => exact Prod.ext rfl (ih p.2)
  | license transport rest ih => exact Prod.ext rfl (ih p.2)
  | composed one two ihOne ihTwo => exact (ihTwo _).trans (congrArg two.codedEmbedding (ihOne p))

theorem embedding_injective (extension : Historical old new) (p q : RoleOccurrenceProfile oldRoles)
    (same : extension.embedding p = extension.embedding q) : p = q := by
  induction extension with
  | suffix => cases p; cases q; rfl
  | same status rest ih =>
      have head := congrArg Prod.fst same
      have tail := congrArg Prod.snd same
      exact Prod.ext head (ih p.2 q.2 tail)
  | composed one two ihOne ihTwo => exact ihOne p q (ihTwo _ _ same)
  | license transport rest ih =>
      have head := congrArg Prod.fst same
      have tail := congrArg Prod.snd same
      exact Prod.ext head (ih p.2 q.2 tail)

def liftMove : {oldCount newCount : Nat} → {source : CausalConstitutiveState} →
    {oldRun : CausalConstitutiveExecutionHistory oldCount source} →
    {newRun : CausalConstitutiveExecutionHistory newCount source} →
    {oldRoles : RelationalConstitutiveRoleHistory oldRun} → {newRoles : RelationalConstitutiveRoleHistory newRun} →
    {old : RoleStatus.History oldRoles} → {new : RoleStatus.History newRoles} → 
    (extension : Historical old new) → {p q : Binary.Profile (roleShape oldRoles)} →
    Binary.Move (mask old) p q →
    Binary.Move (mask new) (extension.codedEmbedding p) (extension.codedEmbedding q)
  | _, _, _, _, _, _, _, _, _, .suffix _ _, _, _, step => nomatch step
  | _, _, _, _, _, _, _, _, _, .same none rest, _, _, step =>
      match step with
      | .tail child => .tail (liftMove rest child)
  | _, _, _, _, _, _, _, _, _, .same (some _) rest, _, _, step =>
      match step with
      | .head => .head
      | .tail child => .tail (liftMove rest child)
  | _, _, _, _, _, _, _, _, _, .license _ rest, _, _, step =>
      match step with
      | .tail child => .tail (liftMove rest child)
  | _, _, _, _, _, _, _, _, _, .composed one two, _, _, step => liftMove two (liftMove one step)


def extension (historical : Historical old new) : Extension (rules old) (rules new) where
  embedding := historical.embedding
  lift := by
    intro p q step
    apply Trace.one
    change ULift (Binary.Move (mask new) (encode newRoles (historical.embedding p))
      (encode newRoles (historical.embedding q)))
    rw [historical.code_embedding p, historical.code_embedding q]
    exact ⟨historical.liftMove step.down⟩

theorem renormalized (historical : Historical old new) (p : RoleOccurrenceProfile oldRoles) :
    new.selected (historical.embedding (old.selected p)) = new.selected (historical.embedding p) := by
  have exact := historical.extension.renormalized p
  change (rules new).normal (historical.embedding ((rules old).normal p)) = (rules new).normal (historical.embedding p) at exact
  rw [normal_selected old p, normal_selected new _, normal_selected new _] at exact
  exact exact

def identity : {count : Nat} → {source : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count source} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → Historical history history
  | _, _, _, _, .nil => .suffix .nil ()
  | _, _, _, _, .step status rest => .same status (identity rest)

def compose {firstCount middleCount lastCount : Nat} {source : CausalConstitutiveState}
    {firstRun : CausalConstitutiveExecutionHistory firstCount source}
    {middleRun : CausalConstitutiveExecutionHistory middleCount source}
    {lastRun : CausalConstitutiveExecutionHistory lastCount source}
    {firstRoles : RelationalConstitutiveRoleHistory firstRun}
    {middleRoles : RelationalConstitutiveRoleHistory middleRun}
    {lastRoles : RelationalConstitutiveRoleHistory lastRun}
    {first : RoleStatus.History firstRoles} {middle : RoleStatus.History middleRoles} {last : RoleStatus.History lastRoles}
    (one : Historical first middle) (two : Historical middle last) : Historical first last :=
  .composed one two

theorem embedding_composes {firstCount middleCount lastCount : Nat} {source : CausalConstitutiveState}
    {firstRun : CausalConstitutiveExecutionHistory firstCount source}
    {middleRun : CausalConstitutiveExecutionHistory middleCount source}
    {lastRun : CausalConstitutiveExecutionHistory lastCount source}
    {firstRoles : RelationalConstitutiveRoleHistory firstRun}
    {middleRoles : RelationalConstitutiveRoleHistory middleRun}
    {lastRoles : RelationalConstitutiveRoleHistory lastRun}
    {first : RoleStatus.History firstRoles} {middle : RoleStatus.History middleRoles} {last : RoleStatus.History lastRoles}
    (one : Historical first middle) (two : Historical middle last) (p : RoleOccurrenceProfile firstRoles) :
    (one.compose two).embedding p = two.embedding (one.embedding p) := rfl

theorem obligation_composes {firstCount middleCount lastCount : Nat} {source : CausalConstitutiveState}
    {firstRun : CausalConstitutiveExecutionHistory firstCount source}
    {middleRun : CausalConstitutiveExecutionHistory middleCount source}
    {lastRun : CausalConstitutiveExecutionHistory lastCount source}
    {firstRoles : RelationalConstitutiveRoleHistory firstRun}
    {middleRoles : RelationalConstitutiveRoleHistory middleRun}
    {lastRoles : RelationalConstitutiveRoleHistory lastRun}
    {first : RoleStatus.History firstRoles} {middle : RoleStatus.History middleRoles} {last : RoleStatus.History lastRoles}
    (one : Historical first middle) (two : Historical middle last) (p : Extension.Obligation (rules first)) :
    two.extension.obligation (one.extension.obligation p) = (one.compose two).extension.obligation p := by
  apply Subtype.ext
  exact two.extension.renormalized (one.embedding p.1)

def executedSuffix {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program) :
    Historical (.nil (state := state)) (RoleStatus.executed reduction) :=
  .suffix (RoleStatus.executed reduction) (retainedRoleProfile reduction)

def returnedGrowth {count : Nat} {state : CausalConstitutiveState} {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next} {role : RelationalConstitutiveRoleStage head}
    {roles : RelationalConstitutiveRoleHistory tail} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) (rest : RoleStatus.History roles) :
    Historical (oldRoles := .step role roles) (newRoles := .step role roles)
      (.step none rest) (.step (some (RoleStatus.returnedTransport license)) rest) :=
  .license (RoleStatus.returnedTransport license) (identity rest)

end Historical
end ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.embedding
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.codedEmbedding
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.embedding_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.liftMove
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.extension
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.renormalized
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.compose
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.embedding_composes
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.obligation_composes
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.executedSuffix
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.returnedGrowth
/- AXIOM_AUDIT_END -/
