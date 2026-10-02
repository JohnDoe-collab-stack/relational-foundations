import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.LocalOperationalStatus
import RelationalPerimeter.Computation.ConstitutiveSearch.ProducedOutputImage

/-!
# Prefix-local operational production

Its producer can receive only the stage that has just been executed. No future
tail, completed history, remaining-stage count or post-hoc readout occurs in
the producer's type.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive

/-- Causal local license for absorbing the transformed occurrence. -/
structure ExecutedRoleReductionLicense
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (atom : RoleStageAtom role) where
  private mk ::
  transformedOccurrence : RoleConstitutedOccurrence role
  transformedOccurrenceExact :
    transformedOccurrence = roleConstitutedOccurrenceAt role .left
  transformedConstitution :
    RoleConstitutionEvidence role transformedOccurrence
  retainedOccurrence : RoleConstitutedOccurrence role
  retainedOccurrenceExact :
    retainedOccurrence = roleConstitutedOccurrenceAt role .right
  retainedConstitution :
    RoleConstitutionEvidence role retainedOccurrence
  transformedOutputExact :
    interpretRoleStageAtom atom
        transformedOccurrence
        transformedConstitution
        (transformedOccurrenceExact ▸ role.executedInput) =
      role.completedOutput
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation)
  transformedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (interpretRoleStageAtom atom
        transformedOccurrence
        transformedConstitution
        (transformedOccurrenceExact ▸ role.executedInput))
  retainedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      role.completedOutput
  actionChangesSource :
    (atom.action role.executedInput).1 ≠ role.executedInput.1
  occurrencesRemainDistinct :
    transformedOccurrence ≠ retainedOccurrence

/-- Canonical license; every field is discharged by the executed role. -/
def executedRoleReductionLicense
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ExecutedRoleReductionLicense role (compileRoleStageAtom role) :=
  { transformedOccurrence := roleConstitutedOccurrenceAt role .left
    transformedOccurrenceExact := rfl
    transformedConstitution :=
      roleConstitutionEvidence role (roleConstitutedOccurrenceAt role .left)
    retainedOccurrence := roleConstitutedOccurrenceAt role .right
    retainedOccurrenceExact := rfl
    retainedConstitution :=
      roleConstitutionEvidence role (roleConstitutedOccurrenceAt role .right)
    transformedOutputExact := by
      exact Eq.trans
        (interpretCompiledRoleStage_left role role.executedInput)
        role.actionExact.symm
    preservesCriterion := (compileRoleStageAtom role).preservesAccepted
    transformedAccepted := by
      exact (compileRoleStageAtom role).preservesAccepted
        role.executedInput
        (role.executedInputExact ▸ run.sourceAccepted)
    retainedAccepted := role.preservation
    actionChangesSource := by
      rw [role.executedInputExact]
      exact compiledRoleStage_action_changes_executed_source run role
    occurrencesRemainDistinct :=
      (fun same => openingRolePosition_left_ne_right role
        (congrArg
          (fun occurrence : RoleConstitutedOccurrence role =>
            occurrence.position)
          same)) }

/-- The local map applies the actual instruction to each canonical input. -/
def producedRoleOutput
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role) (occurrence : RoleConstitutedOccurrence role) :=
  interpretRoleStageAtom atom occurrence (roleConstitutionEvidence role occurrence)
    (canonicalRoleOpeningPayload role occurrence)

/-- Canonical convergence is derived from the executed action agreement. -/
theorem producedRoleOutput_exact
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (occurrence : RoleConstitutedOccurrence role) :
    producedRoleOutput atom occurrence = role.completedOutput := by
  refine eliminateRoleConstitutedOccurrence role occurrence
    (motive := fun occurrence => producedRoleOutput atom occurrence = role.completedOutput) ?_ ?_
  · rcases license with ⟨transformed, transformedExact, transformedConstitution,
      retained, retainedExact, retainedConstitution, output, _preservation,
      _leftAccepted, _rightAccepted, _changes, _separate⟩
    cases transformedExact
    exact output
  · rfl

theorem producedRoleOutputs_converge
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (left right : RoleConstitutedOccurrence role) :
    producedRoleOutput atom left = producedRoleOutput atom right :=
  Eq.trans (producedRoleOutput_exact license left) (producedRoleOutput_exact license right).symm

/-- Full image of actual outputs; neither its type nor its frontier is a
preassigned occurrence or literal singleton. Only the two local sources are read. -/
def producedRoleOutputRegime
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    ObligationRegime (roleOpeningFiniteCarrier role) :=
  ProducedOutputImage.regime (roleOpeningFiniteCarrier role)
    (producedRoleOutput atom) (producedRoleOutputs_converge license)

theorem producedRoleOutputRegime_width
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    (producedRoleOutputRegime license).frontier.length = 1 :=
  ProducedOutputImage.width_exact _ _ (producedRoleOutputs_converge license)
    (roleConstitutedOccurrenceAt role .left)

/--
The operational decomposition available from one executed stage alone. Its
type mentions the current stage but not any future tail.
-/
structure ExecutedStageDecomposition
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) where
  private mk ::
  role : RelationalConstitutiveRoleStage stage
  roleExact : role = relationalConstitutiveRoleStage stage
  license : ExecutedRoleReductionLicense role (compileRoleStageAtom role)
  outputRegime : ObligationRegime (roleOpeningFiniteCarrier role)
  outputRegimeExact : outputRegime = producedRoleOutputRegime license

/-- Canonical local decomposition, constructed from no data beyond the stage. -/
def executedStageDecomposition
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    ExecutedStageDecomposition stage :=
  let role := relationalConstitutiveRoleStage stage
  let license := executedRoleReductionLicense role
  { role := role
    roleExact := rfl
    license := license
    outputRegime := producedRoleOutputRegime license
    outputRegimeExact := rfl }

namespace RoleStatus

/-- Local status supplied by the actual executed license, not by a Boolean switch. -/
def returnedTransport {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source} {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role} (license : ExecutedRoleReductionLicense role atom) :
    AcceptingContinuationTransport (RoleSemantics.occurrenceSystem role)
      (roleConstitutedOccurrenceAt role .left) (roleConstitutedOccurrenceAt role .right) :=
  { map := atom.action, preservesAccept := license.preservesCriterion }

end RoleStatus

/-- The status is read from the license produced by this local decomposition. -/
def ExecutedStageDecomposition.operationalStatus
    {source : CausalConstitutiveState}
    {stage : CausalConstitutiveStageExecution source}
    (decomposition : ExecutedStageDecomposition stage) : RoleStatus.Status decomposition.role :=
  some (RoleStatus.returnedTransport decomposition.license)

/--
A closed, state-indexed past. Each extension records the stage and local
material already produced; it cannot contain an arbitrary user-selected type
of context or a completed future execution as its context payload.
-/
inductive ConstitutedOperationalPrefix : CausalConstitutiveState → Type 2 where
  | root (source : CausalConstitutiveState) : ConstitutedOperationalPrefix source
  | advance {source : CausalConstitutiveState}
      (prior : ConstitutedOperationalPrefix source)
      (stage : CausalConstitutiveStageExecution source)
      (decomposition : ExecutedStageDecomposition stage) :
      ConstitutedOperationalPrefix decomposition.role.nextState

/-- The number of past productions is a downstream readout, not an input. -/
def ConstitutedOperationalPrefix.depth :
    {source : CausalConstitutiveState} → ConstitutedOperationalPrefix source → Nat
  | _, .root _ => 0
  | _, .advance prior _ _ => prior.depth + 1


/-- Material provenance reconstructed from the role actually recorded at the head. -/
def ConstitutedOperationalPrefix.provenance :
    {source : CausalConstitutiveState} → ConstitutedOperationalPrefix source → List SAT.Var
  | _, .root source => source.provenance
  | _, .advance _ stage decomposition =>
      stage.selected :: decomposition.role.provenance

/--
Source and provenance agreements connect the head's actual material to the
source; its target agreement connects the extended material to the next state.
-/
theorem ConstitutedOperationalPrefix.provenance_exact :
    {source : CausalConstitutiveState} →
      (past : ConstitutedOperationalPrefix source) →
      past.provenance = source.provenance
  | _, .root _ => rfl
  | _, .advance _ stage decomposition => by
      change stage.selected :: decomposition.role.provenance =
        decomposition.role.nextState.provenance
      exact Eq.trans
        (congrArg (List.cons stage.selected) decomposition.role.provenanceExact)
        (Eq.trans stage.nextProvenanceExact.symm
          (congrArg CausalConstitutiveState.provenance
            decomposition.role.nextStateExact.symm))

/-- Dependent transport of a context does not invent or recount executed heads. -/
theorem ConstitutedOperationalPrefix.depth_transport
    {source target : CausalConstitutiveState}
    (same : source = target)
    (past : ConstitutedOperationalPrefix source) :
    (same ▸ past : ConstitutedOperationalPrefix target).depth = past.depth := by
  cases same
  rfl

/-- Material produced from the current stage and its already constituted past. -/
structure ExecutedStageOperationalProduction
    {source : CausalConstitutiveState}
    (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) : Type 2 where
  private mk ::
  priorContext : ConstitutedOperationalPrefix source
  priorContextExact : priorContext = context
  decomposition : ExecutedStageDecomposition stage
  decompositionExact : decomposition = executedStageDecomposition stage

/-- No independent status is reconstructed after the future history. -/
def ExecutedStageOperationalProduction.operationalStatus
    {source : CausalConstitutiveState}
    {context : ConstitutedOperationalPrefix source}
    {stage : CausalConstitutiveStageExecution source}
    (production : ExecutedStageOperationalProduction context stage) :
    RoleStatus.Status production.decomposition.role :=
  production.decomposition.operationalStatus

/-- Extend the actual past with this production and the state it produced. -/
def ExecutedStageOperationalProduction.nextContext
    {source : CausalConstitutiveState}
    {context : ConstitutedOperationalPrefix source}
    {stage : CausalConstitutiveStageExecution source}
    (production : ExecutedStageOperationalProduction context stage) :
    ConstitutedOperationalPrefix stage.next :=
  production.decomposition.role.nextStateExact ▸
    ConstitutedOperationalPrefix.advance production.priorContext stage
      production.decomposition

/-- The next context contains one additional already executed production. -/
theorem ExecutedStageOperationalProduction.nextContext_depth
    {source : CausalConstitutiveState}
    {context : ConstitutedOperationalPrefix source}
    {stage : CausalConstitutiveStageExecution source}
    (production : ExecutedStageOperationalProduction context stage) :
    production.nextContext.depth = context.depth + 1 := by
  change production.priorContext.depth + 1 = context.depth + 1
  rw [production.priorContextExact]

/-- The producer has no remaining-count, future-history or arbitrary-context input. -/
abbrev PrefixLocalOperationalProducer : Type 2 :=
  {source : CausalConstitutiveState} →
    (context : ConstitutedOperationalPrefix source) →
    (stage : CausalConstitutiveStageExecution source) →
      ExecutedStageOperationalProduction context stage

/-- Produce the local decomposition before constructing the dependent continuation. -/
def prefixLocalOperationalProducer : PrefixLocalOperationalProducer :=
  fun {_} context stage =>
    { priorContext := context
      priorContextExact := rfl
      decomposition := executedStageDecomposition stage
      decompositionExact := rfl }

/-- The local computation is exactly the function of the already executed stage. -/
theorem prefixLocalOperationalProducer_decomposition_exact
    {source : CausalConstitutiveState}
    (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer context stage).decomposition =
      executedStageDecomposition stage :=
  rfl

/-- The status available before the tail is the status of this head's license. -/
theorem prefixLocalOperationalProducer_status_exact
    {source : CausalConstitutiveState}
    (context : ConstitutedOperationalPrefix source)
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer context stage).operationalStatus =
      (executedStageDecomposition stage).operationalStatus := rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedRoleOutput
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedRoleOutput_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedRoleOutputs_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedRoleOutputRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.producedRoleOutputRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition.outputRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition.outputRegimeExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.prefixLocalOperationalProducer_status_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleStatus.returnedTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition.operationalStatus
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.operationalStatus
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOperationalPrefix.provenance
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOperationalPrefix.provenance_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOperationalPrefix.depth_transport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOperationalPrefix
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutedOperationalPrefix.depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.nextContext
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.nextContext_depth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProducer
#print axioms ConstitutiveSearch.EndogenousDecomposition.prefixLocalOperationalProducer
#print axioms ConstitutiveSearch.EndogenousDecomposition.prefixLocalOperationalProducer_decomposition_exact
/- AXIOM_AUDIT_END -/
