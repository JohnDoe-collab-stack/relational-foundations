import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseOperationalStatus
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedOutputObligations
import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleProfileSemantics

/-!
# Operational image computed by the executed role reduction

The relation-indexed reduction is executed first. For every constituted source
profile it produces a target profile together with the dependent trace that
produced it. The composed images of actual local outputs are realized at those
targets by a two-sided transport. Each admitted obligation retains its actual
value, production evidence and separate semantic guarantee. Its frontier is
the transported output-policy frontier;
completeness and distinctness use the return laws before width is read.
Convergence of continuation values remains a separate executed theorem.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive

/-- Source-indexed results actually produced by one executed reduction. -/
structure ExecutedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) where
  private mk ::
  constitutiveChain : ExecutedReductionConstitutiveChain reduction
  constitutiveChainExact : ExecutedReductionCausalExact constitutiveChain

/-- Canonical normalization is the execution of the reduction history. -/
def executedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ExecutedCausalNormalization reduction :=
  { constitutiveChain := executedReductionConstitutiveChain reduction
    constitutiveChainExact :=
      (executedReductionConstitutiveChain reduction).causalExact }

/-- Preservation is recovered from the exact chain consumed by normalization. -/
def ExecutedCausalNormalization.constitutivePreservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionPreservationExact normalization.constitutiveChain :=
  normalization.constitutiveChainExact.preservationExact

/-- Primitive relational witnesses are recovered from the consumed chain. -/
def ExecutedCausalNormalization.constitutiveRelationalEvidence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionRelationalConstitutionExact
      normalization.constitutiveChain :=
  normalization.constitutiveChainExact.relationalConstitutionExact

/-- Source separation is recovered from that same consumed exact chain. -/
def ExecutedCausalNormalization.constitutiveOccurrenceSeparation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionOccurrenceSeparationExact normalization.constitutiveChain :=
  normalization.constitutiveChainExact.occurrenceSeparationExact

/--
Positive authorization for operational grouping.  It is not a width premise:
it is the ordered preservation and source-separation material extracted from
the very chain whose decisions produce the normalized targets.
-/
structure ExecutedOperationalGroupingAuthorization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  private mk ::
  causalExact : ExecutedReductionCausalExact normalization.constitutiveChain

/-- Preservation licensed by the exact causal chain of this authorization. -/
def ExecutedOperationalGroupingAuthorization.preservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionPreservationExact normalization.constitutiveChain :=
  authorization.causalExact.preservationExact

/-- Relational constitution licensed by the exact causal chain. -/
def ExecutedOperationalGroupingAuthorization.relationalConstitution
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionRelationalConstitutionExact
      normalization.constitutiveChain :=
  authorization.causalExact.relationalConstitutionExact

/-- Occurrence separation licensed by the same exact causal chain. -/
def ExecutedOperationalGroupingAuthorization.occurrenceSeparation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionOccurrenceSeparationExact normalization.constitutiveChain :=
  authorization.causalExact.occurrenceSeparationExact

/-- The grouping authorization is read from the stored causal chain. -/
def ExecutedCausalNormalization.groupingAuthorization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedOperationalGroupingAuthorization normalization :=
  { causalExact := normalization.constitutiveChainExact }

/--
The result is not a field that a caller or an alternative constructor can
replace. It is computed by eliminating the exact constitutive chain stored in
the normalization.
-/
def ExecutedCausalNormalization.result
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedChainNormalization
      normalization.constitutiveChain sourceProfile :=
  normalizeExecutedRoleProfileFromChain
    normalization.constitutiveChain sourceProfile

/-- The result is definitionally the execution of the stored causal chain. -/
theorem ExecutedCausalNormalization.result_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.result sourceProfile =
      normalizeExecutedRoleProfileFromChain
        normalization.constitutiveChain sourceProfile :=
  rfl

/-- Target profile produced for one constituted source profile. -/
def ExecutedCausalNormalization.target
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedOperationalTargetProfile reduction :=
  (normalization.result sourceProfile).target

/-- Dependent executed trace producing that target. -/
def ExecutedCausalNormalization.trace
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedRoleProfileReduction
      reduction sourceProfile (normalization.target sourceProfile) :=
  (normalization.result sourceProfile).trace

/-- Each target is fixed by the executed decisions in its trace. -/
theorem ExecutedCausalNormalization.target_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.target sourceProfile =
      retainedExecutedOperationalTargetProfile reduction :=
  executedRoleProfileReduction_target_exact
    (normalization.trace sourceProfile)

/-- The executed traces, not the ambient target carrier, prove convergence. -/
theorem ExecutedCausalNormalization.targets_converge
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.target left = normalization.target right :=
  Eq.trans (normalization.target_exact left)
    (normalization.target_exact right).symm

/-- Structural semantics of this normalization, with no proof in its description. -/
def ExecutedCausalNormalization.imageDescription
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : SemanticImage.Description :=
  { Source := RoleOccurrenceProfile roles
    Payload := RoleProfilePayload
    Target := ExecutedOperationalTargetProfile reduction
    Accept := RoleSemantics.ProfileAccept
    TargetAccept := RoleSemantics.TargetAccept reduction
    action := RoleSemantics.actProfile reduction
    canonical := canonicalRoleProfilePayload roles
    produced := normalization.target
    reflect := fun target => ⟨RoleSemantics.retainedSelection reduction,
      RoleSemantics.includeTarget reduction target⟩
    SourceInvariant := RoleSemantics.SourcesRemainDistinct reduction ∧
      ∀ p : RoleOccurrenceProfile roles, RoleSemantics.ProfileConstitution p }

/-- Extract the independent semantic obligations from the actual chain. -/
theorem ExecutedOperationalGroupingAuthorization.semanticAdmission
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    SemanticImage.Admission normalization.imageDescription :=
  { invariant := ⟨RoleSemantics.sourcesRemainDistinct authorization.occurrenceSeparation,
      RoleSemantics.profileConstitutionFromChain authorization.relationalConstitution⟩
    canonicalExact := fun p => Eq.trans (RoleSemantics.canonicalAction_exact reduction p)
      (normalization.target_exact p).symm
    preservation := RoleSemantics.profilePreserves authorization.preservation
    reflection := RoleSemantics.includeTarget_preserves reduction }

/-- Admission is discharged before the generic image obligation is constructed. -/
theorem ExecutedOperationalGroupingAuthorization.imageSpecification
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization)
    (value : ExecutedOperationalTargetProfile reduction) :
    SemanticImage.Specification normalization.imageDescription value :=
  authorization.semanticAdmission.specification value

/-- Positive occurrence of one target with its source and executed trace. -/
structure ProducedOperationalTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) where
  source : RoleOccurrenceProfile roles
  target : ExecutedOperationalTargetProfile reduction
  trace : ExecutedRoleProfileReduction reduction source target
  targetExact : target = normalization.target source

/-- Construct the positive target occurrence produced from one source. -/
def ExecutedCausalNormalization.producedTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ProducedOperationalTargetOccurrence normalization :=
  { source := sourceProfile
    target := normalization.target sourceProfile
    trace := normalization.trace sourceProfile
    targetExact := rfl }

/-- Complete source-indexed list of produced target occurrences. -/
def ExecutedCausalNormalization.producedTargetOccurrences
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List (ProducedOperationalTargetOccurrence normalization) :=
  (roleProfileFiniteCarrier roles).frontier.map
    normalization.producedTargetOccurrence

/-- The frontier representative is itself one target produced by execution. -/
def ExecutedCausalNormalization.producedTargetFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (_normalization : ExecutedCausalNormalization reduction) :
    List (ExecutedOperationalTargetProfile reduction) :=
  (rolewiseObligationFrontier (ExecutedOutput.policy reduction)).map
    (ExecutedOutput.value reduction)

/-- Positive membership in the image actually produced by this execution. -/
def ExecutedTargetIsProduced
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (value : ExecutedOperationalTargetProfile reduction) : Prop :=
  ∃ profile, normalization.target profile = value ∧
    Nonempty (ExecutedRoleProfileReduction reduction profile value)

/--
An obligation retains an actual target, its executed production proof and its
independent semantic guarantee.
Membership is not defined as equality to a distinguished output. The ambient
target carrier remains unchanged, and convergence is a separate theorem.
-/
structure AuthorizedProducedTargetObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type where
  admitted ::
  value : ExecutedOperationalTargetProfile reduction
  produced : ExecutedTargetIsProduced normalization value
  semantics : SemanticImage.Specification normalization.imageDescription value

/-- Use an obligation's own preimage guarantee through the abstract consumer. -/
def AuthorizedProducedTargetObligation.transformPayload
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (obligation : AuthorizedProducedTargetObligation normalization)
    (p : RoleOccurrenceProfile roles) (preimage : normalization.target p = obligation.value)
    (payload : RoleProfilePayload p) :
    {result : ExecutedOperationalTargetProfile reduction //
      result = RoleSemantics.actProfile reduction p payload ∧
      (RoleSemantics.ProfileAccept p payload → RoleSemantics.TargetAccept reduction result)} :=
  SemanticImage.use obligation.semantics p preimage payload

/-- The admitted value retains the constitution and separation of its sources. -/
theorem AuthorizedProducedTargetObligation.sourceInvariant
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (obligation : AuthorizedProducedTargetObligation normalization) :
    RoleSemantics.SourcesRemainDistinct reduction ∧
      ∀ p : RoleOccurrenceProfile roles, RoleSemantics.ProfileConstitution p :=
  SemanticImage.source_invariant obligation.semantics

/-- Equality of admitted image values neither merges nor splits produced targets. -/
theorem AuthorizedProducedTargetObligation.eq_of_value_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    {left right : AuthorizedProducedTargetObligation normalization}
    (same : left.value = right.value) : left = right := by
  cases left with
  | admitted leftValue leftProduced leftSemantics =>
    cases right with
    | admitted rightValue rightProduced rightSemantics =>
      change leftValue = rightValue at same
      cases same
      rfl

/-- The executed traces prove equality of the produced image values. -/
theorem AuthorizedProducedTargetObligation.all_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : AuthorizedProducedTargetObligation normalization) :
    left = right := by
  apply AuthorizedProducedTargetObligation.eq_of_value_eq
  rcases left.produced with ⟨leftSource, leftExact, _leftTrace⟩
  rcases right.produced with ⟨rightSource, rightExact, _rightTrace⟩
  exact Eq.trans leftExact.symm
    (Eq.trans (normalization.targets_converge leftSource rightSource) rightExact)

/-- Equality on the image is justified by actual executed convergence. -/
def authorizedProducedTargetObligationDecEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    DecidableEq (AuthorizedProducedTargetObligation normalization) :=
  fun left right => isTrue (AuthorizedProducedTargetObligation.all_eq normalization left right)

/-- The local-output policy and chain normalization compute the same values. -/
theorem ExecutedCausalNormalization.outputCarry_value
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (p : RoleOccurrenceProfile roles) :
    ExecutedOutput.value reduction (rolewiseCarry (ExecutedOutput.policy reduction) p) =
      normalization.target p :=
  Eq.trans (ExecutedOutput.carry_action reduction p)
    (Eq.trans (RoleSemantics.canonicalAction_exact reduction p) (normalization.target_exact p).symm)

/-- Actual target production gives local image membership at every role. -/
theorem ExecutedCausalNormalization.outputProduced_target
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (p : RoleOccurrenceProfile roles) : ExecutedOutput.IsProduced reduction (normalization.target p) :=
  normalization.outputCarry_value p ▸
    ExecutedOutput.value_isProduced reduction (rolewiseCarry (ExecutedOutput.policy reduction) p)

/-- Recover membership from a trace's produced target, without choosing source data. -/
theorem ExecutedCausalNormalization.outputProduced_of_trace
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (target : ExecutedOperationalTargetProfile reduction)
    (produced : ExecutedTargetIsProduced normalization target) :
    ExecutedOutput.IsProduced reduction target := by
  rcases produced with ⟨p, exactTarget, _trace⟩
  exact exactTarget ▸ normalization.outputProduced_target p

/-- Realization reads every actual local output in the policy obligation. -/
def ExecutedCausalNormalization.realizePolicyObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization)
    (q : RolewiseObligation (ExecutedOutput.policy reduction)) :
    AuthorizedProducedTargetObligation normalization :=
  { value := ExecutedOutput.value reduction q
    produced := by
      rcases rolewiseCarry_surjective (ExecutedOutput.policy reduction) q with ⟨p, same⟩
      have targetExact : normalization.target p = ExecutedOutput.value reduction q :=
        Eq.trans (normalization.outputCarry_value p).symm
          (congrArg (ExecutedOutput.value reduction) same)
      exact ⟨p, targetExact, ⟨targetExact ▸ normalization.trace p⟩⟩
    semantics := authorization.imageSpecification _ }

/-- Both return laws copy produced target components. No convergence or
singleton-width lemma is used to prove these inverse laws. -/
def ExecutedCausalNormalization.policyObligationTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    RelationalFoundations.ExactTransport (RolewiseObligation (ExecutedOutput.policy reduction))
      (AuthorizedProducedTargetObligation normalization) :=
  { forward := normalization.realizePolicyObligation authorization
    backward := fun obligation => ExecutedOutput.reify reduction obligation.value
      (normalization.outputProduced_of_trace obligation.value obligation.produced)
    forwardBackward := fun q => ExecutedOutput.reify_value reduction q
    backwardForward := fun obligation =>
      AuthorizedProducedTargetObligation.eq_of_value_eq
        (ExecutedOutput.value_reify reduction obligation.value _) }

/-- The regime is the exact transported realization of the locally produced
policy. Completeness and distinctness follow from the two return laws. -/
def ExecutedCausalNormalization.authorizedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  let policy := ExecutedOutput.policy reduction
  let transport := normalization.policyObligationTransport authorization
  { Obligation := AuthorizedProducedTargetObligation normalization
    decEq := authorizedProducedTargetObligationDecEq normalization
    frontier := (rolewiseObligationFrontier policy).map transport.forward
    complete := fun obligation => by
      have member := Extensive.mem_map transport.forward
        (rolewiseObligationFrontier_complete policy (transport.backward obligation))
      exact transport.backwardForward obligation ▸ member
    nodup := by
      have injective : Function.Injective transport.forward := by
        intro left right same
        exact Eq.trans (transport.forwardBackward left).symm
          (Eq.trans (congrArg transport.backward same) (transport.forwardBackward right))
      exact Extensive.nodup_map transport.forward injective
        (rolewiseObligationFrontier_nodup policy)
    carry := fun p => transport.forward (rolewiseCarry policy p)
    carry_surjective := fun obligation => by
      rcases rolewiseCarry_surjective policy (transport.backward obligation) with ⟨p, same⟩
      exact ⟨p, Eq.trans (congrArg transport.forward same) (transport.backwardForward obligation)⟩ }

/-- The public regime is formed only through its exact grouping authorization. -/
def ExecutedCausalNormalization.operationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  normalization.authorizedOperationalRegime
    normalization.groupingAuthorization

/-- Each carried value is the target of its own source's executed trace. -/
theorem ExecutedCausalNormalization.carry_value
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (p : RoleOccurrenceProfile roles) :
    (normalization.operationalRegime.carry p).value = normalization.target p :=
  normalization.outputCarry_value p

/-- Source portage commutes with the exact realization of produced obligations. -/
theorem ExecutedCausalNormalization.policyObligationTransport_carry
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (p : RoleOccurrenceProfile roles) :
    (normalization.policyObligationTransport normalization.groupingAuthorization).forward
      (rolewiseCarry (ExecutedOutput.policy reduction) p) =
      normalization.operationalRegime.carry p := rfl

/-- The actual carried obligations preserve and reflect the profile criterion. -/
theorem ExecutedCausalNormalization.viable_iff
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    (∃ p : RoleOccurrenceProfile roles, ∃ payload : RoleProfilePayload p,
      RoleSemantics.ProfileAccept p payload) ↔
    (∃ target : ExecutedOperationalTargetProfile reduction,
      RoleSemantics.TargetAccept reduction target) :=
  SemanticImage.viable_iff normalization.imageDescription
    (fun p => by
      change SemanticImage.Specification normalization.imageDescription (normalization.target p)
      rw [← normalization.carry_value p]
      exact (normalization.operationalRegime.carry p).semantics)

/-- The public regime is exactly that executed convergent-target regime. -/
theorem ExecutedCausalNormalization.operationalRegime_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime =
      normalization.authorizedOperationalRegime
        normalization.groupingAuthorization :=
  rfl

/-- Obligation equality is exactly equality of targets produced by execution. -/
theorem ExecutedCausalNormalization.carry_eq_iff_target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.operationalRegime.carry left =
        normalization.operationalRegime.carry right ↔
      normalization.target left = normalization.target right :=
  by
    constructor
    · intro same
      exact Eq.trans (normalization.carry_value left).symm
        (Eq.trans (congrArg (fun obligation => obligation.value) same) (normalization.carry_value right))
    · intro same
      exact AuthorizedProducedTargetObligation.eq_of_value_eq
        (Eq.trans (normalization.carry_value left) (Eq.trans same (normalization.carry_value right).symm))

/--
Positive relation between two constituted profiles whose executed traces
produce one and the same operational target.  This relation records the two
traces themselves; it is not a label inferred from a constant carry map.
-/
structure OperationallyCoDetermined
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) : Type 2 where
  groupingAuthorization :
    ExecutedOperationalGroupingAuthorization normalization
  target : ExecutedOperationalTargetProfile reduction
  leftTrace : ExecutedRoleProfileReduction reduction left target
  rightTrace : ExecutedRoleProfileReduction reduction right target
  leftTargetExact : target = normalization.target left
  rightTargetExact : target = normalization.target right

/-- Equal produced targets positively yield two traces to their common target. -/
def ExecutedCausalNormalization.coDeterminationOfTargetEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles)
    (sameTarget : normalization.target left = normalization.target right) :
    OperationallyCoDetermined normalization left right :=
  { target := normalization.target left
    groupingAuthorization := normalization.groupingAuthorization
    leftTrace := normalization.trace left
    rightTrace := sameTarget.symm ▸ normalization.trace right
    leftTargetExact := rfl
    rightTargetExact := sameTarget }

/-- Codetermination recovers equality of the targets actually produced. -/
theorem OperationallyCoDetermined.target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    {left right : RoleOccurrenceProfile roles}
    (witness : OperationallyCoDetermined normalization left right) :
    normalization.target left = normalization.target right :=
  Eq.trans witness.leftTargetExact.symm witness.rightTargetExact

/-- Obligation equality is exactly inhabited executed codetermination. -/
theorem ExecutedCausalNormalization.carry_eq_iff_coDetermined
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.operationalRegime.carry left =
        normalization.operationalRegime.carry right ↔
      Nonempty (OperationallyCoDetermined normalization left right) := by
  constructor
  · intro sameCarry
    exact ⟨normalization.coDeterminationOfTargetEq left right
      ((normalization.carry_eq_iff_target_eq left right).mp sameCarry)⟩
  · intro witness
    let ⟨produced⟩ := witness
    exact (normalization.carry_eq_iff_target_eq left right).mpr
      produced.target_eq

/--
Authorized exact incorporation of the executed target-image realization. Its
private constructor joins the causal authorization to that exact realization;
neither an independently supplied regime nor authorization detached from the
same causal chain can replace it.
-/
structure ExactExecutedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  private mk ::
  groupingAuthorization :
    ExecutedOperationalGroupingAuthorization normalization
  regime : ObligationRegime (roleProfileFiniteCarrier roles)
  regimeExact : regime = normalization.operationalRegime
  producedOccurrence :
    (source : RoleOccurrenceProfile roles) →
      ProducedOperationalTargetOccurrence normalization
  producedSourceExact :
    (source : RoleOccurrenceProfile roles) →
      (producedOccurrence source).source = source

/-- Canonical exact realization of the regime constructed from executed traces. -/
def exactExecutedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExactExecutedOperationalRegime normalization :=
  { regime := normalization.operationalRegime
    groupingAuthorization := normalization.groupingAuthorization
    regimeExact := rfl
    producedOccurrence := normalization.producedTargetOccurrence
    producedSourceExact := fun _ => rfl }

/-- A one-element finite frontier maps to its actual produced value. -/
theorem mapSingletonOfLengthOne {α β : Type} (values : List α) (f : α → β) (anchor : β)
    (length : values.length = 1) (allEqual : ∀ value, f value = anchor) :
    values.map f = [anchor] := by
  cases values with
  | nil => cases length
  | cons head tail =>
    cases tail with
    | nil => exact congrArg (fun value => [value]) (allEqual head)
    | cons second rest =>
      have impossible : (second :: rest).length = 0 := Nat.succ.inj length
      cases impossible

/-- Local output convergence makes the composed frontier a singleton at the executed target. -/
theorem ExecutedCausalNormalization.producedTargetFrontier_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier =
      [retainedExecutedOperationalTargetProfile reduction] :=
  mapSingletonOfLengthOne _ _ _ (ExecutedOutput.width reduction) (fun obligation => by
    rcases rolewiseCarry_surjective (ExecutedOutput.policy reduction) obligation with ⟨p, same⟩
    exact Eq.trans (congrArg (ExecutedOutput.value reduction) same).symm
      (Eq.trans (normalization.outputCarry_value p) (normalization.target_exact p)))

/-- Both frontiers are realizations of the same local-output image frontier. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length =
      normalization.producedTargetFrontier.length := by
  exact Eq.trans (Extensive.length_map _ _)
    (Extensive.length_map _ _).symm

/-- Operational width is a readout of the actual output-image composition. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_outputWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length =
      (rolewiseObligationFrontier (ExecutedOutput.policy reduction)).length :=
  Extensive.length_map _ _

/-- A subsequent comparison with the occurrence-status width, not its cause. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_statusWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run} {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length =
      (rolewiseObligationFrontier (RoleStatus.executed reduction).policy).length :=
  Eq.trans (Extensive.length_map _ _)
    (Eq.trans (ExecutedOutput.width reduction) (RoleStatus.executed_width reduction).symm)

/-- Width one follows executed output convergence and exact realization. -/
theorem ExecutedCausalNormalization.width_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length = 1 := by
  exact Eq.trans normalization.regimeWidth_eq_outputWidth (ExecutedOutput.width reduction)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_outputWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.outputCarry_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.outputProduced_target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.outputProduced_of_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.eq_of_value_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.authorizedProducedTargetObligationDecEq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.realizePolicyObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.policyObligationTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.policyObligationTransport_carry
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_value
#print axioms ConstitutiveSearch.EndogenousDecomposition.mapSingletonOfLengthOne
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_statusWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.semanticAdmission
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.viable_iff
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.imageDescription
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.imageSpecification
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.transformPayload
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.sourceInvariant

#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedTargetIsProduced
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.produced
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.eq_of_value_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutivePreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutiveRelationalEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutiveOccurrenceSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.preservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.relationalConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.occurrenceSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.groupingAuthorization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.result
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.result_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedOperationalTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrences
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.value
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.all_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.authorizedProducedTargetObligationDecEq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.authorizedOperationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.operationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.operationalRegime_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationallyCoDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.coDeterminationOfTargetEq
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationallyCoDetermined.target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_coDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExactExecutedOperationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.exactExecutedOperationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.width_exact
/- AXIOM_AUDIT_END -/
