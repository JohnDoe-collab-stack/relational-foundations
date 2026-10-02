import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoles
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileConstitution

/-!
# Opening occurrences and extensive profiles indexed by relational roles

The local carrier is not a free Boolean label.  A position is realized by an
occurrence carrying the generated structural state formed at that position of
that particular role.  Complete profiles are dependent selections over the
authoritative role history.  Enumeration and width are derived afterwards.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open RelationalExtensive

/-- The two expected positions of one executed binary opening. -/
inductive OpeningRolePosition
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (_role : RelationalConstitutiveRoleStage run) : Type where
  | left
  | right

/-- The generated state occurring at one role position. -/
def OpeningRolePosition.state
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    OpeningRolePosition role →
      GeneratedStructuralBranchContext source.rootFormula
  | .left => causalOpeningLeft source run.selected run.fresh
  | .right => causalOpeningRight source run.selected run.fresh


/-- The occurrence is justified by structural generation, not by a copied state equation. -/
def RoleFormationAgreement
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role)
    (state : GeneratedStructuralBranchContext source.rootFormula) : Type :=
  match position with
  | .left => GeneratedChildFormation source.operationalState run.selected false run.fresh state
  | .right => GeneratedChildFormation source.operationalState run.selected true run.fresh state

/-- Exact realization is a consequence of the indexed formation. -/
theorem RoleFormationAgreement.down
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {position : OpeningRolePosition role}
    {state : GeneratedStructuralBranchContext source.rootFormula}
    (formation : RoleFormationAgreement role position state) :
    state = position.state role := by
  cases position <;> cases formation <;> rfl

/--
An opening occurrence carries both its historical position and the generated
structural state that realizes that position.
-/
structure RoleOpeningOccurrence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) where
  position : OpeningRolePosition role
  state : GeneratedStructuralBranchContext source.rootFormula
  formationWitness : RoleFormationAgreement role position state


/-- Exact realization is recovered by consuming the stored formation witness. -/
theorem RoleOpeningOccurrence.formedAt
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) :
    occurrence.state = occurrence.position.state role :=
  occurrence.formationWitness.down

/-- Canonical realization of a role position by its generated occurrence. -/
def roleOpeningOccurrenceAt
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    RoleOpeningOccurrence role :=
  { position := position
    state := position.state role
    formationWitness := by cases position <;> exact .formed }

/-- Forget only the realized state, retaining the occurrence's position. -/
def roleOpeningOccurrenceToPosition
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) :
    OpeningRolePosition role :=
  occurrence.position

theorem openingPosition_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    roleOpeningOccurrenceToPosition
      (roleOpeningOccurrenceAt role position) = position :=
  rfl

theorem openingOccurrence_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleOpeningOccurrence role) :
    roleOpeningOccurrenceAt role
        (roleOpeningOccurrenceToPosition occurrence) =
      occurrence := by
  cases occurrence with
  | mk position state formationWitness =>
      cases position <;> cases formationWitness <;> rfl

/-- Exact reversible realization between positions and occurrences. -/
def openingPositionOccurrenceTransport
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    RelationalFoundations.ExactTransport
      (OpeningRolePosition role)
      (RoleOpeningOccurrence role) :=
  { forward := roleOpeningOccurrenceAt role
    backward := roleOpeningOccurrenceToPosition
    forwardBackward := openingPosition_roundTrip role
    backwardForward := openingOccurrence_roundTrip }

/-- Constructive decidable equality of positions. -/
def openingRolePositionDecEq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    DecidableEq (OpeningRolePosition role)
  | .left, .left => isTrue rfl
  | .left, .right => isFalse (fun impossible => nomatch impossible)
  | .right, .left => isFalse (fun impossible => nomatch impossible)
  | .right, .right => isTrue rfl

/-- The complete local frontier of structural role positions. -/
def openingPositionFrontier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    List (OpeningRolePosition role) :=
  [.left, .right]

theorem openingPositionFrontier_complete
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    position ∈ openingPositionFrontier role := by
  cases position with
  | left => exact .head _
  | right => exact .tail _ (.head _)

theorem openingPositionFrontier_nodup
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (openingPositionFrontier role).Nodup := by
  exact .cons
    (fun value member same => by
      cases member with
      | head => nomatch same
      | tail _ impossible => cases impossible)
    (.cons (fun _ impossible _ => nomatch impossible) .nil)

/-- Occurrences are equal exactly when their realized positions are equal. -/
theorem roleOpeningOccurrence_eq_of_position_eq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {left right : RoleOpeningOccurrence role}
    (same : left.position = right.position) :
    left = right := by
  calc
    left = roleOpeningOccurrenceAt role left.position :=
      (openingOccurrence_roundTrip left).symm
    _ = roleOpeningOccurrenceAt role right.position :=
      congrArg (roleOpeningOccurrenceAt role) same
    _ = right := openingOccurrence_roundTrip right

/-- Constructive decidable equality of realized occurrences. -/
def roleOpeningOccurrenceDecEq
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    DecidableEq (RoleOpeningOccurrence role) := by
  intro left right
  match openingRolePositionDecEq role left.position right.position with
  | isTrue same => exact isTrue (roleOpeningOccurrence_eq_of_position_eq same)
  | isFalse different =>
      exact isFalse (fun occurrenceSame =>
        different (congrArg RoleOpeningOccurrence.position occurrenceSame))

/-- Left and right positions are constructively distinct. -/
theorem openingRolePosition_left_ne_right
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (OpeningRolePosition.left : OpeningRolePosition role) ≠
      OpeningRolePosition.right := by
  intro impossible
  nomatch impossible

/-- The two realized opening occurrences are constructively distinct. -/
theorem roleOpeningOccurrence_left_ne_right
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    roleOpeningOccurrenceAt role .left ≠
      roleOpeningOccurrenceAt role .right := by
  intro impossible
  exact openingRolePosition_left_ne_right role
    (congrArg RoleOpeningOccurrence.position impossible)

/-- The two generated states of an opening are distinct as states, not labels. -/
theorem causalOpening_states_distinct
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source) :
    causalOpeningLeft source run.selected run.fresh ≠
      causalOpeningRight source run.selected run.fresh := by
  intro same
  have decisionsSame :=
    congrArg
      (fun state : GeneratedStructuralBranchContext source.rootFormula =>
        state.context.decisions)
      same
  change
    ({ var := run.selected, value := false } : StructuralBranchDecision) ::
        source.operationalState.context.decisions =
      ({ var := run.selected, value := true } : StructuralBranchDecision) ::
        source.operationalState.context.decisions at decisionsSame
  have headsSame := List.cons.inj decisionsSame
  have valuesSame := congrArg StructuralBranchDecision.value headsSame.1
  exact Bool.noConfusion valuesSame

/-- Local occurrence frontier, derived from the position frontier by realization. -/
def openingOccurrenceFrontier
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    List (RoleOpeningOccurrence role) :=
  (openingPositionFrontier role).map (roleOpeningOccurrenceAt role)

theorem openingOccurrenceFrontier_complete
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (occurrence : RoleOpeningOccurrence role) :
    occurrence ∈ openingOccurrenceFrontier role := by
  have member := relational_mem_map (roleOpeningOccurrenceAt role)
    (openingPositionFrontier_complete role occurrence.position)
  exact (openingOccurrence_roundTrip occurrence) ▸ member

theorem openingOccurrenceFrontier_nodup
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (openingOccurrenceFrontier role).Nodup :=
  relational_nodup_map (roleOpeningOccurrenceAt role)
    (fun {_left _right} same => by
      exact congrArg RoleOpeningOccurrence.position same)
    (openingPositionFrontier_nodup role)

/-- Source realization agreement projected from the executed relational role. -/
abbrev executedRoleSourceRelation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (observed : CausalConstitutiveState)
    (candidate : RelationalConstitutiveRoleStage run) : Type :=
  RoleSourceAgreement candidate.searchState observed

/-- Primitive formation relation between an executed role and one occurrence. -/
abbrev executedRoleFormationRelation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (reference : RelationalConstitutiveRoleStage run)
    (candidate : RelationalConstitutiveRoleStage run)
    (occurrence : RoleOpeningOccurrence reference) : Type :=
  PLift (candidate = reference) ×
    RoleFormationAgreement reference occurrence.position occurrence.state

/-- Target realization agreement projected from the executed relational role. -/
abbrev executedRoleTargetRelation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (candidate : RelationalConstitutiveRoleStage run)
    (observed : CausalConstitutiveState) : Type :=
  RoleTargetAgreement candidate.nextState observed

/-- Provenance and formation agreements carried by one executed occurrence. -/
abbrev executedRoleProvenanceRelation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (reference : RelationalConstitutiveRoleStage run)
    (provenance : List Var)
    (candidate : RelationalConstitutiveRoleStage run)
    (occurrence : RoleOpeningOccurrence reference) : Type :=
  RoleProvenanceAgreement provenance candidate.searchState.provenance ×
    PLift (candidate = reference) ×
    RoleFormationAgreement reference occurrence.position occurrence.state

/--
One executed role as an exact relational opening.  Positions are independent
from occurrences; the existing position-occurrence transport realizes them,
and formation and provenance are recorded as exact agreements.
-/
def generalOpeningStageOfRole
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    RelationalOpeningStage CausalConstitutiveState source run.next :=
  { Role := RelationalConstitutiveRoleStage run
    Position := OpeningRolePosition role
    Occurrence := RoleOpeningOccurrence role
    Provenance := List Var
    SourceRelation := executedRoleSourceRelation
    FormationRelation := executedRoleFormationRelation role
    TargetRelation := executedRoleTargetRelation
    ProvenanceRelation := executedRoleProvenanceRelation role
    role := role
    provenance := role.provenance
    sourceWitness := role.sourceWitness
    targetWitness := role.targetWitness
    positionDecEq := openingRolePositionDecEq role
    positionFrontier := openingPositionFrontier role
    positionComplete := openingPositionFrontier_complete role
    positionNodup := openingPositionFrontier_nodup role
    realize := roleOpeningOccurrenceAt role
    classify := roleOpeningOccurrenceToPosition
    realize_classify := openingOccurrence_roundTrip
    classify_realize := openingPosition_roundTrip role
    formationAgreement := fun position =>
      ⟨⟨rfl⟩, (roleOpeningOccurrenceAt role position).formationWitness⟩
    provenanceAgreement := fun position =>
      ⟨role.provenanceWitness, ⟨⟨rfl⟩,
        (roleOpeningOccurrenceAt role position).formationWitness⟩⟩ }

/--
The constituted identity belonging to one executed relational role. The
opening occurrence remains only the internal realization carried by the stage; every
scientific profile and every downstream operation uses this stage-indexed
identity.
-/
abbrev RoleConstitutedOccurrence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) : Type :=
  RelationallyConstitutedOccurrence (generalOpeningStageOfRole role)

/-- Constitute a role identity from its exact historical position. -/
def roleConstitutedOccurrenceAt
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (position : OpeningRolePosition role) :
    RoleConstitutedOccurrence role :=
  relationallyConstitutedOccurrence (generalOpeningStageOfRole role) position

/-- Reconstituting an identity from its carried position returns that identity. -/
theorem roleConstitutedOccurrence_roundTrip
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (identity : RoleConstitutedOccurrence role) :
    roleConstitutedOccurrenceAt role identity.position = identity := by
  exact relationallyConstitutedOccurrence_roundTrip identity

/-- Realize a constituted role identity in its internal occurrence carrier. -/
def realizeRoleConstitutedOccurrence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (identity : RoleConstitutedOccurrence role) :
    RoleOpeningOccurrence role :=
  identity.realized

/-- The position is preserved exactly by the internal realization. -/
theorem realizeRoleConstitutedOccurrence_position
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (identity : RoleConstitutedOccurrence role) :
    (realizeRoleConstitutedOccurrence identity).position = identity.position :=
  rfl

/--
The positive relational evidence constituting one executed identity.  These
witnesses are not metadata adjacent to the carrier: the operational chain
receives this evidence for every identity it transforms or retains.
-/
structure RoleConstitutionEvidence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (identity : RoleConstitutedOccurrence role) : Type where
  sourceWitness : executedRoleSourceRelation source role
  targetWitness : executedRoleTargetRelation role run.next
  formationWitness :
    executedRoleFormationRelation role role identity.realized
  provenanceWitness :
    executedRoleProvenanceRelation role role.provenance role identity.realized

/-- Recover formation and realization witnesses from the exact relational opening. -/
def roleConstitutionEvidence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (identity : RoleConstitutedOccurrence role) :
    RoleConstitutionEvidence role identity :=
  { sourceWitness := identity.sourceWitness
    targetWitness := identity.targetWitness
    formationWitness :=
      (generalOpeningStageOfRole role).formationWitness identity
    provenanceWitness :=
      (generalOpeningStageOfRole role).provenanceWitness identity }


/--
Transport a payload from the realized state to its historical role position.
Unlike an unindexed Result-to-Result wrapper, the input and output here inhabit
different fibres. The actual formation equality supplies the transport.
Source, target and provenance remain carried by the constituted identity; this
function makes no claim that they change the value of the local total action.
-/
def RoleConstitutionEvidence.transportFormation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {identity : RoleConstitutedOccurrence role}
    {Motive : GeneratedStructuralBranchContext source.rootFormula → Sort u}
    (evidence : RoleConstitutionEvidence role identity)
    (value : Motive identity.realized.state) :
    Motive (identity.position.state role) :=
  evidence.formationWitness.2.down ▸ value

/--
Dependent case analysis justified by the realized-occurrence return law.
The branch inputs inhabit the canonical left and right fibres, not an already
supplied result in the fibre of an arbitrary identity.
-/
def eliminateRoleConstitutedOccurrence
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (identity : RoleConstitutedOccurrence role)
    {motive : RoleConstitutedOccurrence role → Sort u}
    (left : motive (roleConstitutedOccurrenceAt role .left))
    (right : motive (roleConstitutedOccurrenceAt role .right)) :
    motive identity := by
  have canonical := roleConstitutedOccurrence_roundTrip identity
  cases positionExact : identity.position with
  | left =>
      rw [positionExact] at canonical
      exact canonical ▸ left
  | right =>
      rw [positionExact] at canonical
      exact canonical ▸ right

/-- The general-stage transport is the authoritative occurrence realization. -/
theorem generalOpeningStage_positionOccurrenceTransport_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (generalOpeningStageOfRole role).positionOccurrenceTransport =
      openingPositionOccurrenceTransport role :=
  rfl

/-- The general relational history constituted by the authoritative roles. -/
def generalHistoryOfRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DependentRelationalRoleHistory CausalConstitutiveState state count
  | _, state, _, .nil => .nil state
  | _, _, _, .step headRole tailRoles =>
      .step (generalOpeningStageOfRole headRole)
        (generalHistoryOfRoleHistory tailRoles)

/-- Position profile over an authoritative role history. -/
abbrev RolePositionProfile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Type :=
  RelationalPositionProfile (generalHistoryOfRoleHistory roles)

/--
The sole occurrence-profile carrier of the executed instance.  It is exactly
the profile derived from the role history through the relational realization;
no parallel concrete profile is defined.
-/
abbrev RoleOccurrenceProfile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Type :=
  RelationalOccurrenceProfile (generalHistoryOfRoleHistory roles)

/-- Pointwise realization of a complete position profile. -/
def rolePositionToOccurrenceProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RolePositionProfile roles → RoleOccurrenceProfile roles :=
  fun roles =>
    relationalPositionToOccurrenceProfile (generalHistoryOfRoleHistory roles)

/-- Recover all historical positions from an occurrence profile. -/
def roleOccurrenceToPositionProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles → RolePositionProfile roles :=
  fun roles =>
    relationalOccurrenceToPositionProfile (generalHistoryOfRoleHistory roles)

theorem rolePositionProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RolePositionProfile roles) →
      roleOccurrenceToPositionProfile roles
          (rolePositionToOccurrenceProfile roles profile) =
        profile :=
  fun roles =>
    relationalPositionProfile_roundTrip (generalHistoryOfRoleHistory roles)

theorem roleOccurrenceProfile_roundTrip :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      rolePositionToOccurrenceProfile roles
          (roleOccurrenceToPositionProfile roles profile) =
        profile :=
  fun roles =>
    relationalOccurrenceProfile_roundTrip (generalHistoryOfRoleHistory roles)

/-- Exact transport between position profiles and realized occurrence profiles. -/
def roleProfileTransport
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    RelationalFoundations.ExactTransport
      (RolePositionProfile roles)
      (RoleOccurrenceProfile roles) :=
  relationalProfileTransport (generalHistoryOfRoleHistory roles)

/-- The sole profile frontier, derived from the exact relational history. -/
def roleProfileFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    List (RoleOccurrenceProfile roles) :=
  relationalProfileFrontier (generalHistoryOfRoleHistory roles)

theorem roleProfileFrontier_complete :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      profile ∈ roleProfileFrontier roles :=
  fun roles profile =>
    relationalProfileFrontier_complete
      (generalHistoryOfRoleHistory roles) profile

theorem roleProfileFrontier_nodup :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (roleProfileFrontier roles).Nodup :=
  fun roles =>
    relationalProfileFrontier_nodup (generalHistoryOfRoleHistory roles)

/-- Width is a readout of the role-produced profile frontier. -/
def roleProfileWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) : Nat :=
  relationalProfileWidth (generalHistoryOfRoleHistory roles)

/-- Every executed role opening has exactly two realized positions. -/
theorem generalRoleHistory_uniformBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      UniformLocalArity (generalHistoryOfRoleHistory roles) 2
  | _, _, _, .nil => True.intro
  | _, _, _, .step _ tailRoles =>
      ⟨rfl, generalRoleHistory_uniformBinary tailRoles⟩

theorem roleProfileWidth_eq_two_pow_count
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    roleProfileWidth roles = 2 ^ count :=
  uniformLocalArity_width
    (generalHistoryOfRoleHistory roles) 2
    (generalRoleHistory_uniformBinary roles)

theorem roleProfileWidth_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    roleProfileWidth
        (RelationalConstitutiveRoleHistory.step headRole tailRoles) =
      roleProfileWidth tailRoles * 2 := by
  rw [roleProfileWidth_eq_two_pow_count,
    roleProfileWidth_eq_two_pow_count]
  exact (Nat.pow_succ 2 _).symm

/-- Constructive equality decision for complete occurrence profiles. -/
def roleOccurrenceProfileDecEq :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      DecidableEq (RoleOccurrenceProfile roles) :=
  fun roles =>
    relationalOccurrenceProfileDecEq (generalHistoryOfRoleHistory roles)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleFormationAgreement.down
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleFormationAgreement
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOpeningOccurrence.formedAt
#print axioms ConstitutiveSearch.EndogenousDecomposition.OpeningRolePosition
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOpeningOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionOccurrenceTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.causalOpening_states_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingOccurrenceFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.openingPositionFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleSourceRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleFormationRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleTargetRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleProvenanceRelation
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningStageOfRole
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleConstitutedOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstitutedOccurrenceAt
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstitutedOccurrence_roundTrip
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeRoleConstitutedOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.realizeRoleConstitutedOccurrence_position
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleConstitutionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleConstitutionEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleConstitutionEvidence.transportFormation
#print axioms ConstitutiveSearch.EndogenousDecomposition.eliminateRoleConstitutedOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalOpeningStage_positionOccurrenceTransport_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistoryOfRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.RolePositionProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleOccurrenceProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_complete
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileFrontier_nodup
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalRoleHistory_uniformBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_step
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleProfileWidth_eq_two_pow_count
#print axioms ConstitutiveSearch.EndogenousDecomposition.roleOccurrenceProfileDecEq
/- AXIOM_AUDIT_END -/
