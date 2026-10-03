import RelationalFoundations.BinaryGrouping
import RelationalFoundations.GroupingReindex
import RelationalFoundations.GroupingImage
import RelationalFoundations.GroupingContinuation
import RelationalFoundations.HistoricalGrouping
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparation
set_option genInjectivity false
namespace ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
open SAT
open RelationalFoundations RelationalFoundations.CertifiedGrouping

def roleShape : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → Binary.Shape
  | _, _, _, .nil => .empty
  | _, _, _, .step _ rest => .more (roleShape rest)

def encode : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → RoleOccurrenceProfile roles → Binary.Profile (roleShape roles)
  | _, _, _, .nil, _ => ()
  | _, _, _, .step _ rest, p => ((match p.1.position with | .left => false | .right => true), encode rest p.2)

def decode : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → Binary.Profile (roleShape roles) → RoleOccurrenceProfile roles
  | _, _, _, .nil, _ => ()
  | _, _, _, .step role rest, p =>
      (roleConstitutedOccurrenceAt role (if p.1 then .right else .left), decode rest p.2)

theorem decode_encode : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → (p : RoleOccurrenceProfile roles) →
    decode roles (encode roles p) = p
  | _, _, _, .nil, p => by cases p; rfl
  | _, _, _, .step role rest, p => by
      have head : roleConstitutedOccurrenceAt role
          (if (match p.1.position with | .left => false | .right => true) then .right else .left) = p.1 := by
        have roundtrip := roleConstitutedOccurrence_roundTrip p.1
        cases same : p.1.position <;> rw [same] at roundtrip <;> exact roundtrip
      exact Prod.ext head (decode_encode rest p.2)

theorem encode_decode : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) → (p : Binary.Profile (roleShape roles)) →
    encode roles (decode roles p) = p
  | _, _, _, .nil, p => by cases p; rfl
  | _, _, _, .step _ rest, p => by
      rcases p with ⟨bit, tail⟩
      cases bit <;> exact Prod.ext rfl (encode_decode rest tail)

def code {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} (roles : RelationalConstitutiveRoleHistory run) :
    ExactTransport (RoleOccurrenceProfile roles) (Binary.Profile (roleShape roles)) :=
  ⟨encode roles, decode roles, decode_encode roles, encode_decode roles⟩

def mask : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    RoleStatus.History roles → Binary.Profile (roleShape roles)
  | _, _, _, _, .nil => ()
  | _, _, _, _, .step none rest => (false, mask rest)
  | _, _, _, _, .step (some _) rest => (true, mask rest)

theorem selected_code : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → (p : RoleOccurrenceProfile roles) →
    encode roles (history.selected p) = Binary.selected (mask history) (encode roles p)
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .step none rest, p => Prod.ext rfl (selected_code rest p.2)
  | _, _, _, _, .step (some _) rest, p => Prod.ext rfl (selected_code rest p.2)

def rules {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) : Rules :=
  (Binary.rules (mask history)).reindex (code roles)

theorem normal_selected {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles) :
    (rules history).normal p = history.selected p := by
  change ((Binary.rules (mask history)).reindex (code roles)).normal p = history.selected p
  rw [Rules.reindex_normal (Binary.rules (mask history)) (code roles) p, Binary.normal_selected]
  exact (congrArg (decode roles) (selected_code history p)).symm.trans (decode_encode roles _)

def normalize {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles) :
    Trace (rules history).Step p (history.selected p) :=
  normal_selected history p ▸ ((rules history).normalize p).trace

theorem carry_fibres {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p q : RoleOccurrenceProfile roles) :
    rolewiseCarry history.policy p = rolewiseCarry history.policy q ↔ Nonempty (Chain (rules history).Step p q) := by
  have exact := (rules history).normal_eq_iff_chain p q
  rw [normal_selected, normal_selected] at exact
  exact (history.fibres p q).trans exact

def projection {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (slot : Binary.Slot (roleShape roles)) (p : RoleOccurrenceProfile roles) :=
  decode roles (Binary.projection (mask history) slot (encode roles p))

def family {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) :
    ProjectionFamily.Authorized (rules history) (Binary.Slot (roleShape roles)) (fun _ => RoleOccurrenceProfile roles) where
  project := projection history
  realize := by
    intro slot p q same
    have coded := congrArg (encode roles) same
    change encode roles (decode roles _) = encode roles (decode roles _) at coded
    rw [encode_decode, encode_decode] at coded
    let joined := Binary.joinOfProjectionEq (mask history) slot (encode roles p) (encode roles q) coded
    have left := Rules.reindexedTrace (Binary.rules (mask history)) (code roles) joined.left
    have right := Rules.reindexedTrace (Binary.rules (mask history)) (code roles) joined.right
    change Trace (rules history).Step (decode roles (encode roles p)) (decode roles joined.target) at left
    change Trace (rules history).Step (decode roles (encode roles q)) (decode roles joined.target) at right
    rw [decode_encode roles p] at left
    rw [decode_encode roles q] at right
    exact ⟨decode roles joined.target, left, right⟩

def stepIdentification {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (step : (rules history).Step p q) :
    {slot : Binary.Slot (roleShape roles) // projection history slot p = projection history slot q} :=
  let found := Binary.stepIdentification step.down
  ⟨found.1, congrArg (decode roles) found.2⟩

theorem projection_fibres {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p q : RoleOccurrenceProfile roles) :
    history.selected p = history.selected q ↔ Nonempty (ProjectionFamily.Path (projection history) p q) := by
  have exact := (family history).exact_fibres (stepIdentification history) p q
  rw [normal_selected, normal_selected] at exact
  exact exact

theorem executed_normal {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p : RoleOccurrenceProfile roles) :
    (rules (RoleStatus.executed reduction)).normal p = retainedRoleProfile reduction :=
  (normal_selected _ p).trans (RoleStatus.executed_selected_eq reduction p)

def executed_join {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p q : RoleOccurrenceProfile roles) : Join (rules (RoleStatus.executed reduction)).Step p q :=
  (rules _).joinOfNormalEq ((executed_normal reduction p).trans (executed_normal reduction q).symm)

theorem stagewise_normal {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} (productions : StagewiseExecutedDecompositionHistory run)
    (p : RoleOccurrenceProfile productions.roles) :
    (rules (RoleStatus.ofStagewise productions)).normal p = retainedRoleProfile productions.reduction := by
  rw [RoleStatus.ofStagewise_eq_executed]
  exact executed_normal productions.reduction p


def codedAction : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → {p q : Binary.Profile (roleShape roles)} →
    Binary.Move (mask history) p q → RoleProfilePayload (decode roles p) → RoleProfilePayload (decode roles q)
  | _, _, _, _, .nil, _, _, step => nomatch step
  | _, _, _, _, .step none rest, _, _, step =>
      match step with
      | .tail child => fun data => (data.1, codedAction rest child data.2)
  | _, _, _, _, .step (some transport) rest, _, _, step =>
      match step with
      | .head => fun data => (transport.map data.1, data.2)
      | .tail child => fun data => (data.1, codedAction rest child data.2)


theorem codedPreserves : {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} → {roles : RelationalConstitutiveRoleHistory run} →
    (history : RoleStatus.History roles) → {p q : Binary.Profile (roleShape roles)} →
    (step : Binary.Move (mask history) p q) → (data : RoleProfilePayload (decode roles p)) →
    RoleSemantics.ProfileAccept (decode roles p) data →
    RoleSemantics.ProfileAccept (decode roles q) (codedAction history step data)
  | _, _, _, _, .nil, _, _, step, _, _ => nomatch step
  | _, _, _, _, .step none rest, _, _, step, data, accepted => by
      cases step with
      | tail child => exact ⟨accepted.1, codedPreserves rest child data.2 accepted.2⟩
  | _, _, _, _, .step (some transport) rest, _, _, step, data, accepted => by
      cases step with
      | head => exact ⟨transport.preservesAccept data.1 accepted.1, accepted.2⟩
      | tail child => exact ⟨accepted.1, codedPreserves rest child data.2 accepted.2⟩


theorem cast_accept {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {p q : RoleOccurrenceProfile roles} (same : p = q) (data : RoleProfilePayload p)
    (accepted : RoleSemantics.ProfileAccept p data) :
    RoleSemantics.ProfileAccept q (same ▸ data) := by
  cases same
  exact accepted


def act {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (step : (rules history).Step p q)
    (data : RoleProfilePayload p) : RoleProfilePayload q :=
  (decode_encode roles q) ▸ codedAction history step.down ((decode_encode roles p).symm ▸ data)

theorem act_preserves {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (step : (rules history).Step p q)
    (data : RoleProfilePayload p) (accepted : RoleSemantics.ProfileAccept p data) :
    RoleSemantics.ProfileAccept q (act history step data) := by
  exact cast_accept (decode_encode roles q) _
    (codedPreserves history step.down _ (cast_accept (decode_encode roles p).symm data accepted))

def normative {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) : Normative (rules history) :=
  ⟨RoleProfilePayload, RoleSemantics.ProfileAccept, act history, act_preserves history⟩

theorem all_trace_acceptance {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {p q} (trace : Trace (rules history).Step p q)
    (data : RoleProfilePayload p) (accepted : RoleSemantics.ProfileAccept p data) :
    RoleSemantics.ProfileAccept q ((normative history).transport trace data) :=
  (normative history).transport_preserves trace data accepted

def executed_path {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p q : RoleOccurrenceProfile roles) : ProjectionFamily.Path (projection (RoleStatus.executed reduction)) p q :=
  let joined := executed_join reduction p q
  (ProjectionFamily.Path.ofTrace (P := projection (RoleStatus.executed reduction))
    (stepIdentification _) joined.left).append
      (ProjectionFamily.Path.ofTrace (P := projection (RoleStatus.executed reduction))
        (stepIdentification _) joined.right).reverse

theorem executed_boundary {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (boundary : RoleOccurrenceProfile roles → Bool)
    (respects : ∀ slot p q, projection (RoleStatus.executed reduction) slot p =
      projection (RoleStatus.executed reduction) slot q → boundary p = boundary q)
    (p q : RoleOccurrenceProfile roles) : boundary p = boundary q :=
  ProjectionFamily.boundary_constant _ (executed_path reduction) boundary respects p q

theorem joint_injective {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) {n : Binary.Shape}
    (size : roleShape roles = .more (.more n)) (p q : RoleOccurrenceProfile roles)
    (agrees : ∀ slot, projection history slot p = projection history slot q) : p = q := by
  have coded : ∀ slot, Binary.projection (mask history) slot (encode roles p) =
      Binary.projection (mask history) slot (encode roles q) := by
    intro slot
    have same := congrArg (encode roles) (agrees slot)
    exact (encode_decode roles _).symm.trans (same.trans (encode_decode roles _))
  have encodedSame : encode roles p = encode roles q := by
    exact Binary.joint_injective_of_shape size _ _ _ coded
  exact (decode_encode roles p).symm.trans
    ((congrArg (decode roles) encodedSame).trans (decode_encode roles q))


def finiteSource {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} (roles : RelationalConstitutiveRoleHistory run) :
    FiniteImage.Source (RoleOccurrenceProfile roles) :=
  let source := roleProfileFiniteCarrier roles
  ⟨source.decEq, source.frontier, source.complete, source.nodup⟩

def composed {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) : FiniteImage.Composed (rules history) where
  frontier := (rolewiseObligationFrontier history.policy).map history.realize
  distinct := Extensive.nodup_map history.realize history.realize_injective (rolewiseObligationFrontier_nodup _)
  exact := by
    intro y
    constructor
    · intro member
      obtain ⟨q, _, same⟩ := Extensive.mem_map_preimage history.realize member
      cases same
      exact (normal_selected history _).trans (history.selected_realize q)
    · intro fixed
      have same : history.selected y = y := (normal_selected history y).symm.trans fixed
      have member := Extensive.mem_map history.realize (rolewiseObligationFrontier_complete history.policy (rolewiseCarry history.policy y))
      rw [history.realize_carry y, same] at member
      exact member

theorem composed_width {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) :
    (composed history).frontier.length = 2 ^ history.pendingCount :=
  (Extensive.length_map history.realize _).trans history.width

theorem exhaustive_width {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) :
    (FiniteImage.frontier (rules history) (finiteSource roles)).length = 2 ^ history.pendingCount :=
  (FiniteImage.composed_width (rules history) (finiteSource roles) (composed history)).trans (composed_width history)

def targetTransport {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) :
    ExactTransport (RolewiseObligation history.policy) (FiniteImage.Target (rules history)) where
  forward := fun q => ⟨history.realize q, (normal_selected history _).trans (history.selected_realize q)⟩
  backward := fun target => rolewiseCarry history.policy target.1
  forwardBackward := history.carry_realize
  backwardForward := fun target => Subtype.ext
    ((history.realize_carry target.1).trans ((normal_selected history target.1).symm.trans target.2))

theorem targetTransport_carry {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    (history : RoleStatus.History roles) (p : RoleOccurrenceProfile roles) :
    (targetTransport history).forward (rolewiseCarry history.policy p) = FiniteImage.carry (rules history) p :=
  Subtype.ext ((history.realize_carry p).trans (normal_selected history p).symm)

theorem canonical_output {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state} {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles} (reduction : ExecutedRoleReductionHistory program)
    (p : RoleOccurrenceProfile roles) :
    RoleStatus.executedPayloadOutput reduction p ((RoleStatus.executed reduction).transform p
      (canonicalRoleProfilePayload roles p)) = retainedExecutedOperationalTargetProfile reduction :=
  (RoleStatus.executed_action_exact reduction p (canonicalRoleProfilePayload roles p)).trans
    (RoleSemantics.canonicalAction_exact reduction p)

end ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.code
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.rules
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normal_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normalize
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.carry_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.family
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.stepIdentification
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.projection_fibres
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.executed_normal
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.executed_join
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.stagewise_normal
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.codedAction
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normative
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.all_trace_acceptance
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.executed_path
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.executed_boundary
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.joint_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.composed
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.exhaustive_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.targetTransport
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.targetTransport_carry
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.canonical_output
/- AXIOM_AUDIT_END -/
