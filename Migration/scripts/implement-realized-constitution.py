#!/usr/bin/env python3
"""Deterministic, branch-local repair against the reviewed immutable baseline.

The generator writes only the three production modules named below and one
regression module. It never changes the scientific target or verification gates.
"""
from pathlib import Path
import subprocess

BASE = "5617ab4b09e5c0c044645737acd62973457b9a59"
ROOT = Path(__file__).resolve().parents[1]
PREFIX = "RelationalPerimeter/Computation/ConstitutiveSearch/"
ED = PREFIX + "EndogenousDecomposition/"

def original(path):
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT, text=True)

def once(text, old, new):
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"Expected one occurrence, got {count}: {old[:100]!r}")
    return text.replace(old, new, 1)

def section(text, start, end, replacement):
    a = text.index(start)
    b = text.index(end, a)
    return text[:a] + replacement.rstrip() + "\n\n" + text[b:]

def save(path, text):
    destination = ROOT / path
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(text.rstrip() + "\n", encoding="utf-8")
    print("GENERATED", path)

subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=True)

path = PREFIX + "RelationalProfileConstitution.lean"
s = original(path)
s = section(s, "/--\nAn identity constituted at one relational stage.", "/-- A profile of identities constituted at every relational role. -/", r'''
/-- Recover a formation witness for an arbitrary realized occurrence. -/
def RelationalOpeningStage.formationAt
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) :
    stage.FormationRelation stage.role occurrence := by
  have witness := stage.formationAgreement (stage.classify occurrence)
  rw [stage.realize_classify occurrence] at witness
  exact witness

/-- Recover provenance through the exact realization, not a position copy. -/
def RelationalOpeningStage.provenanceAt
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) :
    stage.ProvenanceRelation stage.provenance stage.role occurrence := by
  have witness := stage.provenanceAgreement (stage.classify occurrence)
  rw [stage.realize_classify occurrence] at witness
  exact witness

/--
A constituted identity carries its actual realization and all four positive
witnesses. Exactness pins those Type-valued witnesses to the canonical witnesses
of this stage; their possible multiplicity therefore does not change width.
No position is substituted for the realized occurrence.
-/
structure RelationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) : Type where
  private mk ::
  realized : stage.Occurrence
  sourceWitness : stage.SourceRelation source stage.role
  sourceWitnessExact : sourceWitness = stage.sourceWitness
  formationWitness : stage.FormationRelation stage.role realized
  formationWitnessExact : formationWitness = stage.formationAt realized
  targetWitness : stage.TargetRelation stage.role next
  targetWitnessExact : targetWitness = stage.targetWitness
  provenanceWitness :
    stage.ProvenanceRelation stage.provenance stage.role realized
  provenanceWitnessExact : provenanceWitness = stage.provenanceAt realized

/-- Constitute an already realized occurrence with its canonical witnesses. -/
def constituteRealizedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) : RelationallyConstitutedOccurrence stage :=
  { realized := occurrence
    sourceWitness := stage.sourceWitness
    sourceWitnessExact := rfl
    formationWitness := stage.formationAt occurrence
    formationWitnessExact := rfl
    targetWitness := stage.targetWitness
    targetWitnessExact := rfl
    provenanceWitness := stage.provenanceAt occurrence
    provenanceWitnessExact := rfl }

/-- Classify the actual realization to recover its historical position. -/
def RelationallyConstitutedOccurrence.position
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) : stage.Position :=
  stage.classify identity.realized

/-- Realization precedes the construction of the witnessed identity. -/
def relationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (position : stage.Position) : RelationallyConstitutedOccurrence stage :=
  constituteRealizedOccurrence stage (stage.realize position)

/-- Canonical witnesses make reconstitution exact without an extra quotient. -/
theorem RelationallyConstitutedOccurrence.reconstitute
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    constituteRealizedOccurrence stage identity.realized = identity := by
  rcases identity with
    ⟨value, sw, swExact, fw, fwExact, tw, twExact, pw, pwExact⟩
  cases swExact
  cases fwExact
  cases twExact
  cases pwExact
  rfl

/-- This return law uses the classification-realization law of the stage. -/
theorem relationallyConstitutedOccurrence_position
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (position : stage.Position) :
    (relationallyConstitutedOccurrence stage position).position = position :=
  stage.classify_realize position

/-- This return law uses actual realization and canonical witness exactness. -/
theorem relationallyConstitutedOccurrence_roundTrip
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    relationallyConstitutedOccurrence stage identity.position = identity := by
  change constituteRealizedOccurrence stage
    (stage.realize (stage.classify identity.realized)) = identity
  rw [stage.realize_classify identity.realized]
  exact identity.reconstitute

/-- Exact incorporation of actual occurrences into witnessed identities. -/
def RelationalOpeningStage.constitutedOccurrenceTransport
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    ExactTypeTransport stage.Occurrence (RelationallyConstitutedOccurrence stage) :=
  { forward := constituteRealizedOccurrence stage
    backward := RelationallyConstitutedOccurrence.realized
    forwardBackward := fun _ => rfl
    backwardForward := RelationallyConstitutedOccurrence.reconstitute }

/-- Recover the formation witness carried by this particular identity. -/
def RelationalOpeningStage.formationWitness
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.FormationRelation stage.role identity.realized :=
  identity.formationWitness

/-- Recover the provenance witness carried by the same identity. -/
def RelationalOpeningStage.provenanceWitness
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.ProvenanceRelation stage.provenance stage.role identity.realized :=
  identity.provenanceWitness

/-- Equality is inherited through the exact realized occurrence transport. -/
def relationallyConstitutedOccurrenceDecEq
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    DecidableEq (RelationallyConstitutedOccurrence stage) :=
  fun left right =>
    match stage.positionDecEq left.position right.position with
    | isTrue same => isTrue (by
        calc
          left = relationallyConstitutedOccurrence stage left.position :=
            (relationallyConstitutedOccurrence_roundTrip left).symm
          _ = relationallyConstitutedOccurrence stage right.position :=
            congrArg (relationallyConstitutedOccurrence stage) same
          _ = right := relationallyConstitutedOccurrence_roundTrip right)
    | isFalse different =>
        isFalse (fun same => different
          (congrArg RelationallyConstitutedOccurrence.position same))
''')
s = once(s, "exact Prod.ext rfl\n        (relationalPositionProfile_roundTrip tail profile.2)", "exact Prod.ext (head.classify_realize profile.1)\n        (relationalPositionProfile_roundTrip tail profile.2)")
s = once(s, "      cases profile.1\n      exact Prod.ext rfl\n        (relationalOccurrenceProfile_roundTrip tail profile.2)", "      exact Prod.ext (relationallyConstitutedOccurrence_roundTrip profile.1)\n        (relationalOccurrenceProfile_roundTrip tail profile.2)")
s = once(s, "  cases identity\n  exact realizedMember", "  exact (relationallyConstitutedOccurrence_roundTrip identity) ▸ realizedMember")
s = once(s, "    (fun {_left _right} same => by\n      exact congrArg RelationallyConstitutedOccurrence.position same)\n    stage.positionNodup", "    (fun {left right} same => by\n      have classified := congrArg RelationallyConstitutedOccurrence.position same\n      exact Eq.trans (stage.classify_realize left).symm\n        (Eq.trans classified (stage.classify_realize right)))\n    stage.positionNodup")
s = once(s, "/- AXIOM_AUDIT_BEGIN -/", "\n".join([
    "/- AXIOM_AUDIT_BEGIN -/",
    "#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.formationAt",
    "#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.provenanceAt",
    "#print axioms ConstitutiveSearch.RelationalExtensive.constituteRealizedOccurrence",
    "#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.reconstitute",
    "#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence_position",
    "#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence_roundTrip",
    "#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.constitutedOccurrenceTransport",
]))
save(path, s)

path = ED + "RoleIndexedProfiles.lean"
s = original(path)
s = once(s, "  cases identity\n  rfl\n\n/-- Realize a constituted role identity", "  exact relationallyConstitutedOccurrence_roundTrip identity\n\n/-- Realize a constituted role identity")
s = once(s, "  { sourceWitness := (generalOpeningStageOfRole role).sourceWitness\n    targetWitness := (generalOpeningStageOfRole role).targetWitness", "  { sourceWitness := identity.sourceWitness\n    targetWitness := identity.targetWitness")
s = section(s, "/--\nEliminate the four primitive relations in constitutive order.", "/-- The general-stage transport is the authoritative occurrence realization. -/", r'''
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
''')
s = once(s, "#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleConstitutionEvidence.eliminate", "#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleConstitutionEvidence.transportFormation\n#print axioms ConstitutiveSearch.EndogenousDecomposition.eliminateRoleConstitutedOccurrence")
save(path, s)

path = ED + "RoleIndexedProgram.lean"
s = original(path)
s = section(s, "/-- Payload type selected by the actual role occurrence. -/", "theorem interpretCompiledRoleStage_left", r'''
/-- The input payload is typed by the actual realized structural state. -/
def RoleOpeningPayload
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (occurrence : RoleConstitutedOccurrence role) : Type :=
  GeneratedStructuralBranchContinuation occurrence.realized.state

/--
First use the actual formation agreement to transport the input continuation.
Only then select the transformed or retained case at its historical position.
The total relation action and its acceptance-preservation theorem stay separate.
-/
def interpretRoleStageAtom
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role)
    (occurrence : RoleConstitutedOccurrence role)
    (constitution : RoleConstitutionEvidence role occurrence)
    (continuation : RoleOpeningPayload occurrence) :
    GeneratedStructuralBranchContinuation
      (causalOpeningRight source run.selected run.fresh) := by
  have atPosition : GeneratedStructuralBranchContinuation
      (occurrence.position.state role) :=
    constitution.transportFormation
      (Motive := GeneratedStructuralBranchContinuation) continuation
  cases positionExact : occurrence.position with
  | left =>
      rw [positionExact] at atPosition
      exact atom.action atPosition
  | right =>
      rw [positionExact] at atPosition
      exact atPosition
''')
s = section(s, "/-- Canonical accepted payload for every already constituted profile. -/", "/-- Executed retained assignment at every role, read from the role history. -/", r'''
/-- Canonical payload, reconstructed through the realized occurrence eliminator. -/
def canonicalRoleProfilePayload :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      RoleProfilePayload profile
  | _, _, _, .nil, profile => by cases profile; exact ()
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleConstitutedOccurrence headRole ×
        RoleOccurrenceProfile tailRoles at profile
      exact eliminateRoleConstitutedOccurrence headRole profile.1
        (motive := fun occurrence =>
          RoleOpeningPayload occurrence × RoleProfilePayload profile.2)
        (headRole.executedInput,
          canonicalRoleProfilePayload tailRoles profile.2)
        (headRole.completedOutput,
          canonicalRoleProfilePayload tailRoles profile.2)
''')
s = section(s, "/--\nThe compiled program normalizes every accepted profile", "end EndogenousDecomposition", r'''
/-- The canonical payloads normalize to outputs of the same executed history. -/
theorem interpretCompiledRoleHistory_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      (profile : RoleOccurrenceProfile roles) →
      interpretRoleOccurrenceProfile
          (compileRoleHistory roles) profile
          (canonicalRoleProfilePayload roles profile) =
        completedRoleAssignments roles
  | _, _, _, .nil, profile => by cases profile; rfl
  | _, _, _, .step headRole tailRoles, profile => by
      change RoleConstitutedOccurrence headRole ×
        RoleOccurrenceProfile tailRoles at profile
      rcases profile with ⟨headOccurrence, tailProfile⟩
      refine eliminateRoleConstitutedOccurrence headRole headOccurrence
        (motive := fun occurrence =>
          interpretRoleOccurrenceProfile
              (compileRoleHistory
                (RelationalConstitutiveRoleHistory.step headRole tailRoles))
              (occurrence, tailProfile)
              (canonicalRoleProfilePayload
                (RelationalConstitutiveRoleHistory.step headRole tailRoles)
                (occurrence, tailProfile)) =
            completedRoleAssignments
              (RelationalConstitutiveRoleHistory.step headRole tailRoles)) ?_ ?_
      · change
          ((compileRoleStageAtom headRole).action headRole.executedInput).1 ::
              interpretRoleOccurrenceProfile (compileRoleHistory tailRoles)
                tailProfile (canonicalRoleProfilePayload tailRoles tailProfile) =
            headRole.completedOutput.1 :: completedRoleAssignments tailRoles
        have headExact :
            (compileRoleStageAtom headRole).action headRole.executedInput =
              headRole.completedOutput :=
          Eq.trans (compileRoleStageAtom_action_exact headRole headRole.executedInput)
            headRole.actionExact.symm
        rw [congrArg Subtype.val headExact]
        exact congrArg (List.cons headRole.completedOutput.1)
          (interpretCompiledRoleHistory_exact tailRoles tailProfile)
      · change
          headRole.completedOutput.1 ::
              interpretRoleOccurrenceProfile (compileRoleHistory tailRoles)
                tailProfile (canonicalRoleProfilePayload tailRoles tailProfile) =
            headRole.completedOutput.1 :: completedRoleAssignments tailRoles
        exact congrArg (List.cons headRole.completedOutput.1)
          (interpretCompiledRoleHistory_exact tailRoles tailProfile)
''')
save(path, s)

save("Tests/RealizedConstitutionRegression.lean", r'''
import RelationalPerimeter

/-! Regression checks for actual realization, witnessed identities and one public carrier. -/
namespace RealizedConstitutionRegression
open ConstitutiveSearch
open RelationalExtensive
open EndogenousDecomposition

/-- A nonidentity realization separates realized values from their positions. -/
def flipStage : RelationalOpeningStage Nat 0 1 :=
  { Role := Unit
    Position := Bool
    Occurrence := Bool
    Provenance := Nat
    SourceRelation := fun observed _ => PLift (observed = 0)
    FormationRelation := fun _ occurrence => PLift ((!(!occurrence)) = occurrence)
    TargetRelation := fun _ observed => PLift (observed = 1)
    ProvenanceRelation := fun provenance _ occurrence =>
      PLift (provenance = 0) × PLift (occurrence = occurrence)
    role := ()
    provenance := 0
    sourceWitness := ⟨rfl⟩
    targetWitness := ⟨rfl⟩
    positionDecEq := inferInstance
    positionFrontier := [false, true]
    positionComplete := fun position => by
      cases position with
      | false => exact .head _
      | true => exact .tail _ (.head _)
    positionNodup := by
      exact .cons
        (fun value member same => by
          cases member with
          | head => cases same
          | tail _ impossible => cases impossible)
        (.cons (fun _ impossible _ => nomatch impossible) .nil)
    realize := Bool.not
    classify := Bool.not
    realize_classify := fun occurrence => by cases occurrence <;> rfl
    classify_realize := fun position => by cases position <;> rfl
    formationAgreement := fun position => by cases position <;> exact ⟨rfl⟩
    provenanceAgreement := fun _ => ⟨⟨rfl⟩, ⟨rfl⟩⟩ }

example : (relationallyConstitutedOccurrence flipStage false).realized = true := rfl
example : (relationallyConstitutedOccurrence flipStage false).position = false := rfl
example : (constituteRealizedOccurrence flipStage true).position = false := rfl

/-- Exact return uses realized data even when realization is not identity. -/
theorem flip_roundTrip (identity : RelationallyConstitutedOccurrence flipStage) :
    relationallyConstitutedOccurrence flipStage identity.position = identity :=
  relationallyConstitutedOccurrence_roundTrip identity

/-- All four carried witnesses agree with the same stage, including Type data. -/
theorem witnesses_exact
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    identity.sourceWitness = stage.sourceWitness ∧
    identity.formationWitness = stage.formationAt identity.realized ∧
    identity.targetWitness = stage.targetWitness ∧
    identity.provenanceWitness = stage.provenanceAt identity.realized :=
  ⟨identity.sourceWitnessExact, identity.formationWitnessExact,
    identity.targetWitnessExact, identity.provenanceWitnessExact⟩

example (input : Nat) :
    (publicRoleProfileFiniteCarrier input).Identity =
      RoleOccurrenceProfile (publicRelationalConstitutiveRoles input) := rfl

example (input : Nat) :
    (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
      (index := input) ()).Identity =
      (publicRoleProfileFiniteCarrier input).Identity := rfl

example (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  publicCertificate_executedRegime_width input

example (input : Nat)
    (regime : Extensive.ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔ Function.Injective regime.carry :=
  publicCertificate_exponential_iff_carry_injective input regime

end RealizedConstitutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RealizedConstitutionRegression.flipStage
#print axioms RealizedConstitutionRegression.flip_roundTrip
#print axioms RealizedConstitutionRegression.witnesses_exact
/- AXIOM_AUDIT_END -/
''')
