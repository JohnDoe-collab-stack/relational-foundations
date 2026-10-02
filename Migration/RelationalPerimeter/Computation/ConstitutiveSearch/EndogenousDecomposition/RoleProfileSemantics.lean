import RelationalPerimeter.Computation.ConstitutiveSearch.SemanticImage
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Semantic action and admission obligations on the authoritative profiles

The structural action is total. Its acceptance preservation is obtained from
an ordered chain independently of the action. Canonical convergence is a
separate result about the data actually executed, not about all continuations.
-/
namespace ConstitutiveSearch.EndogenousDecomposition.RoleSemantics
open ConstitutiveSearch.SAT

/-- Pointwise acceptance; this does not assert a new global SAT semantics. -/
def ProfileAccept :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (p : RoleOccurrenceProfile roles) → RoleProfilePayload p → Prop
  | _, _, _, .nil, _, _ => True
  | _, _, _, .step _ _, p, c => LocalAccept p.1 c.1 ∧ ProfileAccept p.2 c.2

/-- Acceptance of the actual target continuation at every executed role. -/
def TargetAccept :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    ExecutedOperationalTargetProfile reduction → Prop
  | _, _, _, _, _, .nil, _ => True
  | _, state, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ head _ _ _ _ _ _ tail, value =>
      GeneratedStructuralBranchAccept
        (causalOpeningRight state head.selected head.fresh) value.1 ∧
        TargetAccept tail value.2

/-- Structural interpretation of arbitrary payloads on the authoritative carrier. -/
def actProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (p : RoleOccurrenceProfile roles) → RoleProfilePayload p →
    ExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil, _, _ => ()
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ _ _ atom _ _ tail, p, c =>
      (interpretRoleStageAtom atom p.1 (roleConstitutionEvidence _ p.1) c.1,
        actProfile tail p.2 c.2)

/-- The local semantic consumer uses preservation only after structural action. -/
theorem localPreserves
    {state : CausalConstitutiveState} {run : CausalConstitutiveStageExecution state}
    {role : RelationalConstitutiveRoleStage run}
    (atom : RoleStageAtom role)
    (preserves : ∀ c : GeneratedStructuralBranchContinuation
        (causalOpeningLeft state run.selected run.fresh),
      GeneratedStructuralBranchAccept (causalOpeningLeft state run.selected run.fresh) c →
      GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
        (atom.action c))
    (o : RoleConstitutedOccurrence role) :
    ∀ c : RoleOpeningPayload o, LocalAccept o c →
      GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
        (interpretRoleStageAtom atom o (roleConstitutionEvidence role o) c) := by
  refine eliminateRoleConstitutedOccurrence role o
    (motive := fun o => ∀ c : RoleOpeningPayload o, LocalAccept o c →
      GeneratedStructuralBranchAccept (causalOpeningRight state run.selected run.fresh)
        (interpretRoleStageAtom atom o (roleConstitutionEvidence role o) c)) ?_ ?_
  · intro c accepted
    exact preserves c accepted
  · intro c accepted
    exact accepted

/-- Universal preservation consumes the actual chain's ordered witnesses. -/
theorem profilePreserves :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    {reduction : ExecutedRoleReductionHistory program} →
    {chain : ExecutedReductionConstitutiveChain reduction} →
    ExecutedReductionPreservationExact chain →
    (p : RoleOccurrenceProfile roles) → (c : RoleProfilePayload p) →
    ProfileAccept p c → TargetAccept reduction (actProfile reduction p c)
  | _, _, _, _, _, _, _, .nil, _, _, _ => True.intro
  | _, _, _, _, _, _, _, .step preserves rest, p, c, accepted =>
      ⟨localPreserves _ preserves p.1 c.1 accepted.1,
        profilePreserves rest p.2 c.2 accepted.2⟩

/-- Independent source-identity obligation, not needed to define raw action. -/
def SourcesRemainDistinct :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    ExecutedRoleReductionHistory program → Prop
  | _, _, _, _, _, .nil => True
  | _, _, _, _, _, .step license tail =>
      license.transformedOccurrence ≠ license.retainedOccurrence ∧ SourcesRemainDistinct tail

theorem sourcesRemainDistinct :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    {reduction : ExecutedRoleReductionHistory program} →
    {chain : ExecutedReductionConstitutiveChain reduction} →
    ExecutedReductionOccurrenceSeparationExact chain → SourcesRemainDistinct reduction
  | _, _, _, _, _, _, _, .nil => True.intro
  | _, _, _, _, _, _, _, .step separate rest => ⟨separate, sourcesRemainDistinct rest⟩

/-- Agreement only for the executed canonical payloads, not all continuations. -/
theorem canonicalAction_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (p : RoleOccurrenceProfile roles) →
    actProfile reduction p (canonicalRoleProfilePayload roles p) =
      retainedExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil, p => by cases p; rfl
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ role roles atom _ license tailReduction, p => by
      rcases p with ⟨o, rest⟩
      refine eliminateRoleConstitutedOccurrence role o
        (motive := fun o => actProfile (.step license tailReduction)
          (o, rest) (canonicalRoleProfilePayload (.step role roles) (o, rest)) =
            retainedExecutedOperationalTargetProfile (.step license tailReduction)) ?_ ?_
      · change (atom.action role.executedInput,
            actProfile tailReduction rest (canonicalRoleProfilePayload roles rest)) =
          (role.completedOutput, retainedExecutedOperationalTargetProfile tailReduction)
        have headExact : atom.action role.executedInput = role.completedOutput := by
          unfold RoleStageAtom.action
          rw [atom.returnedRelationExact]
          exact role.actionExact.symm
        exact Prod.ext headExact (canonicalAction_exact tailReduction rest)
      · change (role.completedOutput,
            actProfile tailReduction rest (canonicalRoleProfilePayload roles rest)) =
          (role.completedOutput, retainedExecutedOperationalTargetProfile tailReduction)
        exact Prod.ext rfl (canonicalAction_exact tailReduction rest)


/-- Select retained occurrences without identifying any other source profile. -/
def retainedSelection :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    ExecutedRoleReductionHistory program → RoleOccurrenceProfile roles
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ role _ _ _ _ rest =>
      (roleConstitutedOccurrenceAt role .right, retainedSelection rest)

/-- Include retained continuation data back into the extensive source domain. -/
def includeTarget :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    ExecutedOperationalTargetProfile reduction → RoleProfilePayload (retainedSelection reduction)
  | _, _, _, _, _, .nil, _ => ()
  | _, _, _, _, _, .step _ rest, target => (target.1, includeTarget rest target.2)

/-- Reflection uses the unchanged retained alternatives, not an inverse of absorption. -/
theorem includeTarget_preserves :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    (reduction : ExecutedRoleReductionHistory program) →
    (target : ExecutedOperationalTargetProfile reduction) →
    TargetAccept reduction target →
    ProfileAccept (retainedSelection reduction) (includeTarget reduction target)
  | _, _, _, _, _, .nil, _, _ => True.intro
  | _, _, _, _, _, .step _ rest, target, accepted =>
      ⟨accepted.1, includeTarget_preserves rest target.2 accepted.2⟩

/-- All four agreements are recovered from the occurrence's own evidence. -/
def LocalConstitution
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    (o : RoleConstitutedOccurrence role) : Prop :=
  role.searchState = source ∧ role.provenance = source.provenance ∧
    o.realized.state = o.position.state role ∧ role.nextState = run.next

theorem localConstitution
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {o : RoleConstitutedOccurrence role}
    (evidence : RoleConstitutionEvidence role o) : LocalConstitution o :=
  ⟨evidence.sourceWitness.down,
    Eq.trans evidence.provenanceWitness.1.down
      (congrArg CausalConstitutiveState.provenance evidence.sourceWitness.down),
    evidence.formationWitness.2.down, evidence.targetWitness.down⟩

def ProfileConstitution :
    {count : Nat} → {source : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count source} →
    {roles : RelationalConstitutiveRoleHistory run} → RoleOccurrenceProfile roles → Prop
  | _, _, _, .nil, _ => True
  | _, _, _, .step _ _, p => LocalConstitution p.1 ∧ ProfileConstitution p.2

theorem profileConstitution :
    {count : Nat} → {source : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count source} →
    {roles : RelationalConstitutiveRoleHistory run} →
    (p : RoleOccurrenceProfile roles) → ProfileConstitution p
  | _, _, _, .nil, _ => True.intro
  | _, _, _, .step role _, p =>
      ⟨localConstitution (roleConstitutionEvidence role p.1), profileConstitution p.2⟩

/-- Both local evidence values cover the constituted occurrence carrier. -/
theorem localConstitutionFromBoth
    {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run} {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (leftEvidence : RoleConstitutionEvidence role license.transformedOccurrence)
    (rightEvidence : RoleConstitutionEvidence role license.retainedOccurrence)
    (o : RoleConstitutedOccurrence role) : LocalConstitution o := by
  refine eliminateRoleConstitutedOccurrence role o
    (motive := LocalConstitution) ?_ ?_
  · exact license.transformedOccurrenceExact ▸ localConstitution leftEvidence
  · exact license.retainedOccurrenceExact ▸ localConstitution rightEvidence

/-- The whole-profile agreement consumes this exact chain's relational evidence. -/
theorem profileConstitutionFromChain :
    {count : Nat} → {source : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count source} →
    {roles : RelationalConstitutiveRoleHistory run} →
    {program : RoleIndexedProgram roles} →
    {reduction : ExecutedRoleReductionHistory program} →
    {chain : ExecutedReductionConstitutiveChain reduction} →
    ExecutedReductionRelationalConstitutionExact chain →
    (p : RoleOccurrenceProfile roles) → ProfileConstitution p
  | _, _, _, _, _, _, _, .nil, _ => True.intro
  | _, _, _, _, _, _, _, .step leftEvidence rightEvidence rest, p =>
      ⟨localConstitutionFromBoth leftEvidence rightEvidence p.1,
        profileConstitutionFromChain rest p.2⟩

/-- The action's step equation is specified on arbitrary, not canonical, data. -/
theorem actProfile_step
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {role : RelationalConstitutiveRoleStage head}
    {roles : RelationalConstitutiveRoleHistory tail}
    {atom : RoleStageAtom role} {program : RoleIndexedProgram roles}
    (license : ExecutedRoleReductionLicense role atom)
    (rest : ExecutedRoleReductionHistory program)
    (o : RoleConstitutedOccurrence role) (p : RoleOccurrenceProfile roles)
    (c : RoleOpeningPayload o) (payload : RoleProfilePayload p) :
    actProfile (.step license rest) (o,p) (c,payload) =
      (interpretRoleStageAtom atom o (roleConstitutionEvidence role o) c,
        actProfile rest p payload) := rfl

/-- Every constituted source profile has positive accepted data. Operational
regrouping does not establish impossibility of any of these source profiles. -/
theorem canonicalPayload_accepted :
    {count : Nat} → {state : CausalConstitutiveState} →
    {run : CausalConstitutiveExecutionHistory count state} →
    (roles : RelationalConstitutiveRoleHistory run) →
    (p : RoleOccurrenceProfile roles) →
    ProfileAccept p (canonicalRoleProfilePayload roles p)
  | _, _, _, .nil, p => by cases p; exact True.intro
  | _, _, _, @RelationalConstitutiveRoleHistory.step
      _ _ head _ role roles, p => by
      rcases p with ⟨occurrence, rest⟩
      refine eliminateRoleConstitutedOccurrence role occurrence
        (motive := fun o => ProfileAccept (roles := .step role roles) (o, rest)
          (canonicalRoleProfilePayload (.step role roles) (o, rest))) ?_ ?_
      · refine ⟨?_, canonicalPayload_accepted roles rest⟩
        change GeneratedStructuralBranchAccept _ role.executedInput
        rw [role.executedInputExact]
        exact head.sourceAccepted
      · exact ⟨role.preservation, canonicalPayload_accepted roles rest⟩

end ConstitutiveSearch.EndogenousDecomposition.RoleSemantics
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.canonicalPayload_accepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.retainedSelection
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.includeTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.includeTarget_preserves

#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.localConstitutionFromBoth
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.profileConstitutionFromChain
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.ProfileAccept
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.TargetAccept
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.actProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.localPreserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.profilePreserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.SourcesRemainDistinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.sourcesRemainDistinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.canonicalAction_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.LocalConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.localConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.ProfileConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.profileConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.RoleSemantics.actProfile_step
/- AXIOM_AUDIT_END -/
