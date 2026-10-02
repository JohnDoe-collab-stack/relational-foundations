import Init
set_option genInjectivity false

/-!
# Unique residual role in a faithfully segmented realization

This module isolates the occurrence argument used by
`StrongPerimetralTurning`.  It has no dependency on circular presentations,
differences, provenance, loops, junctions, or totalizations.

The abstract input consists of an exact realization of the internal roles,
disjoint embeddings of the old and new occurrences into an extended
realization, an injective labelling by internal or residual roles, and a
contractible residual role type.  The output is that every new occurrence has
the residual label and that any two new occurrences coincide.  A positive new
part therefore has one distinguished occurrence and no other one.
-/

namespace RelationalFoundations.Residual

universe uInternal uResidual uOld uNew uExtended

/- A contractible residual role is constructively inhabited and has exactly
   one value.  No decidable equality or classical choice is required. -/
structure ContractibleRole (Role : Type uResidual) where
  center : Role
  contracts : (role : Role) → role = center

/- Exact realization is stored as two explicit maps with both round trips.
   The residual-role proof below only consumes the forward realization; the
   stronger structure records the exact scientific interface intended for
   later instantiations. -/
structure ExactInternalRealization
    (InternalRole : Type uInternal)
    (OldOccurrence : Type uOld) where
  roleToOccurrence : InternalRole → OldOccurrence
  occurrenceToRole : OldOccurrence → InternalRole
  occurrenceRoundTrip :
    (occurrence : OldOccurrence) →
      roleToOccurrence (occurrenceToRole occurrence) = occurrence
  roleRoundTrip :
    (role : InternalRole) →
      occurrenceToRole (roleToOccurrence role) = role

/- `FaithfulExtension` contains precisely the dependency boundary of the
   residual-role argument.  `embedOld` and `embedNew` need not arise from a
   particular history representation; only their disjointness and the
   injectivity of the new embedding are used. -/
structure FaithfulExtension
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (NewOccurrence : Type uNew)
    (ExtendedOccurrence : Type uExtended)
    (internal : ExactInternalRealization InternalRole OldOccurrence)
    (residual : ContractibleRole ResidualRole) where
  embedOld : OldOccurrence → ExtendedOccurrence
  embedNew : NewOccurrence → ExtendedOccurrence
  oldNewDisjoint :
    (oldOccurrence : OldOccurrence) →
    (newOccurrence : NewOccurrence) →
      embedOld oldOccurrence ≠ embedNew newOccurrence
  embedNewInjective : Function.Injective embedNew
  label : ExtendedOccurrence → InternalRole ⊕ ResidualRole
  preservesInternal :
    (role : InternalRole) →
      label (embedOld (internal.roleToOccurrence role)) = .inl role
  labelFaithful :
    (first second : ExtendedOccurrence) →
      label first = label second → first = second

/- The residual derivation consumes only the forward placement of internal
   roles.  This kernel keeps exactly the fields used by that derivation; it
   does not claim that every retained field is indispensable to every possible
   proof of the same conclusion. -/
structure ResidualUniquenessKernel
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (NewOccurrence : Type uNew)
    (ExtendedOccurrence : Type uExtended)
    (residual : ContractibleRole ResidualRole) where
  roleToOccurrence : InternalRole → OldOccurrence
  embedOld : OldOccurrence → ExtendedOccurrence
  embedNew : NewOccurrence → ExtendedOccurrence
  oldNewDisjoint :
    (oldOccurrence : OldOccurrence) →
    (newOccurrence : NewOccurrence) →
      embedOld oldOccurrence ≠ embedNew newOccurrence
  embedNewInjective : Function.Injective embedNew
  label : ExtendedOccurrence → InternalRole ⊕ ResidualRole
  preservesInternal :
    (role : InternalRole) →
      label (embedOld (roleToOccurrence role)) = .inl role
  labelFaithful :
    (first second : ExtendedOccurrence) →
      label first = label second → first = second

/- A positive new part supplies an actual new occurrence. -/
structure PositiveNewPart (NewOccurrence : Type uNew) where
  occurrence : NewOccurrence

/- The actually consumed residual-determination interface.  It retains only
   the new occurrence, its internal-or-residual label, injectivity of that
   label, and exclusion of internal labels.  In particular, this core has no
   dependency on old occurrences or on an extended occurrence carrier. -/
structure ResidualDeterminationCore
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (NewOccurrence : Type uNew)
    (residual : ContractibleRole ResidualRole) where
  newLabel : NewOccurrence → InternalRole ⊕ ResidualRole
  newLabelInjective : Function.Injective newLabel
  noInternalReuse :
    (occurrence : NewOccurrence) →
    (role : InternalRole) →
      newLabel occurrence ≠ .inl role

namespace ResidualDeterminationCore

theorem label_is_residual
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual)
    (occurrence : NewOccurrence) :
    core.newLabel occurrence = .inr residual.center := by
  cases labelEquality : core.newLabel occurrence with
  | inl role =>
      exact False.elim
        (core.noInternalReuse occurrence role labelEquality)
  | inr role =>
      exact congrArg Sum.inr (residual.contracts role)

theorem occurrences_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual)
    (first second : NewOccurrence) :
    first = second := by
  have sameLabel :
      core.newLabel first = core.newLabel second :=
    (core.label_is_residual first).trans
      (core.label_is_residual second).symm
  exact core.newLabelInjective sameLabel

end ResidualDeterminationCore

/- The proof-relevant output of the factorized core is indexed only by that
   core.  No old-occurrence or extended-carrier data is required here. -/
structure CoreUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual) where
  occurrence : NewOccurrence
  labelIsResidual :
    core.newLabel occurrence = .inr residual.center
  unique : (other : NewOccurrence) → other = occurrence

def positiveCore_hasUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : ContractibleRole ResidualRole}
    (core : ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual)
    (positive : PositiveNewPart NewOccurrence) :
    CoreUniqueResidualOccurrence core :=
  { occurrence := positive.occurrence
    labelIsResidual := core.label_is_residual positive.occurrence
    unique := fun other => core.occurrences_unique other positive.occurrence }

namespace FaithfulExtension

def toResidualUniquenessKernel
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual) :
    ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual :=
  { roleToOccurrence := internal.roleToOccurrence
    embedOld := extension.embedOld
    embedNew := extension.embedNew
    oldNewDisjoint := extension.oldNewDisjoint
    embedNewInjective := extension.embedNewInjective
    label := extension.label
    preservesInternal := extension.preservesInternal
    labelFaithful := extension.labelFaithful }

end FaithfulExtension

namespace ResidualUniquenessKernel

theorem newOccurrence_cannotReuseInternalRole
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (newOccurrence : NewOccurrence)
    (role : InternalRole)
    (labelEquality :
      kernel.label (kernel.embedNew newOccurrence) = .inl role) :
    False := by
  have sameLabel :
      kernel.label (kernel.embedOld (kernel.roleToOccurrence role)) =
        kernel.label (kernel.embedNew newOccurrence) :=
    (kernel.preservesInternal role).trans labelEquality.symm
  have sameOccurrence := kernel.labelFaithful
    (kernel.embedOld (kernel.roleToOccurrence role))
    (kernel.embedNew newOccurrence) sameLabel
  exact kernel.oldNewDisjoint
    (kernel.roleToOccurrence role) newOccurrence sameOccurrence

def toDeterminationCore
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual) :
    ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual :=
  { newLabel := fun occurrence =>
      kernel.label (kernel.embedNew occurrence)
    newLabelInjective := by
      intro first second labelEquality
      apply kernel.embedNewInjective
      exact kernel.labelFaithful
        (kernel.embedNew first) (kernel.embedNew second) labelEquality
    noInternalReuse := by
      intro occurrence role labelEquality
      exact kernel.newOccurrence_cannotReuseInternalRole
        occurrence role labelEquality }

theorem newOccurrence_label_is_residual
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (newOccurrence : NewOccurrence) :
    kernel.label (kernel.embedNew newOccurrence) =
      .inr residual.center :=
  kernel.toDeterminationCore
    |>.label_is_residual newOccurrence

theorem newOccurrences_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (first second : NewOccurrence) : first = second := by
  exact kernel.toDeterminationCore
    |>.occurrences_unique first second

end ResidualUniquenessKernel

namespace FaithfulExtension

theorem newOccurrence_cannotReuseInternalRole
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (newOccurrence : NewOccurrence)
    (role : InternalRole)
    (labelEquality :
      extension.label (extension.embedNew newOccurrence) = .inl role) :
    False :=
  extension.toResidualUniquenessKernel
    |>.newOccurrence_cannotReuseInternalRole
      newOccurrence role labelEquality

theorem newOccurrence_label_is_residual
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (newOccurrence : NewOccurrence) :
    extension.label (extension.embedNew newOccurrence) =
      .inr residual.center :=
  extension.toResidualUniquenessKernel
    |>.newOccurrence_label_is_residual newOccurrence

theorem newOccurrences_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (first second : NewOccurrence) : first = second :=
  extension.toResidualUniquenessKernel
    |>.newOccurrences_unique first second

end FaithfulExtension

/- The weak kernel still produces the same proof-relevant residual output: an
   actual new occurrence, its exact residual label, and its uniqueness. -/
structure KernelUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual) where
  occurrence : NewOccurrence
  labelIsResidual :
    kernel.label (kernel.embedNew occurrence) = .inr residual.center
  unique : (other : NewOccurrence) → other = occurrence

/- Reattach a core result to the historical kernel interface.  The result is
   accepted only for the core generated by that kernel, so the conversion
   preserves the kernel's concrete label and occurrence types definitionally. -/
def CoreUniqueResidualOccurrence.toKernel
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    {kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual}
    (result : CoreUniqueResidualOccurrence
      kernel.toDeterminationCore) :
    KernelUniqueResidualOccurrence kernel :=
  { occurrence := result.occurrence
    labelIsResidual := result.labelIsResidual
    unique := result.unique }

def positiveKernel_hasUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (positive : PositiveNewPart NewOccurrence) :
    KernelUniqueResidualOccurrence kernel :=
  CoreUniqueResidualOccurrence.toKernel
    (positiveCore_hasUniqueResidualOccurrence
      kernel.toDeterminationCore positive)

/- Constructive internality retains both the role and its exact label.  A
   subtype is used so the role remains projectable data while its certificate
   remains proposition-valued. -/
def OldLabelsInternal
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual) :=
  (old : OldOccurrence) →
    { role : InternalRole //
      kernel.label (kernel.embedOld old) = .inl role }

/- A compatible completion fixes the kernel's forward map definitionally and
   asks only for its inverse and the two round trips. -/
structure ExactInternalCompletion
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual) where
  occurrenceToRole : OldOccurrence → InternalRole
  occurrenceRoundTrip :
    (occurrence : OldOccurrence) →
      kernel.roleToOccurrence (occurrenceToRole occurrence) = occurrence
  roleRoundTrip :
    (role : InternalRole) →
      occurrenceToRole (kernel.roleToOccurrence role) = role

structure ExactReconstructionConditions
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual) where
  oldLabelsInternal : OldLabelsInternal kernel
  embedOldInjective : Function.Injective kernel.embedOld

namespace ExactReconstructionConditions

def toExactInternalCompletion
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    {kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual}
    (conditions : ExactReconstructionConditions kernel) :
    ExactInternalCompletion kernel :=
  { occurrenceToRole := fun old => (conditions.oldLabelsInternal old).1
    occurrenceRoundTrip := by
      intro old
      let labelled := conditions.oldLabelsInternal old
      apply conditions.embedOldInjective
      apply kernel.labelFaithful
      exact (kernel.preservesInternal labelled.1).trans labelled.2.symm
    roleRoundTrip := by
      intro role
      let labelled := conditions.oldLabelsInternal
        (kernel.roleToOccurrence role)
      exact Sum.inl.inj
        (labelled.2.symm.trans (kernel.preservesInternal role)) }

end ExactReconstructionConditions

namespace ExactInternalCompletion

def toExactInternalRealization
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    {kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual}
    (completion : ExactInternalCompletion kernel) :
    ExactInternalRealization InternalRole OldOccurrence :=
  { roleToOccurrence := kernel.roleToOccurrence
    occurrenceToRole := completion.occurrenceToRole
    occurrenceRoundTrip := completion.occurrenceRoundTrip
    roleRoundTrip := completion.roleRoundTrip }

def toReconstructionConditions
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    {kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual}
    (completion : ExactInternalCompletion kernel) :
    ExactReconstructionConditions kernel :=
  { oldLabelsInternal := fun old =>
      { val := completion.occurrenceToRole old
        property :=
          (congrArg
            (fun occurrence => kernel.label (kernel.embedOld occurrence))
            (completion.occurrenceRoundTrip old).symm).trans
              (kernel.preservesInternal (completion.occurrenceToRole old)) }
    embedOldInjective := by
      intro first second imageEquality
      have firstLabel :
          kernel.label (kernel.embedOld first) =
            .inl (completion.occurrenceToRole first) :=
        (congrArg
          (fun occurrence => kernel.label (kernel.embedOld occurrence))
          (completion.occurrenceRoundTrip first).symm).trans
            (kernel.preservesInternal (completion.occurrenceToRole first))
      have secondLabel :
          kernel.label (kernel.embedOld second) =
            .inl (completion.occurrenceToRole second) :=
        (congrArg
          (fun occurrence => kernel.label (kernel.embedOld occurrence))
          (completion.occurrenceRoundTrip second).symm).trans
            (kernel.preservesInternal (completion.occurrenceToRole second))
      have roleEquality :
          completion.occurrenceToRole first =
            completion.occurrenceToRole second :=
        Sum.inl.inj
          (firstLabel.symm.trans
            ((congrArg kernel.label imageEquality).trans secondLabel))
      exact (completion.occurrenceRoundTrip first).symm.trans
        ((congrArg kernel.roleToOccurrence roleEquality).trans
          (completion.occurrenceRoundTrip second)) }

theorem occurrenceToRole_pointwise_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    {kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual}
    (first second : ExactInternalCompletion kernel)
    (old : OldOccurrence) :
    first.occurrenceToRole old = second.occurrenceToRole old :=
  (congrArg first.occurrenceToRole
      (second.occurrenceRoundTrip old).symm).trans
    (first.roleRoundTrip (second.occurrenceToRole old))

end ExactInternalCompletion

namespace ResidualUniquenessKernel

def oldLabelsInternal_of_positive
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (positive : PositiveNewPart NewOccurrence) :
    OldLabelsInternal kernel := fun old => by
  cases labelEquality : kernel.label (kernel.embedOld old) with
  | inl role => exact ⟨role, rfl⟩
  | inr role =>
      exact False.elim (by
        have oldLabelIsResidual :
            kernel.label (kernel.embedOld old) = .inr residual.center :=
          labelEquality.trans (congrArg Sum.inr (residual.contracts role))
        have sameLabel :
            kernel.label (kernel.embedOld old) =
              kernel.label (kernel.embedNew positive.occurrence) :=
          oldLabelIsResidual.trans
            (kernel.newOccurrence_label_is_residual
              positive.occurrence).symm
        exact kernel.oldNewDisjoint old positive.occurrence
          (kernel.labelFaithful
            (kernel.embedOld old)
            (kernel.embedNew positive.occurrence)
            sameLabel))

def toExactInternalCompletion_of_positive
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {residual : ContractibleRole ResidualRole}
    (kernel : ResidualUniquenessKernel
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence residual)
    (positive : PositiveNewPart NewOccurrence)
    (embedOldInjective : Function.Injective kernel.embedOld) :
    ExactInternalCompletion kernel :=
  ExactReconstructionConditions.toExactInternalCompletion
    { oldLabelsInternal := kernel.oldLabelsInternal_of_positive positive
      embedOldInjective := embedOldInjective }

end ResidualUniquenessKernel

namespace FaithfulExtension

def internalCompletion
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual) :
    ExactInternalCompletion extension.toResidualUniquenessKernel :=
  { occurrenceToRole := internal.occurrenceToRole
    occurrenceRoundTrip := internal.occurrenceRoundTrip
    roleRoundTrip := internal.roleRoundTrip }

theorem embedOld_injective
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual) :
    Function.Injective extension.embedOld :=
  extension.internalCompletion.toReconstructionConditions.embedOldInjective

def reconstructInternalCompletion
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence) :
    ExactInternalCompletion extension.toResidualUniquenessKernel :=
  extension.toResidualUniquenessKernel
    |>.toExactInternalCompletion_of_positive positive extension.embedOld_injective

theorem reconstructed_roleToOccurrence_eq
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence) :
    (extension.reconstructInternalCompletion positive
      |>.toExactInternalRealization).roleToOccurrence =
        internal.roleToOccurrence :=
  rfl

theorem reconstructed_roleToOccurrence_agrees
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence)
    (role : InternalRole) :
    (extension.reconstructInternalCompletion positive
      |>.toExactInternalRealization).roleToOccurrence role =
        internal.roleToOccurrence role :=
  rfl

theorem reconstructed_occurrenceToRole_agrees
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence)
    (old : OldOccurrence) :
    (extension.reconstructInternalCompletion positive).occurrenceToRole
        old = internal.occurrenceToRole old :=
  ExactInternalCompletion.occurrenceToRole_pointwise_unique
    (extension.reconstructInternalCompletion positive)
    extension.internalCompletion old

end FaithfulExtension

/- The constructive output packages existence, the exact residual label, and
   uniqueness. -/
structure UniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual) where
  occurrence : NewOccurrence
  labelIsResidual :
    extension.label (extension.embedNew occurrence) = .inr residual.center
  unique : (other : NewOccurrence) → other = occurrence

/- Reattach a core result to the public rich extension interface. -/
def CoreUniqueResidualOccurrence.toRich
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    {extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual}
    (result : CoreUniqueResidualOccurrence
      extension.toResidualUniquenessKernel.toDeterminationCore) :
    UniqueResidualOccurrence extension :=
  { occurrence := result.occurrence
    labelIsResidual := result.labelIsResidual
    unique := result.unique }

def positiveExtension_hasUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence) :
    UniqueResidualOccurrence extension :=
  CoreUniqueResidualOccurrence.toRich
    (positiveCore_hasUniqueResidualOccurrence
      extension.toResidualUniquenessKernel.toDeterminationCore positive)

theorem positiveExtension_result_occurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence) :
    (positiveExtension_hasUniqueResidualOccurrence extension positive).occurrence =
      positive.occurrence :=
  rfl

end RelationalFoundations.Residual

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.Residual.ExactInternalRealization
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel
#print axioms RelationalFoundations.Residual.ResidualDeterminationCore
#print axioms RelationalFoundations.Residual.ResidualDeterminationCore.label_is_residual
#print axioms RelationalFoundations.Residual.ResidualDeterminationCore.occurrences_unique
#print axioms RelationalFoundations.Residual.CoreUniqueResidualOccurrence
#print axioms RelationalFoundations.Residual.positiveCore_hasUniqueResidualOccurrence
#print axioms RelationalFoundations.Residual.CoreUniqueResidualOccurrence.toKernel
#print axioms RelationalFoundations.Residual.FaithfulExtension.toResidualUniquenessKernel
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.newOccurrence_cannotReuseInternalRole
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.toDeterminationCore
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.newOccurrence_label_is_residual
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.newOccurrences_unique
#print axioms RelationalFoundations.Residual.FaithfulExtension.newOccurrence_cannotReuseInternalRole
#print axioms RelationalFoundations.Residual.FaithfulExtension.newOccurrence_label_is_residual
#print axioms RelationalFoundations.Residual.FaithfulExtension.newOccurrences_unique
#print axioms RelationalFoundations.Residual.KernelUniqueResidualOccurrence
#print axioms RelationalFoundations.Residual.positiveKernel_hasUniqueResidualOccurrence
#print axioms RelationalFoundations.Residual.OldLabelsInternal
#print axioms RelationalFoundations.Residual.ExactInternalCompletion
#print axioms RelationalFoundations.Residual.ExactReconstructionConditions
#print axioms RelationalFoundations.Residual.ExactReconstructionConditions.toExactInternalCompletion
#print axioms RelationalFoundations.Residual.ExactInternalCompletion.toExactInternalRealization
#print axioms RelationalFoundations.Residual.ExactInternalCompletion.toReconstructionConditions
#print axioms RelationalFoundations.Residual.ExactInternalCompletion.occurrenceToRole_pointwise_unique
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.oldLabelsInternal_of_positive
#print axioms RelationalFoundations.Residual.ResidualUniquenessKernel.toExactInternalCompletion_of_positive
#print axioms RelationalFoundations.Residual.FaithfulExtension.internalCompletion
#print axioms RelationalFoundations.Residual.FaithfulExtension.embedOld_injective
#print axioms RelationalFoundations.Residual.FaithfulExtension.reconstructInternalCompletion
#print axioms RelationalFoundations.Residual.FaithfulExtension.reconstructed_roleToOccurrence_eq
#print axioms RelationalFoundations.Residual.FaithfulExtension.reconstructed_roleToOccurrence_agrees
#print axioms RelationalFoundations.Residual.FaithfulExtension.reconstructed_occurrenceToRole_agrees
#print axioms RelationalFoundations.Residual.positiveExtension_hasUniqueResidualOccurrence
#print axioms RelationalFoundations.Residual.CoreUniqueResidualOccurrence.toRich
#print axioms RelationalFoundations.Residual.positiveExtension_result_occurrence
/- AXIOM_AUDIT_END -/
