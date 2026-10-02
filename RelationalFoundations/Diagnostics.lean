import RelationalFoundations.Residual
set_option genInjectivity false

/-!
# Abstract turning of a segmented totality

This module isolates a second dependency boundary from
`StrongPerimetralTurning`.  It contains no circular presentation, endpoint
difference, provenance, loop, or final junction.

The abstract mechanism has three independent inputs:

* an exact segmented boundary with a contractible residual role;
* a generator producing a strict continuation of the canonical boundary;
* a regime analysis saying that every admitted candidate is either the
  canonical boundary or carries a forbidden totalization attempt.

The output combines the unique residual occurrence, exact relative
classification of the segmented regime, strict continuation outside that
regime, and rejection of every totalization attempt.
-/

namespace RelationalFoundations.Diagnostics

universe
  uCarrier uExtension uInternal uResidual uOld uNew uCombined
  uRegime uInterpretation uAttempt uContext
  uFaithful' uFaithful'' uRegime' uRegime''
  uImplementation uImplementation' uImplementation''

/- A boundary generator is deliberately independent of histories.  Its
   extension relation is required to be irreflexive, so the generated
   continuation is constructively distinct from the completed boundary. -/
structure BoundaryGenerator
    (Carrier : Type uCarrier)
    (Extension : Carrier → Carrier → Type uExtension) where
  boundary : Carrier
  continuation : Carrier
  generates : Extension boundary continuation
  extensionIrreflexive :
    (carrier : Carrier) → Extension carrier carrier → False

namespace BoundaryGenerator

theorem continuation_ne_boundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension) :
    generator.continuation ≠ generator.boundary := by
  intro equality
  exact generator.extensionIrreflexive
    generator.boundary
    (cast
      (congrArg (Extension generator.boundary) equality)
      generator.generates)

end BoundaryGenerator

/- Exact classification is constructive: both directions are retained as
   transformations rather than collapsed into a bare logical equivalence. -/
structure ExactRegimeClassification
    {Carrier : Type uCarrier}
    (canonical : Carrier)
    (Regime : Carrier → Type uRegime) where
  regimeImpliesEquality :
    {candidate : Carrier} → Regime candidate → candidate = canonical
  equalityBuildsRegime :
    {candidate : Carrier} → candidate = canonical → Regime candidate

/- A regime exit is a typed diagnostic: the same candidate carries a positive
   witness of the selected faithful structure while its regime type is
   refuted. No particular notion of history, circularity, or boundary is
   assumed here. -/
structure RegimeExit
    {Carrier : Type uCarrier}
    (Faithful : Carrier → Type uInterpretation)
    (Regime : Carrier → Type uRegime) where
  candidate : Carrier
  faithful : Faithful candidate
  inadmissible : Regime candidate → False

namespace RegimeExit

/- Covariant transport of the positive witness family. -/
def mapFaithful
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Faithful' : Carrier → Type uFaithful'}
    {Regime : Carrier → Type uRegime}
    (exit : RegimeExit Faithful Regime)
    (map : (candidate : Carrier) → Faithful candidate → Faithful' candidate) :
    RegimeExit Faithful' Regime :=
  { candidate := exit.candidate
    faithful := map exit.candidate exit.faithful
    inadmissible := exit.inadmissible }

/- Contravariant transport of the refuted regime family. -/
def restrictRegime
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    {Regime' : Carrier → Type uRegime'}
    (exit : RegimeExit Faithful Regime)
    (restrict : (candidate : Carrier) → Regime' candidate → Regime candidate) :
    RegimeExit Faithful Regime' :=
  { candidate := exit.candidate
    faithful := exit.faithful
    inadmissible := fun regime' =>
      exit.inadmissible (restrict exit.candidate regime') }

/- A local regime exit refutes every proposed global lift from the faithful
   family to the regime family, at the candidate carried by the exit. -/
theorem refutesFaithfulToRegime
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : RegimeExit Faithful Regime)
    (lift : (candidate : Carrier) → Faithful candidate → Regime candidate) :
    False :=
  exit.inadmissible (lift exit.candidate exit.faithful)

@[simp] theorem mapFaithful_id
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : RegimeExit Faithful Regime) :
    exit.mapFaithful (fun _ faithful => faithful) = exit := by
  rfl

@[simp] theorem mapFaithful_comp
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Faithful' : Carrier → Type uFaithful'}
    {Faithful'' : Carrier → Type uFaithful''}
    {Regime : Carrier → Type uRegime}
    (exit : RegimeExit Faithful Regime)
    (first : (candidate : Carrier) → Faithful candidate → Faithful' candidate)
    (second : (candidate : Carrier) → Faithful' candidate → Faithful'' candidate) :
    (exit.mapFaithful first).mapFaithful second =
      exit.mapFaithful (fun candidate faithful =>
        second candidate (first candidate faithful)) := by
  rfl

@[simp] theorem restrictRegime_id
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : RegimeExit Faithful Regime) :
    exit.restrictRegime (fun _ regime => regime) = exit := by
  rfl

@[simp] theorem restrictRegime_comp
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    {Regime' : Carrier → Type uRegime'}
    {Regime'' : Carrier → Type uRegime''}
    (exit : RegimeExit Faithful Regime)
    (first : (candidate : Carrier) → Regime' candidate → Regime candidate)
    (second : (candidate : Carrier) → Regime'' candidate → Regime' candidate) :
    (exit.restrictRegime first).restrictRegime second =
      exit.restrictRegime (fun candidate regime =>
        first candidate (second candidate regime)) := by
  rfl

@[simp] theorem mapFaithful_restrictRegime
    {Carrier : Type uCarrier}
    {Faithful : Carrier → Type uInterpretation}
    {Faithful' : Carrier → Type uFaithful'}
    {Regime : Carrier → Type uRegime}
    {Regime' : Carrier → Type uRegime'}
    (exit : RegimeExit Faithful Regime)
    (map : (candidate : Carrier) → Faithful candidate → Faithful' candidate)
    (restrict : (candidate : Carrier) → Regime' candidate → Regime candidate) :
    (exit.mapFaithful map).restrictRegime restrict =
      (exit.restrictRegime restrict).mapFaithful map := by
  rfl

end RegimeExit

/- Uniform regime exit does not introduce a second diagnostic structure.  It
   specializes the positive family of `RegimeExit` to a dependent product over
   implementations, thereby fixing the candidate before implementation
   variation. -/
abbrev UniformRegimeExit
    {Carrier : Type uCarrier}
    (Implementation : Type uImplementation)
    (Faithful : Implementation → Carrier → Type uInterpretation)
    (Regime : Carrier → Type uRegime) :
    Type (max (max uImplementation uInterpretation) uCarrier) :=
  RegimeExit
    (fun candidate =>
      (implementation : Implementation) → Faithful implementation candidate)
    Regime

namespace UniformRegimeExit

/- Evaluate the universal positive fibre at one supplied implementation. -/
def atImplementation
    {Carrier : Type uCarrier}
    {Implementation : Type uImplementation}
    {Faithful : Implementation → Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : UniformRegimeExit Implementation Faithful Regime)
    (implementation : Implementation) :
    RegimeExit (Faithful implementation) Regime :=
  { candidate := exit.candidate
    faithful := exit.faithful implementation
    inadmissible := exit.inadmissible }

/- Reindex implementation parameters by precomposition. -/
def reindexImplementation
    {Carrier : Type uCarrier}
    {Implementation : Type uImplementation}
    {Implementation' : Type uImplementation'}
    {Faithful : Implementation → Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : UniformRegimeExit Implementation Faithful Regime)
    (reindex : Implementation' → Implementation) :
    UniformRegimeExit
      Implementation'
      (fun implementation' candidate =>
        Faithful (reindex implementation') candidate)
      Regime :=
  { candidate := exit.candidate
    faithful := fun implementation' => exit.faithful (reindex implementation')
    inadmissible := exit.inadmissible }

@[simp] theorem reindex_id
    {Carrier : Type uCarrier}
    {Implementation : Type uImplementation}
    {Faithful : Implementation → Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : UniformRegimeExit Implementation Faithful Regime) :
    reindexImplementation exit id = exit := by
  rfl

@[simp] theorem reindex_comp
    {Carrier : Type uCarrier}
    {Implementation : Type uImplementation}
    {Implementation' : Type uImplementation'}
    {Implementation'' : Type uImplementation''}
    {Faithful : Implementation → Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : UniformRegimeExit Implementation Faithful Regime)
    (first : Implementation' → Implementation)
    (second : Implementation'' → Implementation') :
    reindexImplementation (reindexImplementation exit first) second =
      reindexImplementation exit (first ∘ second) := by
  rfl

@[simp] theorem reindex_at
    {Carrier : Type uCarrier}
    {Implementation : Type uImplementation}
    {Implementation' : Type uImplementation'}
    {Faithful : Implementation → Carrier → Type uInterpretation}
    {Regime : Carrier → Type uRegime}
    (exit : UniformRegimeExit Implementation Faithful Regime)
    (reindex : Implementation' → Implementation)
    (implementation : Implementation') :
    atImplementation (reindexImplementation exit reindex) implementation =
      atImplementation exit (reindex implementation) := by
  rfl

end UniformRegimeExit

/- The weak occurrence layer carries only the residual-determination data
   consumed by the core turning theorem. -/
structure CoreSegmentedBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (_generator : BoundaryGenerator Carrier Extension)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (NewOccurrence : Type uNew)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole) where
  core :
    RelationalFoundations.Residual.ResidualDeterminationCore
      InternalRole ResidualRole NewOccurrence residual
  positive : RelationalFoundations.Residual.PositiveNewPart NewOccurrence

/- The rich occurrence layer remains available as the compatibility boundary
   for existing consumers. -/
structure SegmentedBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (_generator : BoundaryGenerator Carrier Extension)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (NewOccurrence : Type uNew)
    (CombinedOccurrence : Type uCombined)
    (internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole) where
  extension : RelationalFoundations.Residual.FaithfulExtension
    InternalRole ResidualRole OldOccurrence NewOccurrence CombinedOccurrence
    internal residual
  positive : RelationalFoundations.Residual.PositiveNewPart NewOccurrence

/- The boundary's residual core is obtained through the explicit adapter
   chain, while the rich boundary remains available to its consumers. -/
def SegmentedBoundary.toCoreBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {CombinedOccurrence : Type uCombined}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (segmented : SegmentedBoundary generator
      InternalRole ResidualRole OldOccurrence NewOccurrence CombinedOccurrence
      internal residual) :
    CoreSegmentedBoundary
      generator InternalRole ResidualRole NewOccurrence residual :=
  { core :=
      segmented.extension
        |>.toResidualUniquenessKernel
        |>.toDeterminationCore
    positive := segmented.positive }

/- A regime is analyzed without assuming its maximality.  An admitted
   candidate yields either equality with the canonical boundary or an actual
   totalization attempt at an interpretation of that candidate.  The
   obstruction rejects the second branch. -/
set_option linter.checkUnivs false in
structure ObstructedRegime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension) where
  Regime : Carrier → Type uRegime
  Interpretation : Carrier → Type uInterpretation
  Attempt :
    {candidate : Carrier} → Interpretation candidate → Type uAttempt
  canonicalRegime : Regime generator.boundary
  classifyOrTotalize :
    {candidate : Carrier} →
      Regime candidate →
        PLift (candidate = generator.boundary) ⊕
          (Σ interpretation : Interpretation candidate,
            Attempt interpretation)
  rejectTotalization :
    {candidate : Carrier} →
    (interpretation : Interpretation candidate) →
      Attempt interpretation → False

namespace ObstructedRegime

def exactClassification
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    (obstructed : ObstructedRegime generator) :
    ExactRegimeClassification generator.boundary obstructed.Regime :=
  { regimeImpliesEquality := by
      intro candidate regime
      cases obstructed.classifyOrTotalize regime with
      | inl equality => exact equality.down
      | inr totalized =>
          exact False.elim
            (obstructed.rejectTotalization totalized.1 totalized.2)
    equalityBuildsRegime := by
      intro candidate equality
      cases equality
      exact obstructed.canonicalRegime }

theorem continuation_outside_regime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    (obstructed : ObstructedRegime generator) :
    obstructed.Regime generator.continuation → False := by
  intro regime
  exact generator.continuation_ne_boundary
    (obstructed.exactClassification.regimeImpliesEquality regime)

theorem no_strict_regime_extension
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    (obstructed : ObstructedRegime generator) :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × obstructed.Regime candidate) →
      False := by
  rintro ⟨candidate, extension, regime⟩
  have equality :=
    obstructed.exactClassification.regimeImpliesEquality regime
  cases equality
  exact generator.extensionIrreflexive generator.boundary extension

end ObstructedRegime

/- The complete turning conclusion at the factorized core boundary level. -/
structure CoreTurningConclusion
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (segmented : CoreSegmentedBoundary generator
      InternalRole ResidualRole NewOccurrence residual)
    (obstructed : ObstructedRegime generator) where
  uniqueResidualOccurrence :
    RelationalFoundations.Residual.CoreUniqueResidualOccurrence segmented.core
  exactRelativeClassification :
    ExactRegimeClassification generator.boundary obstructed.Regime
  generatedContinuation :
    Extension generator.boundary generator.continuation
  continuationIsStrict : generator.continuation ≠ generator.boundary
  continuationOutsideRegime :
    obstructed.Regime generator.continuation → False
  noStrictRegimeExtension :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × obstructed.Regime candidate) →
      False
  totalizationRejected :
    {candidate : Carrier} →
    (interpretation : obstructed.Interpretation candidate) →
      obstructed.Attempt interpretation → False

/- This is the fundamental theorem: it consumes only the core boundary and
   the obstructed regime, with no rich realization data in its signature. -/
def coreTurning
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {NewOccurrence : Type uNew}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (segmented : CoreSegmentedBoundary generator
      InternalRole ResidualRole NewOccurrence residual)
    (obstructed : ObstructedRegime generator) :
    CoreTurningConclusion segmented obstructed :=
  { uniqueResidualOccurrence :=
      RelationalFoundations.Residual.positiveCore_hasUniqueResidualOccurrence
        segmented.core segmented.positive
    exactRelativeClassification := obstructed.exactClassification
    generatedContinuation := generator.generates
    continuationIsStrict := generator.continuation_ne_boundary
    continuationOutsideRegime := obstructed.continuation_outside_regime
    noStrictRegimeExtension := obstructed.no_strict_regime_extension
    totalizationRejected := obstructed.rejectTotalization }

/- The conclusion keeps all four outputs as explicit constructive data. -/
structure TurningConclusion
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {CombinedOccurrence : Type uCombined}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (segmented : SegmentedBoundary generator
      InternalRole ResidualRole OldOccurrence NewOccurrence CombinedOccurrence
      internal residual)
    (obstructed : ObstructedRegime generator) where
  uniqueResidualOccurrence :
    RelationalFoundations.Residual.UniqueResidualOccurrence segmented.extension
  exactRelativeClassification :
    ExactRegimeClassification generator.boundary obstructed.Regime
  generatedContinuation :
    Extension generator.boundary generator.continuation
  continuationIsStrict : generator.continuation ≠ generator.boundary
  continuationOutsideRegime :
    obstructed.Regime generator.continuation → False
  noStrictRegimeExtension :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × obstructed.Regime candidate) →
      False
  totalizationRejected :
    {candidate : Carrier} →
    (interpretation : obstructed.Interpretation candidate) →
      obstructed.Attempt interpretation → False

def abstractTurning
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {CombinedOccurrence : Type uCombined}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (segmented : SegmentedBoundary generator
      InternalRole ResidualRole OldOccurrence NewOccurrence CombinedOccurrence
      internal residual)
    (obstructed : ObstructedRegime generator) :
    TurningConclusion segmented obstructed := by
  let coreResult := coreTurning segmented.toCoreBoundary obstructed
  exact
    { uniqueResidualOccurrence := coreResult.uniqueResidualOccurrence.toRich
      exactRelativeClassification := coreResult.exactRelativeClassification
      generatedContinuation := coreResult.generatedContinuation
      continuationIsStrict := coreResult.continuationIsStrict
      continuationOutsideRegime := coreResult.continuationOutsideRegime
      noStrictRegimeExtension := coreResult.noStrictRegimeExtension
      totalizationRejected := coreResult.totalizationRejected }

/-! ## Residual-to-turning coupling

`TurningConclusion` above deliberately preserves the first factorization: a
segmented residual theorem and an obstructed-regime theorem are packaged
together.  The following stronger interface records the missing dependency.

A positive noncanonical boundary now carries its own segmented extension and
strict extension witness.  Its interpretation must be built from the unique
residual occurrence produced by that extension, and an admitted positive
boundary must build its attempted totalization from the same residual data.
-/

/- The weak positive boundary used by the coupled core.  It retains only the
   candidate context, strict extension, residual core, and positive witness. -/
structure CorePositiveResidualBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension)
    (Context : Carrier → Type uContext)
    (NewOccurrence : {candidate : Carrier} → Context candidate → Type uNew)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole)
    (candidate : Carrier) where
  context : Context candidate
  strict : Extension generator.boundary candidate
  core :
    RelationalFoundations.Residual.ResidualDeterminationCore
      InternalRole ResidualRole (NewOccurrence context) residual
  positive : RelationalFoundations.Residual.PositiveNewPart (NewOccurrence context)

namespace CorePositiveResidualBoundary

def uniqueResidualOccurrence
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    {candidate : Carrier}
    (boundary : CorePositiveResidualBoundary generator Context
      NewOccurrence InternalRole ResidualRole residual candidate) :
    RelationalFoundations.Residual.CoreUniqueResidualOccurrence boundary.core :=
  RelationalFoundations.Residual.positiveCore_hasUniqueResidualOccurrence
    boundary.core boundary.positive

end CorePositiveResidualBoundary

structure PositiveResidualBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension)
    (Context : Carrier → Type uContext)
    (NewOccurrence : {candidate : Carrier} → Context candidate → Type uNew)
    (CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole)
    (candidate : Carrier) where
  context : Context candidate
  strict : Extension generator.boundary candidate
  extension : RelationalFoundations.Residual.FaithfulExtension
    InternalRole ResidualRole OldOccurrence
    (NewOccurrence context) (CombinedOccurrence context) internal residual
  positive : RelationalFoundations.Residual.PositiveNewPart (NewOccurrence context)

def PositiveResidualBoundary.toCoreBoundary
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    {candidate : Carrier}
    (boundary : PositiveResidualBoundary generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual candidate) :
    CorePositiveResidualBoundary generator Context
      NewOccurrence InternalRole ResidualRole residual candidate :=
  { context := boundary.context
    strict := boundary.strict
    core :=
      boundary.extension
        |>.toResidualUniquenessKernel
        |>.toDeterminationCore
    positive := boundary.positive }

namespace PositiveResidualBoundary

def uniqueResidualOccurrence
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    {candidate : Carrier}
    (boundary : PositiveResidualBoundary generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual candidate) :
    RelationalFoundations.Residual.UniqueResidualOccurrence boundary.extension :=
  RelationalFoundations.Residual.CoreUniqueResidualOccurrence.toRich
    (CorePositiveResidualBoundary.uniqueResidualOccurrence
      boundary.toCoreBoundary)

end PositiveResidualBoundary

set_option linter.checkUnivs false in
structure CoreCoupledObstructedRegime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension)
    (Context : Carrier → Type uContext)
    (NewOccurrence : {candidate : Carrier} → Context candidate → Type uNew)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole) where
  Regime : Carrier → Type uRegime
  Interpretation : Carrier → Type uInterpretation
  Attempt :
    {candidate : Carrier} → Interpretation candidate → Type uAttempt
  canonicalRegime : Regime generator.boundary
  interpretResidual :
    {candidate : Carrier} →
    (boundary : CorePositiveResidualBoundary generator Context
      NewOccurrence InternalRole ResidualRole residual candidate) →
    (unique : RelationalFoundations.Residual.CoreUniqueResidualOccurrence
      boundary.core) →
      Interpretation candidate
  analyzeRegime :
    {candidate : Carrier} →
    (regime : Regime candidate) →
      PLift (candidate = generator.boundary) ⊕
        (Σ boundary : CorePositiveResidualBoundary generator Context
          NewOccurrence InternalRole ResidualRole residual candidate,
          Attempt
            (interpretResidual boundary
              boundary.uniqueResidualOccurrence))
  rejectTotalization :
    {candidate : Carrier} →
    (interpretation : Interpretation candidate) →
      Attempt interpretation → False

namespace CoreCoupledObstructedRegime

def exactClassification
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) :
    ExactRegimeClassification generator.boundary coupled.Regime :=
  { regimeImpliesEquality := by
      intro candidate regime
      cases coupled.analyzeRegime regime with
      | inl equality => exact equality.down
      | inr residualBranch =>
          rcases residualBranch with ⟨boundary, attempt⟩
          let interpretation := coupled.interpretResidual boundary
            boundary.uniqueResidualOccurrence
          exact False.elim
            (coupled.rejectTotalization interpretation attempt)
    equalityBuildsRegime := by
      intro candidate equality
      cases equality
      exact coupled.canonicalRegime }

def toObstructedRegime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) :
    ObstructedRegime generator :=
  { Regime := coupled.Regime
    Interpretation := coupled.Interpretation
    Attempt := coupled.Attempt
    canonicalRegime := coupled.canonicalRegime
    classifyOrTotalize := by
      intro candidate regime
      cases coupled.analyzeRegime regime with
      | inl equality => exact .inl equality
      | inr residualBranch =>
          rcases residualBranch with ⟨boundary, attempt⟩
          let interpretation := coupled.interpretResidual boundary
            boundary.uniqueResidualOccurrence
          exact .inr ⟨interpretation, attempt⟩
    rejectTotalization := coupled.rejectTotalization }

theorem admittedPositiveBoundary_rejected
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual)
    {candidate : Carrier}
    (boundary : CorePositiveResidualBoundary generator Context
      NewOccurrence InternalRole ResidualRole residual candidate)
    (attempt : coupled.Attempt
      (coupled.interpretResidual boundary
        boundary.uniqueResidualOccurrence)) :
    False :=
  coupled.rejectTotalization
    (coupled.interpretResidual boundary boundary.uniqueResidualOccurrence)
    attempt

theorem continuation_outside_regime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) :
    coupled.Regime generator.continuation → False := by
  intro regime
  exact generator.continuation_ne_boundary
    (coupled.exactClassification.regimeImpliesEquality regime)

theorem no_strict_regime_extension
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × coupled.Regime candidate) →
      False := by
  rintro ⟨candidate, extension, regime⟩
  have equality := coupled.exactClassification.regimeImpliesEquality regime
  cases equality
  exact generator.extensionIrreflexive generator.boundary extension

end CoreCoupledObstructedRegime

structure CoreCoupledTurningConclusion
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) where
  exactRelativeClassification :
    ExactRegimeClassification generator.boundary coupled.Regime
  generatedContinuation :
    Extension generator.boundary generator.continuation
  continuationIsStrict : generator.continuation ≠ generator.boundary
  continuationOutsideRegime :
    coupled.Regime generator.continuation → False
  admittedPositiveBoundaryRejected :
    {candidate : Carrier} →
    (boundary : CorePositiveResidualBoundary generator Context
      NewOccurrence InternalRole ResidualRole residual candidate) →
    coupled.Attempt
      (coupled.interpretResidual boundary
        boundary.uniqueResidualOccurrence) →
      False
  noStrictRegimeExtension :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × coupled.Regime candidate) →
      False

def coreCoupledTurning
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual) :
    CoreCoupledTurningConclusion coupled :=
  { exactRelativeClassification := coupled.exactClassification
    generatedContinuation := generator.generates
    continuationIsStrict := generator.continuation_ne_boundary
    continuationOutsideRegime := coupled.continuation_outside_regime
    admittedPositiveBoundaryRejected :=
      coupled.admittedPositiveBoundary_rejected
    noStrictRegimeExtension := coupled.no_strict_regime_extension }

set_option linter.checkUnivs false in
structure CoupledObstructedRegime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    (generator : BoundaryGenerator Carrier Extension)
    (Context : Carrier → Type uContext)
    (NewOccurrence : {candidate : Carrier} → Context candidate → Type uNew)
    (CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined)
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence)
    (residual : RelationalFoundations.Residual.ContractibleRole ResidualRole) where
  Regime : Carrier → Type uRegime
  Interpretation : Carrier → Type uInterpretation
  Attempt :
    {candidate : Carrier} → Interpretation candidate → Type uAttempt
  canonicalRegime : Regime generator.boundary
  interpretResidual :
    {candidate : Carrier} →
    (boundary : PositiveResidualBoundary generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual candidate) →
    (unique : RelationalFoundations.Residual.UniqueResidualOccurrence
      boundary.extension) →
      Interpretation candidate
  analyzeRegime :
    {candidate : Carrier} →
    (regime : Regime candidate) →
      PLift (candidate = generator.boundary) ⊕
        (Σ boundary : PositiveResidualBoundary generator Context
          NewOccurrence CombinedOccurrence
          InternalRole ResidualRole OldOccurrence internal residual candidate,
          Attempt
            (interpretResidual boundary
              boundary.uniqueResidualOccurrence))
  rejectTotalization :
    {candidate : Carrier} →
    (interpretation : Interpretation candidate) →
      Attempt interpretation → False

namespace CoupledObstructedRegime

def exactClassification
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    ExactRegimeClassification generator.boundary coupled.Regime :=
  { regimeImpliesEquality := by
      intro candidate regime
      cases coupled.analyzeRegime regime with
      | inl equality => exact equality.down
      | inr residualBranch =>
          rcases residualBranch with ⟨boundary, attempt⟩
          let interpretation := coupled.interpretResidual boundary
            boundary.uniqueResidualOccurrence
          exact False.elim
            (coupled.rejectTotalization interpretation attempt)
    equalityBuildsRegime := by
      intro candidate equality
      cases equality
      exact coupled.canonicalRegime }

def toObstructedRegime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    ObstructedRegime generator :=
  { Regime := coupled.Regime
    Interpretation := coupled.Interpretation
    Attempt := coupled.Attempt
    canonicalRegime := coupled.canonicalRegime
    classifyOrTotalize := by
      intro candidate regime
      cases coupled.analyzeRegime regime with
      | inl equality => exact .inl equality
      | inr residualBranch =>
          rcases residualBranch with ⟨boundary, attempt⟩
          let interpretation := coupled.interpretResidual boundary
            boundary.uniqueResidualOccurrence
          exact .inr
            ⟨interpretation, attempt⟩
    rejectTotalization := coupled.rejectTotalization }

theorem admittedPositiveBoundary_rejected
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual)
    {candidate : Carrier}
    (boundary : PositiveResidualBoundary generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual candidate)
    (attempt : coupled.Attempt
      (coupled.interpretResidual boundary
        boundary.uniqueResidualOccurrence)) :
    False :=
  coupled.rejectTotalization
    (coupled.interpretResidual boundary boundary.uniqueResidualOccurrence)
    attempt

theorem continuation_outside_regime
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    coupled.Regime generator.continuation → False := by
  intro regime
  exact generator.continuation_ne_boundary
    (coupled.exactClassification.regimeImpliesEquality regime)

theorem no_strict_regime_extension
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × coupled.Regime candidate) →
      False := by
  rintro ⟨candidate, extension, regime⟩
  have equality := coupled.exactClassification.regimeImpliesEquality regime
  cases equality
  exact generator.extensionIrreflexive generator.boundary extension

end CoupledObstructedRegime

/- The historical coupled regime can be viewed through the core interface
   without pretending that a core boundary reconstructs a rich boundary.
   The compatibility attempt explicitly carries the rich boundary needed by
   the historical interpretation. -/
def CoupledObstructedRegime.toCoreCoupled
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    CoreCoupledObstructedRegime generator Context
      NewOccurrence InternalRole ResidualRole residual :=
  { Regime := coupled.Regime
    Interpretation := fun _ => Unit
    Attempt := fun {candidate} _ =>
      Σ boundary : PositiveResidualBoundary generator Context
        NewOccurrence CombinedOccurrence
        InternalRole ResidualRole OldOccurrence internal residual candidate,
        coupled.Attempt
          (coupled.interpretResidual boundary
            boundary.uniqueResidualOccurrence)
    canonicalRegime := coupled.canonicalRegime
    interpretResidual := fun {_} _ _ => ()
    analyzeRegime := by
      intro candidate regime
      cases coupled.analyzeRegime regime with
      | inl equality => exact .inl equality
      | inr residualBranch =>
          rcases residualBranch with ⟨boundary, attempt⟩
          exact .inr ⟨boundary.toCoreBoundary, ⟨boundary, attempt⟩⟩
    rejectTotalization := by
      intro candidate interpretation attempt
      rcases attempt with ⟨boundary, richAttempt⟩
      exact coupled.rejectTotalization
        (coupled.interpretResidual boundary
          boundary.uniqueResidualOccurrence)
        richAttempt }

structure CoupledTurningConclusion
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) where
  exactRelativeClassification :
    ExactRegimeClassification generator.boundary coupled.Regime
  generatedContinuation :
    Extension generator.boundary generator.continuation
  continuationIsStrict : generator.continuation ≠ generator.boundary
  continuationOutsideRegime :
    coupled.Regime generator.continuation → False
  admittedPositiveBoundaryRejected :
    {candidate : Carrier} →
    (boundary : PositiveResidualBoundary generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual candidate) →
    coupled.Attempt
      (coupled.interpretResidual boundary
        boundary.uniqueResidualOccurrence) →
      False
  noStrictRegimeExtension :
    (Σ candidate : Carrier,
      Extension generator.boundary candidate × coupled.Regime candidate) →
      False

def coupledTurning
    {Carrier : Type uCarrier}
    {Extension : Carrier → Carrier → Type uExtension}
    {generator : BoundaryGenerator Carrier Extension}
    {Context : Carrier → Type uContext}
    {NewOccurrence :
      {candidate : Carrier} → Context candidate → Type uNew}
    {CombinedOccurrence :
      {candidate : Carrier} → Context candidate → Type uCombined}
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {internal : RelationalFoundations.Residual.ExactInternalRealization
      InternalRole OldOccurrence}
    {residual : RelationalFoundations.Residual.ContractibleRole ResidualRole}
    (coupled : CoupledObstructedRegime generator Context
      NewOccurrence CombinedOccurrence
      InternalRole ResidualRole OldOccurrence internal residual) :
    CoupledTurningConclusion coupled := by
  let coreCoupled := CoupledObstructedRegime.toCoreCoupled coupled
  let coreResult := coreCoupledTurning coreCoupled
  exact
    { exactRelativeClassification := coreResult.exactRelativeClassification
      generatedContinuation := coreResult.generatedContinuation
      continuationIsStrict := coreResult.continuationIsStrict
      continuationOutsideRegime := coreResult.continuationOutsideRegime
      admittedPositiveBoundaryRejected := by
        intro candidate boundary attempt
        let coreBoundary := boundary.toCoreBoundary
        let coreAttempt :
            coreCoupled.Attempt
              (coreCoupled.interpretResidual coreBoundary
                coreBoundary.uniqueResidualOccurrence) :=
          ⟨boundary, attempt⟩
        exact coreResult.admittedPositiveBoundaryRejected
          coreBoundary coreAttempt
      noStrictRegimeExtension := coreResult.noStrictRegimeExtension }

end RelationalFoundations.Diagnostics

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.Diagnostics.BoundaryGenerator.continuation_ne_boundary
#print axioms RelationalFoundations.Diagnostics.ObstructedRegime.exactClassification
#print axioms RelationalFoundations.Diagnostics.ObstructedRegime.continuation_outside_regime
#print axioms RelationalFoundations.Diagnostics.ObstructedRegime.no_strict_regime_extension
#print axioms RelationalFoundations.Diagnostics.CoreSegmentedBoundary
#print axioms RelationalFoundations.Diagnostics.SegmentedBoundary.toCoreBoundary
#print axioms RelationalFoundations.Diagnostics.CoreTurningConclusion
#print axioms RelationalFoundations.Diagnostics.coreTurning
#print axioms RelationalFoundations.Diagnostics.CorePositiveResidualBoundary
#print axioms RelationalFoundations.Diagnostics.CorePositiveResidualBoundary.uniqueResidualOccurrence
#print axioms RelationalFoundations.Diagnostics.PositiveResidualBoundary.toCoreBoundary
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime.exactClassification
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime.toObstructedRegime
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime.admittedPositiveBoundary_rejected
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime.continuation_outside_regime
#print axioms RelationalFoundations.Diagnostics.CoreCoupledObstructedRegime.no_strict_regime_extension
#print axioms RelationalFoundations.Diagnostics.CoreCoupledTurningConclusion
#print axioms RelationalFoundations.Diagnostics.coreCoupledTurning
#print axioms RelationalFoundations.Diagnostics.CoupledObstructedRegime.toCoreCoupled
#print axioms RelationalFoundations.Diagnostics.abstractTurning
#print axioms RelationalFoundations.Diagnostics.PositiveResidualBoundary.uniqueResidualOccurrence
#print axioms RelationalFoundations.Diagnostics.CoupledObstructedRegime.exactClassification
#print axioms RelationalFoundations.Diagnostics.CoupledObstructedRegime.toObstructedRegime
#print axioms RelationalFoundations.Diagnostics.CoupledObstructedRegime.admittedPositiveBoundary_rejected
#print axioms RelationalFoundations.Diagnostics.coupledTurning
#print axioms RelationalFoundations.Diagnostics.RegimeExit
#print axioms RelationalFoundations.Diagnostics.RegimeExit.mapFaithful
#print axioms RelationalFoundations.Diagnostics.RegimeExit.restrictRegime
#print axioms RelationalFoundations.Diagnostics.RegimeExit.refutesFaithfulToRegime
#print axioms RelationalFoundations.Diagnostics.RegimeExit.mapFaithful_id
#print axioms RelationalFoundations.Diagnostics.RegimeExit.mapFaithful_comp
#print axioms RelationalFoundations.Diagnostics.RegimeExit.restrictRegime_id
#print axioms RelationalFoundations.Diagnostics.RegimeExit.restrictRegime_comp
#print axioms RelationalFoundations.Diagnostics.RegimeExit.mapFaithful_restrictRegime
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit.atImplementation
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit.reindexImplementation
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit.reindex_id
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit.reindex_comp
#print axioms RelationalFoundations.Diagnostics.UniformRegimeExit.reindex_at
/- AXIOM_AUDIT_END -/
