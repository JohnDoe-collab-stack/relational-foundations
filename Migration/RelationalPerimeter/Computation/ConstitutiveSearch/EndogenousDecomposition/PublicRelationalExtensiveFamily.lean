import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalRoleExtensiveFamily

/-!
# Exact public instance of the general relational extensive family

This module reads the public causal history and its relational role history.
The general family, the executed instance and the width theorem all use the
same realized occurrence profiles and the same derived frontier.  No second
carrier and no reindexing layer intervene between constitution and readout.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive
open RelationalExtensive

theorem generalHistory_is_uniformBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      UniformLocalArity (generalHistoryOfRoleHistory roles) 2 :=
  fun roles => generalRoleHistory_uniformBinary roles

theorem generalHistory_is_atLeastBinary :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      AtLeastBinaryLocalArity (generalHistoryOfRoleHistory roles)
  | _, _, _, .nil => True.intro
  | _, _, _, .step _ tailRoles => by
      exact ⟨Nat.le_refl 2, generalHistory_is_atLeastBinary tailRoles⟩

/-- The generic width readout agrees with the concrete binary exponent. -/
theorem generalHistory_width_eq_twoPow
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    relationalProfileWidth (generalHistoryOfRoleHistory roles) = 2 ^ count :=
  uniformLocalArity_width
    (generalHistoryOfRoleHistory roles) 2
    (generalRoleHistory_uniformBinary roles)

/-- The public initial state of the already executed causal history. -/
def publicCausalInitialState (input : Nat) : CausalConstitutiveState :=
  causalStateOfThreadedState
    (executeConstitutiveResolution input).threadedInitialState

/-- The exact general history read from the public execution. -/
def publicGeneralRelationalHistory (input : Nat) :
    DependentRelationalRoleHistory CausalConstitutiveState
      (publicCausalInitialState input) (resolutionLength input) :=
  generalHistoryOfRoleHistory (publicRelationalConstitutiveRoles input)

/--
The public run is a nontrivial unbounded member of the general class.  Its
problem parameter is only the external input; all history data is executed and
then projected by the existing public construction.
-/
def publicRelationalRoleExtensiveFamily :
    RelationalRoleExtensiveFamily :=
  { State := CausalConstitutiveState
    Problem := fun _ => Unit
    initialState := fun {index} _ => publicCausalInitialState index
    stageCount := fun {index} _ => resolutionLength index
    producedHistory := fun {index} _ => publicGeneralRelationalHistory index
    nontrivialOpenings := fun {index} _ =>
      generalHistory_is_atLeastBinary (publicRelationalConstitutiveRoles index)
    unboundedIndex := id
    unboundedProblem := fun _ => ()
    unboundedStages := fun bound => Nat.le_succ bound }

/-- The same public execution as a member of the general binary subclass. -/
def publicBinaryRelationalRoleExtensiveFamily :
    BinaryRelationalRoleExtensiveFamily :=
  { toRelationalRoleExtensiveFamily := publicRelationalRoleExtensiveFamily
    binaryOpenings := fun {index} _ =>
      generalRoleHistory_uniformBinary
        (publicRelationalConstitutiveRoles index) }

theorem publicGeneralSourceWidth (input : Nat) :
    (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ()).frontier.length = 2 ^ (input + 1) := by
  change (relationalProfileFiniteCarrier
    (publicGeneralRelationalHistory input)).frontier.length = 2 ^ (input + 1)
  rw [relationalProfileFiniteCarrier_width]
  exact generalHistory_width_eq_twoPow
    (publicRelationalConstitutiveRoles input)

/-- Public specialization of the general `iff`, derived rather than restated. -/
theorem publicGeneral_fullWidth_iff_preservesConstitutedIdentities
    (input : Nat)
    (regime : ObligationRegime
      (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.HasFullExtensiveWidth ↔ PreservesIdentitiesSeparately regime :=
  RelationalRoleExtensiveFamily.fullWidth_iff_preservesConstitutedIdentities
    publicRelationalRoleExtensiveFamily () regime

/-- Public factorized-capacity specialization of the general theorem. -/
theorem publicGeneral_fullWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : ObligationRegime
      (publicRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.HasFullExtensiveWidth ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (publicRelationalRoleExtensiveFamily.sourceCarrier
            (index := input) ()).frontier.length) :=
  RelationalRoleExtensiveFamily.fullWidth_iff_exactRegimeCapacity
    publicRelationalRoleExtensiveFamily () regime

/--
Public specialization of the class-level target: exact `2^(input+1)` width is
equivalent to separate conservation of the already constituted identities.
-/
theorem publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
    (input : Nat)
    (regime : ObligationRegime
      (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      PreservesIdentitiesSeparately regime :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_preservesConstitutedIdentities
    publicBinaryRelationalRoleExtensiveFamily () regime

theorem publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier
    (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry := by
  exact publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
    input regime

/-- Exact separately-addressable capacity form of the same public `iff`. -/
theorem publicBinary_exponentialWidth_iff_exactRegimeCapacity
    (input : Nat)
    (regime : ObligationRegime
      (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
        (index := input) ())) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (publicBinaryRelationalRoleExtensiveFamily.sourceCarrier
            (index := input) ()).frontier.length) :=
  BinaryRelationalRoleExtensiveFamily.exponentialWidth_iff_exactRegimeCapacity
    publicBinaryRelationalRoleExtensiveFamily () regime

/-- Program compiled from exactly the same public role history. -/
def publicRoleIndexedProgram (input : Nat) :
    RoleIndexedProgram (publicRelationalConstitutiveRoles input) :=
  compileRoleHistory (publicRelationalConstitutiveRoles input)

theorem publicRoleIndexedProgram_atomCount (input : Nat) :
    (publicRoleIndexedProgram input).atomCount = input + 1 :=
  compileRoleHistory_atomCount_exact
    (publicRelationalConstitutiveRoles input)

theorem publicRoleIndexedProgram_interpretationExact
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    interpretRoleOccurrenceProfile
        (publicRoleIndexedProgram input) profile
        (canonicalRoleProfilePayload
          (publicRelationalConstitutiveRoles input) profile) =
      completedRoleAssignments (publicRelationalConstitutiveRoles input) :=
  interpretCompiledRoleHistory_exact
    (publicRelationalConstitutiveRoles input) profile

/-- Causal reduction of that same compiled public program. -/
def publicExecutedRoleReduction (input : Nat) :
    ExecutedRoleReductionHistory (publicRoleIndexedProgram input) :=
  buildExecutedRoleReductionHistory (publicRelationalConstitutiveRoles input)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_is_uniformBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_is_atLeastBinary
#print axioms ConstitutiveSearch.EndogenousDecomposition.generalHistory_width_eq_twoPow
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCausalInitialState
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneralRelationalHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinaryRelationalRoleExtensiveFamily
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneralSourceWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneral_fullWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicGeneral_fullWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_preservesConstitutedIdentities
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicBinary_exponentialWidth_iff_exactRegimeCapacity
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram_atomCount
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicRoleIndexedProgram_interpretationExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicExecutedRoleReduction
/- AXIOM_AUDIT_END -/
