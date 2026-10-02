import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalFoundationBridge
import Constitution.GenericCircularView
set_option genInjectivity false

namespace FoundationMigrationTests
open StrongPerimetralTurning
open StrongPerimetralTurning.Example

/-- The computation actually carries the new rooted history type. -/
def stateConstitution (state : ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveState) :
    RelationalFoundations.RootedConstruction (@GeneratedStep examplePresentation)
      (initialPositive examplePresentation) := state.constitutedHistory

theorem state_endpoint_exact (state : ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveState) :
    (stateConstitution state).endpoint = state.constitutedHistory.endpoint := rfl

theorem state_history_exact (state : ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveState) :
    (stateConstitution state).history = state.constitutedHistory.history := rfl

theorem iteration_consumes_foundation (P : CircularPresentation) (n : Nat) :
    ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory P n =
      RelationalFoundations.ConstitutiveGeneration.iterate (perimeterDeployment P) (fun state => generate state) n := rfl

theorem old_occurrence_actual (P : CircularPresentation) (n : Nat)
    (old : History.Occurrence (ConstitutiveSearch.ConstitutiveGeneration.iteratedHistory P n).history) :
    (ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit P n).forward (.inl old) = .earlier old := rfl

theorem fresh_occurrence_actual (P : CircularPresentation) (n : Nat) :
    (ConstitutiveSearch.ConstitutiveGeneration.successorOccurrenceSplit P n).forward (.inr ()) = .last := rfl

def exactRichQuantity (P : CircularPresentation) := RelationalFoundations.PerimetralView.circularQuantity P

theorem rich_formation_actual (P : CircularPresentation) (history : RootedGeneratedHistory P) :
    (RelationalFoundations.PerimetralView.richFormation history).toHistory = history.history :=
  RelationalFoundations.PerimetralView.richFormation_history_exact history

theorem rich_records_roundTrip (P : CircularPresentation) (history : RootedGeneratedHistory P)
    (record : RelationalFoundations.Formation.Record (RelationalFoundations.PerimetralView.richFormation history)) :
    (RelationalFoundations.PerimetralView.richRecords history).backward
      ((RelationalFoundations.PerimetralView.richRecords history).forward record) = record :=
  (RelationalFoundations.PerimetralView.richRecords history).forwardBackward record
end FoundationMigrationTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms FoundationMigrationTests.stateConstitution
#print axioms FoundationMigrationTests.state_endpoint_exact
#print axioms FoundationMigrationTests.state_history_exact
#print axioms FoundationMigrationTests.iteration_consumes_foundation
#print axioms FoundationMigrationTests.old_occurrence_actual
#print axioms FoundationMigrationTests.fresh_occurrence_actual
#print axioms FoundationMigrationTests.exactRichQuantity
#print axioms FoundationMigrationTests.rich_formation_actual
#print axioms FoundationMigrationTests.rich_records_roundTrip
/- AXIOM_AUDIT_END -/
