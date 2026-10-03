import RelationalFoundations.GroupingContinuation
import RelationalFoundations.NativeForgettingContract
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping.Native
open NativeForgettingV1

/-- Historical proof carrier. The reduced executor receives only Memory. -/
def Source := (seed : Nat) × (frame : HeterogeneousFeedback.Frame seed) ×
  HeterogeneousFeedback.Execution (HeterogeneousFeedback.initial seed) frame

def project (source : Source) : Memory := forget source.2.1
def next (source : Source) (_ : Unit) : Source :=
  ⟨source.1, HeterogeneousFeedback.advance source.2.1, .step source.2.2⟩

def sourceEvent (source : Source) (_ : Unit) : ReducedHeterogeneous.Event :=
  ⟨source.2.1.1, (HeterogeneousFeedback.advance source.2.1).1, HeterogeneousFeedback.reaction source.2.1⟩

def reducedNext (memory : Memory) (_ : Unit) : Memory := step memory
def reducedEvent (memory : Memory) (_ : Unit) : ReducedHeterogeneous.Event := event memory
def reducedRead (memory : Memory) : Observation := observation memory

def bridge : Continuation.Exact Source Memory Unit ReducedHeterogeneous.Event Observation where
  project := project
  sourceNext := next
  reducedNext := reducedNext
  sourceAllow := fun _ _ => Unit
  reducedAllow := fun _ _ => Unit
  toReduced := fun _ _ _ => ()
  toSource := fun _ _ _ => ()
  sourceEvent := sourceEvent
  reducedEvent := reducedEvent
  sourceRead := fun source => nativeObservation source.2.1
  reducedRead := reducedRead
  nextLaw := fun source _ => forget_step source.2.2
  eventLaw := fun source _ => (event_native _ _ (forget_matches source.2.2)).symm
  readLaw := fun source => (observation_native _ _ (forget_matches source.2.2)).symm

theorem all_finite (source : Source) (inputs : List Unit) :
    project (Continuation.run next source inputs) = Continuation.run (fun memory (_ : Unit) => step memory) (project source) inputs ∧
    Continuation.events next sourceEvent source inputs =
      Continuation.events (fun memory (_ : Unit) => step memory) (fun memory (_ : Unit) => event memory) (project source) inputs ∧
    Continuation.observations next (fun x => nativeObservation x.2.1) source inputs =
      Continuation.observations (fun memory (_ : Unit) => step memory) observation (project source) inputs :=
  ⟨bridge.run_exact source inputs, bridge.events_exact source inputs, bridge.observations_exact source inputs⟩

/-- All suffixes admitted by the independent native predicate, with its actual
history and events, rather than a new admission invented by this adapter. -/
theorem all_native_admissible (source : Source) {target : HeterogeneousFeedback.State}
    (following : History HeterogeneousFeedback.Step (view (project source)) target)
    (allowed : HeterogeneousFeedback.Admissible following) :
    view (run (project source) following.length) = target ∧
    events (project source) following.length = historyEvents following ∧
    observations (project source) following.length = nativeObservations source.2.1 following.length :=
  forgetting_all_admissible source.2.2 following allowed

theorem all_new_certifications (source : Source) (count : Nat) :
    (certify (run (project source) count)).value = ((certify (run (project source) count)).node.map
      (intoNextFor (run (project source) count) (HeterogeneousFeedback.run source.2.1 count).1
        (matches_run (project source) source.2.1 (forget_matches source.2.2) count))).eval
          (HeterogeneousFeedback.advance (HeterogeneousFeedback.run source.2.1 count).1).2.support.read :=
  forgetting_all_new_evaluations source.2.2 count

theorem references_compose (source : Source) (first second : Nat) (kind : TypedResources.Kind)
    (ref : TypedResources.Ref source.2.1.2.context kind) :
    ((HeterogeneousFeedback.run source.2.1 first).2.compose
      (HeterogeneousFeedback.run (HeterogeneousFeedback.run source.2.1 first).1 second).2).embed kind ref =
    (HeterogeneousFeedback.run (HeterogeneousFeedback.run source.2.1 first).1 second).2.embed kind
      ((HeterogeneousFeedback.run source.2.1 first).2.embed kind ref) :=
  transports_compose source.2.1 first second kind ref

theorem forgotten_decision :
    ¬ (∃ recover : Memory → Bool, ∀ seed,
      recover (forget (HeterogeneousFeedback.run (HeterogeneousFeedback.initial seed) 2).1) =
        NativeForgettingContract.firstDecision seed) :=
  NativeForgettingContract.first_decision_irrecoverable
end RelationalFoundations.CertifiedGrouping.Native
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Native.next
#print axioms RelationalFoundations.CertifiedGrouping.Native.bridge
#print axioms RelationalFoundations.CertifiedGrouping.Native.reducedNext
#print axioms RelationalFoundations.CertifiedGrouping.Native.reducedEvent
#print axioms RelationalFoundations.CertifiedGrouping.Native.reducedRead
#print axioms RelationalFoundations.CertifiedGrouping.Native.all_finite
#print axioms RelationalFoundations.CertifiedGrouping.Native.all_native_admissible
#print axioms RelationalFoundations.CertifiedGrouping.Native.all_new_certifications
#print axioms RelationalFoundations.CertifiedGrouping.Native.references_compose
#print axioms RelationalFoundations.CertifiedGrouping.Native.forgotten_decision
/- AXIOM_AUDIT_END -/
