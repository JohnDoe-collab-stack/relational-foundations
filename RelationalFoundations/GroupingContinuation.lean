import RelationalFoundations.GroupingNormalization
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping
universe u v w z t

structure Normative (rules : Rules.{u}) where
  Payload : rules.State → Type v
  Accept : (x : rules.State) → Payload x → Prop
  act : ∀ {x y}, rules.Step x y → Payload x → Payload y
  preserves : ∀ {x y} (step : rules.Step x y) (data : Payload x),
    Accept x data → Accept y (act step data)

namespace Normative
variable {rules : Rules.{u}}
def transport (norm : Normative.{u,v} rules) {x y} (path : Trace rules.Step x y) :
    norm.Payload x → norm.Payload y := Trace.act (Step := rules.Step) (D := norm.Payload) norm.act path

theorem transport_preserves (norm : Normative.{u,v} rules) {x y}
    (path : Trace rules.Step x y) (data : norm.Payload x) (accepted : norm.Accept x data) :
    norm.Accept y (norm.transport path data) :=
  Trace.act_preserves (Step := rules.Step) (D := norm.Payload) norm.act norm.Accept norm.preserves path data accepted

theorem transport_composes (norm : Normative.{u,v} rules) {x y z}
    (first : Trace rules.Step x y) (second : Trace rules.Step y z) (data : norm.Payload x) :
    norm.transport (first.append second) data = norm.transport second (norm.transport first data) :=
  Trace.act_append (Step := rules.Step) (D := norm.Payload) norm.act first second data

/-- Endpoint confluence does not supply this extra law on payload transports. -/
def Coherent (norm : Normative.{u,v} rules) : Prop :=
  ∀ {x y} (first second : Trace rules.Step x y) (data : norm.Payload x),
    norm.transport first data = norm.transport second data
end Normative

namespace Continuation
def run {S : Type u} {I : Type v} (next : S → I → S) : S → List I → S
  | state, [] => state
  | state, input :: rest => run next (next state input) rest

def events {S : Type u} {I : Type v} {E : Type w}
    (next : S → I → S) (emit : S → I → E) : S → List I → List E
  | _, [] => []
  | state, input :: rest => emit state input :: events next emit (next state input) rest

def observations {S : Type u} {I : Type v} {O : Type w}
    (next : S → I → S) (read : S → O) : S → List I → List O
  | _, [] => []
  | state, input :: rest => read state :: observations next read (next state input) rest

inductive Admitted {S : Type u} {I : Type v}
    (next : S → I → S) (allow : S → I → Type w) : S → List I → Type (max u v w) where
  | nil (state) : Admitted next allow state []
  | cons {state input rest} (witness : allow state input)
      (tail : Admitted next allow (next state input) rest) :
      Admitted next allow state (input :: rest)

structure Exact (Source : Type u) (Reduced : Type v) (Input : Type w)
    (Event : Type z) (Observation : Type t) where
  project : Source → Reduced
  sourceNext : Source → Input → Source
  reducedNext : Reduced → Input → Reduced
  sourceAllow : Source → Input → Type u
  reducedAllow : Reduced → Input → Type v
  toReduced : ∀ x a, sourceAllow x a → reducedAllow (project x) a
  toSource : ∀ x a, reducedAllow (project x) a → sourceAllow x a
  sourceEvent : Source → Input → Event
  reducedEvent : Reduced → Input → Event
  sourceRead : Source → Observation
  reducedRead : Reduced → Observation
  nextLaw : ∀ x a, project (sourceNext x a) = reducedNext (project x) a
  eventLaw : ∀ x a, sourceEvent x a = reducedEvent (project x) a
  readLaw : ∀ x, sourceRead x = reducedRead (project x)

namespace Exact
variable {S : Type u} {R : Type v} {I : Type w} {E : Type z} {O : Type t}
theorem stable (bridge : Exact S R I E O) {x y : S} (same : bridge.project x = bridge.project y)
    (input : I) : bridge.project (bridge.sourceNext x input) = bridge.project (bridge.sourceNext y input) :=
  (bridge.nextLaw x input).trans ((congrArg (fun state => bridge.reducedNext state input) same).trans
    (bridge.nextLaw y input).symm)

theorem run_exact (bridge : Exact S R I E O) (x : S) (inputs : List I) :
    bridge.project (run bridge.sourceNext x inputs) = run bridge.reducedNext (bridge.project x) inputs := by
  induction inputs generalizing x with
  | nil => rfl
  | cons input rest ih => exact (ih _).trans (congrArg (fun state => run bridge.reducedNext state rest) (bridge.nextLaw x input))

theorem events_exact (bridge : Exact S R I E O) (x : S) (inputs : List I) :
    events bridge.sourceNext bridge.sourceEvent x inputs =
      events bridge.reducedNext bridge.reducedEvent (bridge.project x) inputs := by
  induction inputs generalizing x with
  | nil => rfl
  | cons input rest ih =>
      change bridge.sourceEvent x input :: _ = bridge.reducedEvent (bridge.project x) input :: _
      rw [bridge.eventLaw x input]
      exact congrArg (List.cons _) ((ih _).trans (congrArg (fun state => events bridge.reducedNext bridge.reducedEvent state rest) (bridge.nextLaw x input)))

theorem observations_exact (bridge : Exact S R I E O) (x : S) (inputs : List I) :
    observations bridge.sourceNext bridge.sourceRead x inputs =
      observations bridge.reducedNext bridge.reducedRead (bridge.project x) inputs := by
  induction inputs generalizing x with
  | nil => rfl
  | cons input rest ih =>
      change bridge.sourceRead x :: _ = bridge.reducedRead (bridge.project x) :: _
      rw [bridge.readLaw x]
      exact congrArg (List.cons _) ((ih _).trans (congrArg (fun state => observations bridge.reducedNext bridge.reducedRead state rest) (bridge.nextLaw x input)))

def admitted (bridge : Exact S R I E O) {x : S} {inputs : List I} :
    Admitted bridge.sourceNext bridge.sourceAllow x inputs →
      Admitted bridge.reducedNext bridge.reducedAllow (bridge.project x) inputs
  | .nil _ => .nil _
  | .cons witness tail => .cons (bridge.toReduced _ _ witness)
      ((bridge.nextLaw _ _) ▸ admitted bridge tail)

def admittedSource (bridge : Exact S R I E O) {x : S} {inputs : List I} :
    Admitted bridge.reducedNext bridge.reducedAllow (bridge.project x) inputs →
      Admitted bridge.sourceNext bridge.sourceAllow x inputs :=
  match inputs with
  | [] => fun _ => .nil _
  | input :: _rest => fun trace =>
      match trace with
      | .cons witness tail => .cons (bridge.toSource x input witness)
          (admittedSource bridge ((bridge.nextLaw x input).symm ▸ tail))
termination_by structural inputs
end Exact

theorem run_append {S : Type u} {I : Type v} (next : S → I → S)
    (x : S) (first second : List I) :
    run next x (first ++ second) = run next (run next x first) second := by
  induction first generalizing x with
  | nil => rfl
  | cons input rest ih => exact ih _

theorem events_append {S : Type u} {I : Type v} {E : Type w}
    (next : S → I → S) (emit : S → I → E) (x : S) (first second : List I) :
    events next emit x (first ++ second) = events next emit x first ++ events next emit (run next x first) second := by
  induction first generalizing x with
  | nil => rfl
  | cons input rest ih => exact congrArg (List.cons (emit x input)) (ih _)
end Continuation
end RelationalFoundations.CertifiedGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Normative.transport
#print axioms RelationalFoundations.CertifiedGrouping.Normative.transport_preserves
#print axioms RelationalFoundations.CertifiedGrouping.Normative.transport_composes
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.Exact.run_exact
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.Exact.events_exact
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.Exact.observations_exact
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.Exact.admitted
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.Exact.admittedSource
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.run_append
#print axioms RelationalFoundations.CertifiedGrouping.Continuation.events_append
/- AXIOM_AUDIT_END -/
