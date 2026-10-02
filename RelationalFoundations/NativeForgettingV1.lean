import RelationalFoundations.ReducedWeakening
set_option genInjectivity false

/-!
Version 1: historical forgetting relative to the three native consumers.
The execution memory contains position and active number. All new production
certificates are obtained from a finite typed frontier, without a prefix replay.
-/

namespace RelationalFoundations.NativeForgettingV1
open TypedResources
open ReducedHeterogeneous (Phase phaseAt)

structure Memory where
  position : Nat
  active : Nat

def initial (number : Nat) : Memory := ⟨0, number⟩
def view (m : Memory) := ReducedHeterogeneous.state (phaseAt m.position) m.active

def Context : Phase → List Kind
  | .ready => [.number]
  | .observed => [.truth, .number]
  | .updated => [.number]

def Result : Phase → Kind
  | .ready => .truth
  | .observed => .number
  | .updated => .number

def emptyPorts {family : Kind → Type} (kind : Kind) (ref : Ref [] kind) : family kind := nomatch ref

def prependPorts {family : Kind → Type} {head : Kind} {rest : List Kind}
    (value : family head) (previous : ∀ kind, Ref rest kind → family kind) :
    (kind : Kind) → Ref (head :: rest) kind → family kind
  | _, .head => value
  | kind, .old ref => previous kind ref

def read : (stage : Phase) → Nat → (kind : Kind) → Ref (Context stage) kind → Value kind
  | .ready, n => prependPorts n emptyPorts
  | .observed, n => prependPorts (TypedResources.test n) (prependPorts n emptyPorts)
  | .updated, n => prependPorts n emptyPorts

def operation : (stage : Phase) → Operation (Context stage) (Result stage)
  | .ready => .test .head
  | .observed => .adjust .head (.old .head)
  | .updated => .reuse .head

def produce (stage : Phase) (n : Nat) : Value (Result stage) :=
  (operation stage).eval (read stage n)

def target (stage : Phase) (n : Nat) : HeterogeneousFeedback.State :=
  match stage with
  | .ready => .observed n (produce .ready n)
  | .observed => .updated (produce .observed n)
  | .updated => .ready (produce .updated n)

def step (m : Memory) : Memory := ⟨m.position + 1, ReducedHeterogeneous.number (target (phaseAt m.position) m.active)⟩

def eventAt (stage : Phase) (n : Nat) : ReducedHeterogeneous.Event :=
  match stage with
  | .ready => ⟨.ready n, target .ready n, .observe n (produce .ready n)⟩
  | .observed => ⟨.observed n (TypedResources.test n), target .observed n,
      .act n (TypedResources.test n) (read .observed n .truth .head) (produce .observed n)⟩
  | .updated => ⟨.updated n, target .updated n, .reuse n (produce .updated n)⟩

def event (m : Memory) := eventAt (phaseAt m.position) m.active

theorem target_next (stage : Phase) (n : Nat) : target stage n = HeterogeneousFeedback.next (ReducedHeterogeneous.state stage n) := by
  cases stage <;> rfl

theorem event_canonical (m : Memory) : event m =
    ⟨view m, HeterogeneousFeedback.next (view m), HeterogeneousFeedback.canonical (view m)⟩ := by
  unfold event view
  cases phaseAt m.position <;> rfl

theorem event_admitted (m : Memory) : HeterogeneousFeedback.LocalAdmission (event m).2.2 := by
  rw [event_canonical]
  exact HeterogeneousFeedback.canonical_admitted _

theorem step_view (m : Memory) : view (step m) = HeterogeneousFeedback.next (view m) := by
  change ReducedHeterogeneous.state ((phaseAt m.position).next)
    (ReducedHeterogeneous.number (target (phaseAt m.position) m.active)) = _
  unfold view
  cases phaseAt m.position <;> rfl

/-- Coordinates are relative to one execution. Cross-execution comparison is
provided by explicit native frontier maps in the bridge module. -/
def coordinate : (stage : Phase) → Nat → (kind : Kind) → Ref (Context stage) kind → Nat
  | .ready, position => prependPorts position emptyPorts
  | .observed, position => prependPorts position (prependPorts position.pred emptyPorts)
  | .updated, position => prependPorts position emptyPorts

def inputCoordinates (stage : Phase) (position : Nat) : AnyRef (Context stage) → Kind × Nat
  | .number ref => ⟨.number, coordinate stage position .number ref⟩
  | .truth ref => ⟨.truth, coordinate stage position .truth ref⟩

inductive Operator where
  | test | adjust | reuse

def operator : Phase → Operator
  | .ready => .test
  | .observed => .adjust
  | .updated => .reuse

structure Observation where
  occurrence : Nat
  kind : Kind
  value : Value kind
  operator : Operator
  inputs : List (Kind × Nat)

def observation (m : Memory) : Observation :=
  ⟨m.position + 1, Result (phaseAt m.position), produce (phaseAt m.position) m.active,
    operator (phaseAt m.position),
    (operation (phaseAt m.position)).inputs.map (inputCoordinates (phaseAt m.position) m.position)⟩

/-- A new node and its evaluation certificate, using only the current frontier.
The parameter contains exactly the two scalar fields of memory. -/
structure Production (m : Memory) where
  node : Operation (Context (phaseAt m.position)) (Result (phaseAt m.position))
  value : Value (Result (phaseAt m.position))
  nodeExact : node = operation (phaseAt m.position)
  certified : value = node.eval (read (phaseAt m.position) m.active)

def certify (m : Memory) : Production m := ⟨operation _, produce _ m.active, rfl, rfl⟩

def outputRead (m : Memory) : (kind : Kind) →
    Ref (Result (phaseAt m.position) :: Context (phaseAt m.position)) kind → Value kind
  | _, .head => (certify m).value
  | kind, .old ref => read (phaseAt m.position) m.active kind ref

theorem new_evaluation_certified (m : Memory) :
    outputRead m (Result (phaseAt m.position)) .head =
      ((certify m).node.map (fun _ => Ref.old)).eval (outputRead m) :=
  (certify m).certified.trans (Operation.eval_map (fun _ => Ref.old) (outputRead m) (certify m).node).symm

theorem frontier_local (m : Memory)
    (other : ∀ kind, Ref (Context (phaseAt m.position)) kind → Value kind)
    (same : ∀ kind ref, AnyRef.pack kind ref ∈ (operation (phaseAt m.position)).inputs →
      read (phaseAt m.position) m.active kind ref = other kind ref) :
    produce (phaseAt m.position) m.active = (operation (phaseAt m.position)).eval other :=
  ReducedHeterogeneous.evaluation_local _ _ _ same

def sweep (position active : Nat) : Nat → Nat
  | 0 => active
  | count + 1 => ReducedHeterogeneous.number (target (phaseAt (position + count)) (sweep position active count))

def run (m : Memory) (count : Nat) : Memory := ⟨m.position + count, sweep m.position m.active count⟩

theorem run_succ (m : Memory) (count : Nat) : run m (count + 1) = step (run m count) := by
  unfold run step
  rw [← Nat.add_assoc]
  rfl

theorem run_add (m : Memory) (one two : Nat) : run m (one + two) = run (run m one) two := by
  induction two with
  | zero => rfl
  | succ two ih =>
      exact (congrArg (run m) (Nat.add_assoc one two 1).symm).trans
        ((run_succ m (one + two)).trans ((congrArg step ih).trans (run_succ (run m one) two).symm))

/-- Observations are an optional output log; the persistent state stays Memory. -/
def observations (m : Memory) : Nat → List Observation
  | 0 => []
  | count + 1 => observations m count ++ [observation (run m count)]

def erase (m : ReducedHeterogeneous.Memory) : Memory := ⟨m.position, m.active⟩

theorem erase_step (m : ReducedHeterogeneous.Memory) : erase (ReducedHeterogeneous.step m) = step (erase m) := by
  unfold erase ReducedHeterogeneous.step ReducedHeterogeneous.nextState ReducedHeterogeneous.output step
  cases phaseAt m.position <;> rfl

theorem erase_run (m : ReducedHeterogeneous.Memory) (count : Nat) : erase (ReducedHeterogeneous.run m count) = run (erase m) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (congrArg erase (ReducedHeterogeneous.run_succ m count)).trans
        ((erase_step _).trans ((congrArg step ih).trans (run_succ (erase m) count).symm))

def cost (m : Memory) : Nat := 3 + ReducedHeterogeneous.digits m.position + ReducedHeterogeneous.digits m.active

theorem cost_removed_origin (m : ReducedHeterogeneous.Memory) :
    ReducedHeterogeneous.cacheCost m = cost (erase m) + (1 + ReducedHeterogeneous.digits m.origin) := by
  unfold ReducedHeterogeneous.cacheCost cost erase
  rw [Nat.add_right_comm 4 (ReducedHeterogeneous.digits m.origin) (ReducedHeterogeneous.digits m.position),
    Nat.add_right_comm (4 + ReducedHeterogeneous.digits m.position) (ReducedHeterogeneous.digits m.origin) (ReducedHeterogeneous.digits m.active)]
  rw [← Nat.add_assoc (3 + ReducedHeterogeneous.digits m.position + ReducedHeterogeneous.digits m.active) 1,
    Nat.add_right_comm (3 + ReducedHeterogeneous.digits m.position) (ReducedHeterogeneous.digits m.active) 1,
    Nat.add_right_comm 3 (ReducedHeterogeneous.digits m.position) 1]

end RelationalFoundations.NativeForgettingV1
