import RelationalFoundations.Cardinalization
import RelationalFoundations.EquippedQuantity
import RelationalFoundations.Interpretation
set_option genInjectivity false

namespace RelationalFoundations.Perimetral

inductive Node
  | first | second | third | fourth | free (index : Nat)
  deriving DecidableEq

inductive ExplicitToken
  | primitive (index : Nat) | formed (index : Nat)
  deriving DecidableEq

inductive ImplicitToken
  | primitive (index : Nat) | formed (index : Nat)
  deriving DecidableEq

def explicit : Node → ExplicitToken
  | .first => .primitive 0
  | .second => .primitive 1
  | .third => .primitive 2
  | .fourth => .primitive 3
  | .free index => .formed index

def implicit : Node → ImplicitToken
  | .first => .primitive 0
  | .second => .primitive 1
  | .third => .primitive 2
  | .fourth => .primitive 3
  | .free index => .formed index

/-- Distinct licenses are distinct relation witnesses in a fixed fiber. -/
inductive Compatible : ImplicitToken → ExplicitToken → Type
  | licensed (license : Bool) : Compatible source target

abbrev Next (source target : Node) := Compatible (implicit source) (explicit target)

def spine : Spine Next Node.first :=
  Spine.advance (Next := Next) (target := Node.second) (.licensed true)
    (Spine.advance (Next := Next) (source := Node.second) (target := Node.third) (.licensed false)
      (Spine.advance (Next := Next) (source := Node.third) (.licensed true) (Spine.boundary Node.fourth)))

def presentation : CircularPresentation where
  Node := Node
  Next := Next
  start := .first
  spine := spine
  Terminal := ImplicitToken
  Initial := ExplicitToken
  terminalInterface := implicit
  initialInterface := explicit
  Close := Compatible
  junction := .licensed true

def continuation : OneStepContinuation presentation := ⟨.free 0, .licensed false⟩

def boundaryInterpretation : BoundaryInterpretation continuation := .ofContinuation continuation

theorem interior_has_three : presentation.interiorHistory.length = 3 := rfl
theorem extended_has_four : continuation.history.length = 4 := rfl

def interiorQuantity : StructuralQuantity :=
  ⟨presentation.InternalRole, presentation.InteriorOccurrence,
    presentation.InteriorRealizes, presentation.interiorRealization⟩

def cardinalization : ExactTransport presentation.InternalRole (Fin 3) :=
  presentation.interiorCardinalization

theorem generated_target_differs_from_initial :
    explicit boundaryInterpretation.actualStep.target ≠ presentation.boundary.initial := by
  intro eq
  cases eq

def obstruction : PoleObstruction where
  Pole := Bool
  left := false
  right := true
  rejectsIdentification := fun eq => by cases eq

structure Attempt (candidate : RootedConstruction Next Node.first) where
  step : OneStepContinuation presentation
  candidateExact : candidate = step.construction
  interpretation : BoundaryInterpretation step
  totalization : BilateralTotalization obstruction

def regimeAnalysis : ObstructedRegime presentation.interiorConstruction where
  Admission := fun candidate => PLift (candidate = presentation.interiorConstruction) ⊕ Attempt candidate
  Attempt := Attempt
  canonicalAdmission := .inl ⟨rfl⟩
  analyze := fun _ witness => witness
  reject := fun _ attempt => obstruction.rejectTotalization attempt.totalization

def regime : ExactRegime presentation.interiorConstruction := regimeAnalysis.exact
def turning : TurningWithExit continuation regime := continuation.verifiedExit regime

def next : Node → Node
  | .first => .second
  | .second => .third
  | .third => .fourth
  | .fourth => .free 0
  | .free n => .free (n + 1)

def generatedStep (source : Node) : Next source (next source) := .licensed false

def iterate : Nat → RootedConstruction Next Node.first
  | 0 => presentation.interiorConstruction
  | n + 1 =>
    let prior := iterate n
    ⟨next prior.endpoint, .extend prior.history (generatedStep prior.endpoint)⟩

theorem iterate_length (n : Nat) : (iterate n).history.length = 3 + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (iterate n).history.length + 1 = 3 + (n + 1)
    rw [ih, Nat.add_assoc]

theorem iterationStrictGrowth (n : Nat) : 3 < 3 + (n + 1) := by
  induction n with
  | zero => exact Nat.lt_succ_self 3
  | succ n ih => exact Nat.le.step ih

theorem iterate_outside_regime (n : Nat) : regime.Admission (iterate (n + 1)) → False := by
  intro admission
  have eq := regime.classify _ admission
  have lengthEq := congrArg (fun h : RootedConstruction Next Node.first => h.history.length) eq
  rw [iterate_length] at lengthEq
  change 3 + (n + 1) = 3 at lengthEq
  exact Nat.ne_of_gt (iterationStrictGrowth n) lengthEq

def forgetting : HistoryInterpretation Next where
  ConcreteState := Unit
  ConcreteStep := fun _ _ => Unit
  stateAt := fun _ => ()
  stepAt := fun _ => ()

theorem license_witnesses_distinct :
    (Compatible.licensed true : Next .first .second) ≠ .licensed false := by
  intro eq
  cases eq

theorem forgetting_not_faithful :
    ¬ Function.Injective (fun w : Next .first .second => forgetting.stepAt w) := by
  intro faithful
  exact license_witnesses_distinct (faithful rfl)

end RelationalFoundations.Perimetral
