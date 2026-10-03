import RelationalFoundations.BinaryGrouping
import RelationalFoundations.GroupingInstances
import RelationalFoundations.GroupingImage
import RelationalFoundations.HistoricalGrouping
import RelationalFoundations.TypedResourceOrder
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGroupingTests
open CertifiedGrouping
def two : Binary.Shape := .more (.more .empty)
def low : Binary.Profile two := (false, (false, ()))
def high : Binary.Profile two := (true, (true, ()))

def real_peak : Join (Binary.Move (Binary.enabled two))
    (true, (false, ())) (false, (true, ())) :=
  (Binary.rules (Binary.enabled two)).diamond .head (.tail .head)

theorem projections_each_separate :
    Binary.projection (Binary.enabled two) .here low ≠ Binary.projection (Binary.enabled two) .here high ∧
    Binary.projection (Binary.enabled two) (.there .here) low ≠ Binary.projection (Binary.enabled two) (.there .here) high := by
  constructor
  · intro same
    exact Bool.noConfusion (congrArg (fun p : Binary.Profile two => p.2.1) same)
  · intro same
    exact Bool.noConfusion (congrArg (fun p : Binary.Profile two => p.1) same)

def nevertheless_connected : ProjectionFamily.Path (Binary.projection (Binary.enabled two)) low high :=
  Binary.familyConnected low high

def current : Bool × Bool → Bool := Prod.fst
def shift (x : Bool × Bool) (_ : Unit) : Bool × Bool := (x.2, x.1)
theorem current_equal_future_distinct :
    current (false, false) = current (false, true) ∧
    current (shift (false, false) ()) ≠ current (shift (false, true) ()) :=
  ⟨rfl, Bool.false_ne_true⟩

inductive Fork where | root | left | right
inductive ForkStep : Fork → Fork → Type where | left : ForkStep .root .left | right : ForkStep .root .right
theorem fork_left_terminal {target} : Trace ForkStep .left target → target = .left
  | .nil _ => rfl
  | .cons step _ => nomatch step
theorem fork_right_terminal {target} : Trace ForkStep .right target → target = .right
  | .nil _ => rfl
  | .cons step _ => nomatch step
theorem fork_no_join : ¬ Nonempty (Join ForkStep .left .right) := by
  intro ⟨joined⟩
  exact Fork.noConfusion ((fork_left_terminal joined.left).symm.trans (fork_right_terminal joined.right))

theorem cycle_forbids_strict_rank (rank : Bool → Nat)
    (one : rank true < rank false) (two : rank false < rank true) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans one two)

theorem neutral_forbids_strict_rank (rules : Rules) (x : rules.State) (step : rules.Step x x) : False :=
  Nat.lt_irrefl _ (rules.decreases step)

inductive Tagged : Bool → Bool → Type where
  | change (tag : Bool) : Tagged false true

def tagged : Rules where
  State := Bool
  Step := Tagged
  rank := fun bit => if bit then 0 else 1
  choices := fun bit => match bit with
    | false => [⟨true, .change false⟩, ⟨true, .change true⟩]
    | true => []
  locate := fun step => match step with
    | .change false => ⟨_, .head _, HEq.rfl⟩
    | .change true => ⟨_, .tail _ (.head _), HEq.rfl⟩
  decreases := fun step => match step with | .change _ => Nat.zero_lt_succ 0
  diamond := fun one two => match one, two with | .change _, .change _ => ⟨true, .nil _, .nil _⟩

def taggedNorm : Normative tagged where
  Payload := fun _ => Bool
  Accept := fun _ _ => True
  act := fun step data => match step with | .change flag => if flag then !data else data
  preserves := fun _ _ _ => True.intro

theorem equal_target_different_transport :
    tagged.normal false = tagged.normal true ∧
    taggedNorm.transport (Trace.one (.change false)) false ≠
      taggedNorm.transport (Trace.one (.change true)) false :=
  ⟨tagged.normal_step (.change false), Bool.false_ne_true⟩

theorem admissions_mismatch :
    current (false, false) = current (false, true) ∧
    (false, false).2 ≠ (false, true).2 := ⟨rfl, Bool.false_ne_true⟩

def emptyRules : Rules where
  State := Empty
  Step := fun _ _ => Empty
  rank := fun x => nomatch x
  choices := fun x => nomatch x
  locate := fun step => nomatch step
  decreases := fun step => nomatch step
  diamond := fun step _ => nomatch step

def emptySource : FiniteImage.Source Empty where
  equality := fun x => nomatch x
  frontier := []
  complete := fun x => nomatch x
  distinct := .nil
theorem empty_width : (FiniteImage.frontier emptyRules emptySource).length = 0 := rfl

def singletonSource : FiniteImage.Source Unit :=
  ⟨fun x y => match x, y with | (), () => isTrue rfl,
    [()], fun x => by cases x; exact .head _, .cons (fun _ impossible _ => nomatch impossible) .nil⟩
theorem inhabited_width :
    (FiniteImage.frontier (Binary.rules (n := .empty) ()) singletonSource).length = 1 := rfl

def additionalLicense : Extension (Binary.rules (n := .more .empty) (false, ())) (Binary.rules (n := .more .empty) (true, ())) where
  embedding := id
  lift := by
    intro p q step
    change Binary.Move (n := .more .empty) (false, ()) p q at step
    cases step with
    | tail child => cases child

theorem new_license_requires_renormalization :
    (Binary.rules (n := .more .empty) (true, ())).normal
      ((Binary.rules (n := .more .empty) (false, ())).normal (false, ())) ≠
        (Binary.rules (n := .more .empty) (false, ())).normal (false, ()) := by
  intro same
  exact Bool.noConfusion (congrArg Prod.fst same)

def checkProfiles {shape : Binary.Shape} (mask : Binary.Profile shape) : Bool :=
  (Binary.enumerate shape).all (fun source =>
    let produced := (Binary.rules mask).normalize source
    let same := match Binary.equality shape produced.target (Binary.selected mask source) with
      | isFalse _ => false
      | isTrue _ => true
    same && Nat.ble produced.trace.length (Binary.rank mask source))

def checkNormalizer : Bool :=
  [0, 1, 2, 3, 4, 5, 6].all (fun size =>
    (Binary.enumerate (Binary.shape size)).all checkProfiles)

def pairCount : List Nat → Nat
  | [] => 0
  | size :: rest =>
      let width := (Binary.enumerate (Binary.shape size)).length
      width * width + pairCount rest

#guard checkNormalizer
#guard Nat.beq (pairCount [0, 1, 2, 3, 4, 5, 6]) 5461
#eval match checkNormalizer with
  | true => "GROUPING_V5_RUNTIME_OK: 5461 mask/profile pairs; dimensions 0..6; normalization and trace bounds"
  | false => "GROUPING_V5_RUNTIME_FAILED"

end RelationalFoundations.CertifiedGroupingTests
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGroupingTests.real_peak
#print axioms RelationalFoundations.CertifiedGroupingTests.projections_each_separate
#print axioms RelationalFoundations.CertifiedGroupingTests.nevertheless_connected
#print axioms RelationalFoundations.CertifiedGroupingTests.current_equal_future_distinct
#print axioms RelationalFoundations.CertifiedGroupingTests.fork_no_join
#print axioms RelationalFoundations.CertifiedGroupingTests.cycle_forbids_strict_rank
#print axioms RelationalFoundations.CertifiedGroupingTests.neutral_forbids_strict_rank
#print axioms RelationalFoundations.CertifiedGroupingTests.tagged
#print axioms RelationalFoundations.CertifiedGroupingTests.equal_target_different_transport
#print axioms RelationalFoundations.CertifiedGroupingTests.admissions_mismatch
#print axioms RelationalFoundations.CertifiedGroupingTests.empty_width
#print axioms RelationalFoundations.CertifiedGroupingTests.inhabited_width
#print axioms RelationalFoundations.CertifiedGroupingTests.additionalLicense
#print axioms RelationalFoundations.CertifiedGroupingTests.new_license_requires_renormalization
#print axioms RelationalFoundations.CertifiedGroupingTests.checkNormalizer
/- AXIOM_AUDIT_END -/
