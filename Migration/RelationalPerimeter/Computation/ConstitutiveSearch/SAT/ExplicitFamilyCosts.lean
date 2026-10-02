import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyResources

/-!
# Certified structural counts for the explicit SAT family

This module records exact structural counts for the announced explicit strategy.

These are not machine-runtime bounds.  In particular, they do not yet charge
for executable relation search, transport-code closure search, representation
costs, or proof checking.  They are certified counts of objects and operations
already present in the constructed trajectory.
-/

namespace ConstitutiveSearch
namespace SAT

namespace FlipSymmetricTrajectory

/-- Number of certified split/reduction levels in a trajectory. -/
def stepCount
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      Nat
  | .done _ =>
      0
  | .step _var _fresh _symmetric tail =>
      tail.stepCount + 1

/-- The executable step count agrees exactly with the trajectory index. -/
theorem stepCount_eq_index
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.stepCount = length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      rw [show
        (FlipSymmetricTrajectory.step
          var fresh symmetric tail).stepCount =
            tail.stepCount + 1 from rfl]
      rw [inductionHypothesis]

/--
Number of frontier-state slots explicitly encountered by the announced
singleton -> pair -> singleton strategy.

A terminal trajectory contributes one singleton slot.  Each nonterminal level
adds one singleton slot and one two-state split frontier, hence three slots.
-/
def frontierSlotCount
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      Nat
  | .done _ =>
      1
  | .step _var _fresh _symmetric tail =>
      3 + tail.frontierSlotCount

/-- One nonterminal level contributes exactly three frontier slots. -/
theorem frontierSlotCount_succ
    (length : Nat) :
    3 + (3 * length + 1) =
      3 * (length + 1) + 1 := by
  calc
    3 + (3 * length + 1)
        = (3 + 3 * length) + 1 :=
          (Nat.add_assoc 3 (3 * length) 1).symm
    _ = (3 * length + 3) + 1 :=
          congrArg
            (fun value => value + 1)
            (Nat.add_comm 3 (3 * length))
    _ = 3 * (length + 1) + 1 := by
          rw [Nat.mul_succ]

/-- Exact closed form for the structural frontier-slot count. -/
theorem frontierSlotCount_eq
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.frontierSlotCount =
      3 * length + 1 := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      rw [show
        (FlipSymmetricTrajectory.step
          var fresh symmetric tail).frontierSlotCount =
            3 + tail.frontierSlotCount from rfl]
      rw [inductionHypothesis]
      exact frontierSlotCount_succ _

/--
Combined structural work count for any flip-symmetric trajectory.
This still excludes relation-search and representation costs.
-/
def structuralWorkUnits
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    Nat :=
  trajectory.stepCount +
    trajectory.frontierSlotCount

/-- Pure arithmetic identity used by the structural work count. -/
theorem structuralWorkArithmetic
    (count : Nat) :
    count + (3 * count + 1) =
      4 * count + 1 := by
  calc
    count + (3 * count + 1)
        = (count + 3 * count) + 1 :=
          (Nat.add_assoc count (3 * count) 1).symm
    _ = (3 * count + count) + 1 :=
          congrArg
            (fun value => value + 1)
            (Nat.add_comm count (3 * count))
    _ = 4 * count + 1 :=
          congrArg
            (fun value => value + 1)
            (Nat.succ_mul 3 count).symm

/-- Exact generic work count for every certified flip-symmetric trajectory. -/
theorem structuralWorkUnits_eq
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.structuralWorkUnits =
      4 * length + 1 := by
  unfold structuralWorkUnits
  calc
    trajectory.stepCount +
          trajectory.frontierSlotCount
        =
      length + trajectory.frontierSlotCount :=
        congrArg
          (fun value =>
            value + trajectory.frontierSlotCount)
          (FlipSymmetricTrajectory.stepCount_eq_index
            trajectory)
    _ =
      length + (3 * length + 1) :=
        congrArg
          (Nat.add length)
          (FlipSymmetricTrajectory.frontierSlotCount_eq
            trajectory)
    _ = 4 * length + 1 :=
        structuralWorkArithmetic length

end FlipSymmetricTrajectory

/--
One proof object collecting the exact structural counts already established for
the closed family `F(n)`.
-/
structure ExplicitFamilyCertifiedCounts
    (count : Nat) : Prop where
  clauseCount :
    (explicitStackedSymmetricFamily count).length =
      2 * count
  literalCount :
    Cnf.literalCount
      (explicitStackedSymmetricFamily count) =
        4 * count
  decisionResourceSize :
    (explicitFamilyDecisionResource count).length =
      count
  trajectoryStepCount :
    (explicitFamilyResourceTrajectory count).trajectory.stepCount =
      count
  widthTraceEntries :
    (explicitFamilyResourceTrajectory count).trajectory.widthTrace.length =
      2 * count + 1
  frontierSlotCount :
    (explicitFamilyResourceTrajectory count).trajectory.frontierSlotCount =
      3 * count + 1
  widthBound :
    ∀ width : Nat,
      width ∈
        (explicitFamilyResourceTrajectory count).trajectory.widthTrace →
          width ≤ 2
  endpointDepth :
    (explicitFamilyResourceTrajectory count).finish.depth =
      count
  endpointTerminal :
    ResourceTerminal
      (explicitFamilyResourceTrajectory count).finish
      []

/-- Complete certified structural accounting for every member of the family. -/
theorem explicitFamilyCertifiedCounts
    (count : Nat) :
    ExplicitFamilyCertifiedCounts count := by
  constructor
  · change
      (stackedSymmetricBlocks count count).length =
        2 * count
    exact
      stackedSymmetricBlocks_length count count
  · change
      Cnf.literalCount
        (stackedSymmetricBlocks count count) =
          4 * count
    exact
      stackedSymmetricBlocks_literalCount count count
  · exact
      explicitFamilyDecisionResource_length count
  · exact
      FlipSymmetricTrajectory.stepCount_eq_index
        (explicitFamilyResourceTrajectory count).trajectory
  · exact
      FlipSymmetricTrajectory.widthTrace_length
        (explicitFamilyResourceTrajectory count).trajectory
  · exact
      FlipSymmetricTrajectory.frontierSlotCount_eq
        (explicitFamilyResourceTrajectory count).trajectory
  · intro width member
    exact
      explicitFamilyResourceTrajectory_width_le_two
        count
        width
        member
  · exact
      explicitFamilyEndpoint_depth count
  · exact
      explicitFamilyEndpoint_terminal count

/--
A deliberately narrow structural work proxy: certified trajectory levels plus
frontier-state slots explicitly encountered.

This excludes relation-search cost, certificate representation size, closure
search, and machine-level execution cost.
-/
def explicitFamilyStructuralWorkUnits
    (count : Nat) : Nat :=
  (explicitFamilyResourceTrajectory count).trajectory.structuralWorkUnits

/-- Exact value of the narrow structural work proxy. -/
theorem explicitFamilyStructuralWorkUnits_eq
    (count : Nat) :
    explicitFamilyStructuralWorkUnits count =
      4 * count + 1 :=
  FlipSymmetricTrajectory.structuralWorkUnits_eq
    (explicitFamilyResourceTrajectory count).trajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.stepCount
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.stepCount_eq_index
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.frontierSlotCount
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.frontierSlotCount_succ
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.frontierSlotCount_eq
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.structuralWorkUnits
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.structuralWorkArithmetic
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.structuralWorkUnits_eq
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyCertifiedCounts
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertifiedCounts
#print axioms ConstitutiveSearch.SAT.explicitFamilyStructuralWorkUnits
#print axioms ConstitutiveSearch.SAT.explicitFamilyStructuralWorkUnits_eq
/- AXIOM_AUDIT_END -/
