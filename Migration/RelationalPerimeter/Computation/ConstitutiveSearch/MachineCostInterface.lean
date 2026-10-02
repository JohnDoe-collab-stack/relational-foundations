import RelationalPerimeter.Computation.ConstitutiveSearch.ComplexityInterface

/-!
# Separation between representation charge and machine cost

ComplexityInterface deliberately leaves AtomicCosts abstract.  The SAT layers
instantiate them with binary representation charges.  A representation charge
must not silently become a machine-time claim.

This module makes the missing bridge explicit.

* MachineCostModel is a separately declared machine-level atomic-cost model.
* affineAtomicEnvelope turns a representation charge into a declared machine
  envelope using a multiplicative factor and additive per-event overhead.
* RepresentationMachineBridge is the proof obligation that every machine-level
  atomic cost is below that envelope.
* only after such a bridge is supplied may an aggregate machine-cost theorem be
  derived.

No bridge is postulated by this module.
-/

namespace ConstitutiveSearch

/-- Pointwise ordering between two atomic-cost assignments. -/
structure AtomicCostPointwiseLe
    (lower upper : AtomicCosts) : Prop where
  syntaxLe :
    lower.syntaxUnit ≤ upper.syntaxUnit
  frontierLe :
    lower.frontierSlot ≤ upper.frontierSlot
  provenanceLe :
    lower.provenanceUnit ≤ upper.provenanceUnit
  certificateLe :
    lower.certificateAtom ≤ upper.certificateAtom
  relationLe :
    lower.relationFindCall ≤ upper.relationFindCall
  closurePrimitiveLe :
    lower.closurePrimitiveQuery ≤ upper.closurePrimitiveQuery
  closureCandidateLe :
    lower.closureCompositionCandidate ≤
      upper.closureCompositionCandidate
  terminalLe :
    lower.terminalCheck ≤ upper.terminalCheck

/-- Pointwise atomic-cost domination lifts to the aggregate charged cost. -/
theorem chargedCost_mono
    (counts : ComplexityCounts)
    (lower upper : AtomicCosts)
    (bounded :
      AtomicCostPointwiseLe lower upper) :
    chargedCost counts lower ≤
      chargedCost counts upper := by
  unfold chargedCost
  exact
    Nat.add_le_add
      (Nat.mul_le_mul_left
        counts.syntaxUnits
        bounded.syntaxLe)
      (Nat.add_le_add
        (Nat.mul_le_mul_left
          counts.frontierSlots
          bounded.frontierLe)
        (Nat.add_le_add
          (Nat.mul_le_mul_left
            counts.provenanceUnits
            bounded.provenanceLe)
          (Nat.add_le_add
            (Nat.mul_le_mul_left
              counts.certificateAtoms
              bounded.certificateLe)
            (Nat.add_le_add
              (Nat.mul_le_mul_left
                counts.relationFindCalls
                bounded.relationLe)
              (Nat.add_le_add
                (Nat.mul_le_mul_left
                  counts.closurePrimitiveQueries
                  bounded.closurePrimitiveLe)
                (Nat.add_le_add
                  (Nat.mul_le_mul_left
                    counts.closureCompositionCandidates
                    bounded.closureCandidateLe)
                  (Nat.mul_le_mul_left
                    counts.terminalChecks
                    bounded.terminalLe)))))))

/-- A separately declared machine-level atomic-cost assignment. -/
structure MachineCostModel where
  atomic : AtomicCosts

/--
Affine envelope converting one representation-level atomic charge into a
candidate machine-level upper bound.
-/
def affineAtomicEnvelope
    (representation : AtomicCosts)
    (factor overhead : Nat) : AtomicCosts :=
  { syntaxUnit :=
      factor * representation.syntaxUnit + overhead
    frontierSlot :=
      factor * representation.frontierSlot + overhead
    provenanceUnit :=
      factor * representation.provenanceUnit + overhead
    certificateAtom :=
      factor * representation.certificateAtom + overhead
    relationFindCall :=
      factor * representation.relationFindCall + overhead
    closurePrimitiveQuery :=
      factor * representation.closurePrimitiveQuery + overhead
    closureCompositionCandidate :=
      factor * representation.closureCompositionCandidate + overhead
    terminalCheck :=
      factor * representation.terminalCheck + overhead }

/--
Explicit proof obligation connecting a representation model to one machine
model.  The factor and overhead are declared parameters, not inferred facts.
-/
structure RepresentationMachineBridge
    (representation : AtomicCosts)
    (machine : MachineCostModel)
    (factor overhead : Nat) : Prop where
  machineLeEnvelope :
    AtomicCostPointwiseLe
      machine.atomic
      (affineAtomicEnvelope
        representation
        factor
        overhead)

/-- Aggregate cost charged by a separately declared machine model. -/
def machineChargedCost
    (counts : ComplexityCounts)
    (machine : MachineCostModel) : Nat :=
  chargedCost counts machine.atomic

/-- Aggregate machine envelope derived from representation charges and calibration. -/
def representationCalibratedMachineBudget
    (counts : ComplexityCounts)
    (representation : AtomicCosts)
    (factor overhead : Nat) : Nat :=
  chargedCost
    counts
    (affineAtomicEnvelope
      representation
      factor
      overhead)

/--
A machine-cost bound follows only after the representation-to-machine bridge is
proved.
-/
theorem machineChargedCost_le_calibrated
    (counts : ComplexityCounts)
    (representation : AtomicCosts)
    (machine : MachineCostModel)
    (factor overhead : Nat)
    (bridge :
      RepresentationMachineBridge
        representation
        machine
        factor
        overhead) :
    machineChargedCost counts machine ≤
      representationCalibratedMachineBudget
        counts
        representation
        factor
        overhead := by
  exact
    chargedCost_mono
      counts
      machine.atomic
      (affineAtomicEnvelope
        representation
        factor
        overhead)
      bridge.machineLeEnvelope

/-- Identity pointwise domination. -/
theorem atomicCostPointwiseLe_refl
    (costs : AtomicCosts) :
    AtomicCostPointwiseLe costs costs :=
  { syntaxLe := Nat.le_refl _
    frontierLe := Nat.le_refl _
    provenanceLe := Nat.le_refl _
    certificateLe := Nat.le_refl _
    relationLe := Nat.le_refl _
    closurePrimitiveLe := Nat.le_refl _
    closureCandidateLe := Nat.le_refl _
    terminalLe := Nat.le_refl _ }

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.AtomicCostPointwiseLe
#print axioms ConstitutiveSearch.chargedCost_mono
#print axioms ConstitutiveSearch.MachineCostModel
#print axioms ConstitutiveSearch.affineAtomicEnvelope
#print axioms ConstitutiveSearch.RepresentationMachineBridge
#print axioms ConstitutiveSearch.machineChargedCost
#print axioms ConstitutiveSearch.representationCalibratedMachineBudget
#print axioms ConstitutiveSearch.machineChargedCost_le_calibrated
#print axioms ConstitutiveSearch.atomicCostPointwiseLe_refl
/- AXIOM_AUDIT_END -/
