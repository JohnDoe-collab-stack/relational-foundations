import RelationalPerimeter.Computation.ConstitutiveSearch.TransportCode
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyProvenance

/-!
# Transport-certificate size for the explicit stacked SAT family

The local absorption used by the symmetric trajectory is encoded as one
primitive transport-code atom.

This module deliberately measures certificate syntax, not serialized Lean proof
terms and not the cost of checking source/target formula equalities.  Those
verification costs remain a separate algorithmic layer.
-/

namespace ConstitutiveSearch
namespace SAT

/--
One primitive global flip witness with the selected variable stored explicitly.

Packaging the variable inside the generator gives one uniform generator family
across different trajectory levels.
-/
structure GeneratedStructuralFlipWitness
    {rootFormula : Cnf}
    (source target : GeneratedStructuralBranchContext rootFormula) where
  var : Var
  relation :
    GeneratedStructuralFlipAtRelation
      var
      source
      target

namespace GeneratedStructuralFlipWitness

/-- Interpret one packaged flip witness as a hardened total transport. -/
def toAcceptingTransport
    {rootFormula : Cnf}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (witness :
      GeneratedStructuralFlipWitness source target) :
    AcceptingContinuationTransport
      (generatedStructuralBranchSystem rootFormula)
      source
      target :=
  witness.relation.toAcceptingTransport

end GeneratedStructuralFlipWitness

/-- Hardened action for packaged primitive flip witnesses. -/
def generatedStructuralFlipWitnessAction
    (rootFormula : Cnf) :
    AcceptedRelationalAction
      (generatedStructuralBranchSystem rootFormula)
      (GeneratedStructuralFlipWitness
        (rootFormula := rootFormula)) :=
  { toTransport := fun witness =>
      witness.toAcceptingTransport }

/-- Package the exact sibling flip witness used by one symmetric split. -/
def flipSymmetricSiblingWitness
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    GeneratedStructuralFlipWitness
      (GeneratedStructuralBranchContext.child
        parent var false fresh)
      (GeneratedStructuralBranchContext.child
        parent var true fresh) :=
  { var := var
    relation :=
      flipSymmetricSiblingRelation
        parent
        var
        fresh
        symmetric }

/-- One local sibling absorption has a one-atom transport code. -/
def flipSymmetricSiblingCode
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    TransportCode
      (GeneratedStructuralFlipWitness
        (rootFormula := rootFormula))
      (GeneratedStructuralBranchContext.child
        parent var false fresh)
      (GeneratedStructuralBranchContext.child
        parent var true fresh) :=
  .atom
    (flipSymmetricSiblingWitness
      parent
      var
      fresh
      symmetric)

/-- Every local sibling certificate contains exactly one primitive atom. -/
theorem flipSymmetricSiblingCode_size
    {rootFormula : Cnf}
    (parent : GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt parent.context.formula var) :
    (flipSymmetricSiblingCode
      parent var fresh symmetric).size = 1 := by
  rfl

namespace FlipSymmetricTrajectory

/--
Total number of primitive transport atoms explicitly used along the complete
trajectory.
-/
def transportCertificateAtomCount
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat} :
    FlipSymmetricTrajectory start finish length →
      Nat
  | .done _ =>
      0
  | .step var fresh symmetric tail =>
      (flipSymmetricSiblingCode
        _
        var
        fresh
        symmetric).size +
          tail.transportCertificateAtomCount

/-- Exactly one primitive transport atom is used per trajectory level. -/
theorem transportCertificateAtomCount_eq_index
    {rootFormula : Cnf}
    {start finish : GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.transportCertificateAtomCount =
      length := by
  induction trajectory with
  | done state =>
      rfl
  | @step parent finish length var fresh symmetric tail inductionHypothesis =>
      have localSize :
          (flipSymmetricSiblingCode
            parent
            var
            fresh
            symmetric).size = 1 :=
        flipSymmetricSiblingCode_size
          parent
          var
          fresh
          symmetric
      calc
        (FlipSymmetricTrajectory.step
          var fresh symmetric tail).transportCertificateAtomCount
            =
          (flipSymmetricSiblingCode
            parent var fresh symmetric).size +
              tail.transportCertificateAtomCount :=
            rfl
        _ =
          1 + tail.transportCertificateAtomCount :=
            congrArg
              (fun value =>
                value +
                  tail.transportCertificateAtomCount)
              localSize
        _ =
          1 + length :=
            congrArg
              (Nat.add 1)
              inductionHypothesis
        _ =
          length + 1 :=
            Nat.add_comm 1 length

end FlipSymmetricTrajectory

/-- The closed family uses exactly n primitive flip-certificate atoms. -/
theorem explicitFamilyTransportCertificateAtomCount
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).trajectory.transportCertificateAtomCount =
      count :=
  FlipSymmetricTrajectory.transportCertificateAtomCount_eq_index
    (explicitFamilyResourceTrajectory count).trajectory

/--
Bundle the two now-certified representation measures for the explicit family:
provenance decisions and primitive transport-code atoms.
-/
structure ExplicitFamilyCertificateSizes
    (count : Nat) : Prop where
  provenanceDecisions :
    (explicitFamilyResourceTrajectory count).finish.context.decisions.length =
      count
  transportAtoms :
    (explicitFamilyResourceTrajectory count).trajectory.transportCertificateAtomCount =
      count

/-- Exact certificate-size bundle for F(n). -/
theorem explicitFamilyCertificateSizes
    (count : Nat) :
    ExplicitFamilyCertificateSizes count :=
  { provenanceDecisions :=
      explicitFamilyEndpoint_decisions_length count
    transportAtoms :=
      explicitFamilyTransportCertificateAtomCount count }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipWitness
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipWitness.toAcceptingTransport
#print axioms ConstitutiveSearch.SAT.generatedStructuralFlipWitnessAction
#print axioms ConstitutiveSearch.SAT.flipSymmetricSiblingWitness
#print axioms ConstitutiveSearch.SAT.flipSymmetricSiblingCode
#print axioms ConstitutiveSearch.SAT.flipSymmetricSiblingCode_size
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.transportCertificateAtomCount
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.transportCertificateAtomCount_eq_index
#print axioms ConstitutiveSearch.SAT.explicitFamilyTransportCertificateAtomCount
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyCertificateSizes
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateSizes
/- AXIOM_AUDIT_END -/
