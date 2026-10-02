import RelationalPerimeter

/-!
# Public-root import gate

This module is a downstream-style build check.  Its presence in the default
Lake target ensures that the public `RelationalPerimeter` module is registered,
built, and importable rather than merely valid when elaborated as a source file.
-/

namespace RelationalPerimeter.Tests.PublicRootImport

open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

def publicEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence

def publicFamily :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family

def publicSuccinctnessEvidence :=
  RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutiveNormalizerSuccinctnessEvidence

theorem publicIndependentAddressingBound
    (input : Nat) (addressing : IndependentProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  independent_profile_addressing_requires_exponential_slots input addressing

theorem publicNormalizerProgramSize (input : Nat) :
    (constitutiveNormalizerSuccinctnessEvidence input).program.program.codeSize =
      input + 1 :=
  constitutive_normalizer_program_code_size_exact input

theorem publicNormalizerMetricAgreement (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  constitutive_normalizer_code_metric_exact input

end RelationalPerimeter.Tests.PublicRootImport

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicFamily
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicSuccinctnessEvidence
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicIndependentAddressingBound
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicNormalizerProgramSize
#print axioms RelationalPerimeter.Tests.PublicRootImport.publicNormalizerMetricAgreement
/- AXIOM_AUDIT_END -/
