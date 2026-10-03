import RelationalFoundations.HeterogeneousInvariants
import RelationalFoundations.NativeForgettingContract
import Tests.CyclicSupport
import Tests.HiddenEncoding
set_option genInjectivity false

namespace RelationalFoundations.AuditCorrectionsTests

def invariantChecks : Bool :=
  (List.range 13).all (fun seed => (List.range 25).all (fun depth =>
    let memory := NativeForgettingV1.run (NativeForgettingV1.initial seed) depth
    memory.active ≤ seed + 1))

def encodingChecks : Bool :=
  (List.range 3).all (fun seed => (List.range 7).all (fun depth =>
    HiddenEncodingTests.decO (HiddenEncodingTests.hrun (HiddenEncodingTests.hinit seed) depth).active == seed))

def checks : Bool :=
  invariantChecks && encodingChecks &&
    ((CyclicSupportTests.loop (1 : Nat) ⟨(), Sum.inr ()⟩).nodes.length == 2) &&
    (NativeForgettingContract.firstDecision 0 == true) &&
    (NativeForgettingContract.firstDecision 2 == false)

#guard checks

end RelationalFoundations.AuditCorrectionsTests

#eval match RelationalFoundations.AuditCorrectionsTests.checks with
  | true => "AUDIT_V3_RUNTIME_OK: 325 value-bound checks; 21 hidden-origin checks; cyclic visits and lost decisions"
  | false => "AUDIT_V3_RUNTIME_FAILED"

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.AuditCorrectionsTests.checks
/- AXIOM_AUDIT_END -/
