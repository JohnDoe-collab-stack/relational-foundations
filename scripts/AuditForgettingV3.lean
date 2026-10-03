import Lean
import Tests.FoundationTests

open Lean Elab Command

def auditScalarDependenciesV3 (memory : Name) (roots : Array Name) (label : String) : CommandElabM Unit := do
  let env ← getEnv
  let some structureInfo := getStructureInfo? env memory | throwError "Missing memory"
  unless structureInfo.fieldNames == #[`position, `active] do
    throwError "Scalar memory must contain exactly position and active"
  for field in structureInfo.fieldNames do
    let some constant := env.find? (memory ++ field) | throwError "Missing field {field}"
    match constant.type with
    | .forallE _ (.const actual _) (.const `Nat _) _ =>
        unless actual == memory do throwError "Unexpected memory field domain"
    | other => throwError "Scalar field is not a scalar natural: {other}"
  let forbidden := #[
    "RelationalFoundations.History",
    "RelationalFoundations.TypedResources.Support",
    "RelationalFoundations.TypedResources.Extension",
    "RelationalFoundations.HeterogeneousFeedback.Frame",
    "RelationalFoundations.HeterogeneousFeedback.At",
    "RelationalFoundations.HeterogeneousFeedback.Focus",
    "RelationalFoundations.HeterogeneousFeedback.run",
    "RelationalFoundations.HeterogeneousFeedback.advance",
    "RelationalFoundations.HeterogeneousFeedback.visible",
    "RelationalFoundations.HeterogeneousFeedback.initial",
    "RelationalFoundations.ReducedHeterogeneous.Memory",
    "RelationalFoundations.ReducedHeterogeneous.Kernel",
    "RelationalFoundations.ReducedHeterogeneous.reconstruct",
    "RelationalFoundations.ReducedHeterogeneous.inflate",
    "RelationalFoundations.ReducedHeterogeneous.trajectory",
    "RelationalFoundations.NativeForgettingV1.forget",
    "RelationalFoundations.NativeForgettingV1.erase",
    "RelationalFoundations.NativeForgettingV1.Matches",
    "RelationalFoundations.NativeForgettingV1.frontierFor"]
  let mut queue := roots
  let mut visited : NameSet := {}
  let mut cursor := 0
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    if visited.contains name then continue
    visited := visited.insert name
    for banned in forbidden do
      -- Shared generic matchers are checked by their complete type and body.
      if name.toString == banned ||
          (name.toString.startsWith (banned ++ ".") && !name.toString.startsWith (banned ++ ".match_")) then
        throwError "Syntactic dependencies retain historical material: {name}"
    let some info := env.find? name | throwError "Missing dependency {name}"
    queue := queue ++ info.type.getUsedConstants
    if let .defnInfo data := info then
      queue := queue ++ data.value.getUsedConstants
  logInfo m!"{label}: {roots.size} roots; {visited.size} type/body dependencies; two Nat fields; forbidden-name scan only"

elab "#audit_scalar_v3 " memory:ident " [" roots:ident,* "] " label:str : command => do
  auditScalarDependenciesV3 memory.getId (roots.getElems.map (fun root => root.getId)) label.getString

#audit_scalar_v3 RelationalFoundations.NativeForgettingV1.Memory [RelationalFoundations.NativeForgettingV1.Memory,
    RelationalFoundations.NativeForgettingV1.Memory.mk,
    RelationalFoundations.NativeForgettingV1.Production,
    RelationalFoundations.NativeForgettingV1.Production.mk,
    RelationalFoundations.NativeForgettingV1.Observation,
    RelationalFoundations.NativeForgettingV1.Observation.mk,
    RelationalFoundations.NativeForgettingV1.initial,
    RelationalFoundations.NativeForgettingV1.view,
    RelationalFoundations.NativeForgettingV1.Context,
    RelationalFoundations.NativeForgettingV1.read,
    RelationalFoundations.NativeForgettingV1.operation,
    RelationalFoundations.NativeForgettingV1.produce,
    RelationalFoundations.NativeForgettingV1.target,
    RelationalFoundations.NativeForgettingV1.step,
    RelationalFoundations.NativeForgettingV1.event,
    RelationalFoundations.NativeForgettingV1.coordinate,
    RelationalFoundations.NativeForgettingV1.observation,
    RelationalFoundations.NativeForgettingV1.certify,
    RelationalFoundations.NativeForgettingV1.outputRead,
    RelationalFoundations.NativeForgettingV1.sweep,
    RelationalFoundations.NativeForgettingV1.run,
    RelationalFoundations.NativeForgettingV1.tick] "FORGETTING_V3_SYNTAX_OK"
#audit_scalar_v3 RelationalFoundations.HiddenEncodingTests.HMem [
  RelationalFoundations.HiddenEncodingTests.HMem,
  RelationalFoundations.HiddenEncodingTests.HMem.mk,
  RelationalFoundations.HiddenEncodingTests.half,
  RelationalFoundations.HiddenEncodingTests.strip,
  RelationalFoundations.HiddenEncodingTests.enc,
  RelationalFoundations.HiddenEncodingTests.decO,
  RelationalFoundations.HiddenEncodingTests.decA,
  RelationalFoundations.HiddenEncodingTests.toV1,
  RelationalFoundations.HiddenEncodingTests.hinit,
  RelationalFoundations.HiddenEncodingTests.hstep,
  RelationalFoundations.HiddenEncodingTests.hrun] "HIDDEN_ENCODING_SYNTAX_ACCEPTED"

elab "#semantic_witnesses_v3" : command => do
  let roots := #[
    `RelationalFoundations.NativeForgettingV1.same_erased,
    `RelationalFoundations.NativeForgettingV1.origin_irrecoverable_from_prefixes,
    `RelationalFoundations.NativeForgettingContract.first_decision_irrecoverable,
    `RelationalFoundations.NativeForgettingV1.forgetting_all_admissible,
    `RelationalFoundations.HeterogeneousInvariants.constructed_then_forgotten,
    `RelationalFoundations.HiddenEncodingTests.hidden_origin_recoverable,
    `RelationalFoundations.HiddenEncodingTests.hidden_separating_horizon]
  for root in roots do
    let axioms ← Lean.collectAxioms root
    unless axioms.isEmpty do throwError "Semantic witness uses axioms: {root}: {axioms}"
  logInfo m!"FORGETTING_V3_SEMANTIC_WITNESSES_OK: {roots.size} axiom-free declarations; two actual prefixes collide, their origin and first decision are irrecoverable; hidden encoding retains its origin"

#semantic_witnesses_v3

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.NativeForgettingV1.origin_irrecoverable_from_prefixes
#print axioms RelationalFoundations.NativeForgettingContract.first_decision_irrecoverable
#print axioms RelationalFoundations.HiddenEncodingTests.hidden_origin_recoverable
/- AXIOM_AUDIT_END -/
