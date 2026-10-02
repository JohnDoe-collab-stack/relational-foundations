import Lean
import Tests.FoundationTests

open Lean Elab Command

elab "#audit_reduced_execution" : command => do
  let env ← getEnv
  for (structureName, expected) in
      #[( `RelationalFoundations.ReducedHeterogeneous.Memory, 3),
        ( `RelationalFoundations.ReducedHeterogeneous.Kernel, 2)] do
    let some info := getStructureInfo? env structureName | throwError "Missing scalar memory {structureName}"
    unless info.fieldNames.size == expected do throwError "Unexpected fields in {structureName}"
    for field in info.fieldNames do
      let fieldName := structureName ++ field
      let some constant := env.find? fieldName | throwError "Missing field {fieldName}"
      match constant.type with
      | .forallE _ _ (.const `Nat _) _ => pure ()
      | other => throwError "Persistent field {fieldName} is not a scalar natural: {other}"
  let roots := #[
    `RelationalFoundations.ReducedHeterogeneous.initial,
    `RelationalFoundations.ReducedHeterogeneous.phaseAt,
    `RelationalFoundations.ReducedHeterogeneous.view,
    `RelationalFoundations.ReducedHeterogeneous.produced,
    `RelationalFoundations.ReducedHeterogeneous.output,
    `RelationalFoundations.ReducedHeterogeneous.nextState,
    `RelationalFoundations.ReducedHeterogeneous.step,
    `RelationalFoundations.ReducedHeterogeneous.event,
    `RelationalFoundations.ReducedHeterogeneous.sweep,
    `RelationalFoundations.ReducedHeterogeneous.run,
    `RelationalFoundations.ReducedHeterogeneous.inflate,
    `RelationalFoundations.ReducedHeterogeneous.Kernel.initial,
    `RelationalFoundations.ReducedHeterogeneous.Kernel.tick]
  let forbidden := #[
    "RelationalFoundations.History",
    "RelationalFoundations.TypedResources.Support",
    "RelationalFoundations.TypedResources.Ref",
    "RelationalFoundations.TypedResources.AnyRef",
    "RelationalFoundations.TypedResources.Operation",
    "RelationalFoundations.HeterogeneousFeedback.Frame",
    "RelationalFoundations.HeterogeneousFeedback.At",
    "RelationalFoundations.HeterogeneousFeedback.run",
    "RelationalFoundations.HeterogeneousFeedback.advance",
    "RelationalFoundations.ReducedHeterogeneous.reconstruct"]
  let mut queue := roots
  let mut visited : NameSet := {}
  let mut cursor := 0
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    if visited.contains name then continue
    visited := visited.insert name
    for banned in forbidden do
      -- Lean shares generic matchers across declarations: the native run's
      -- Nat matcher is just Nat.casesOn. Its body is still traversed below.
      if name.toString == banned ||
          (name.toString.startsWith (banned ++ ".") && !name.toString.startsWith (banned ++ ".match_")) then
        throwError "Reduced executable depends on historical materialization: {name}"
    let some info := env.find? name | throwError "Missing executable declaration {name}"
    if let .defnInfo data := info then
      queue := queue ++ data.value.getUsedConstants
  logInfo m!"REDUCED_EXECUTION_OK: {roots.size} executable roots; {visited.size} dependencies; scalar persistent fields; no history/support/replay dependencies"

#audit_reduced_execution
