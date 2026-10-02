import Lean
import Tests.FoundationTests

open Lean Elab Command

elab "#audit_forgetting_v1" : command => do
  let env ← getEnv
  let memory := `RelationalFoundations.NativeForgettingV1.Memory
  let some structureInfo := getStructureInfo? env memory | throwError "Missing V1 memory"
  unless structureInfo.fieldNames == #[`position, `active] do
    throwError "V1 memory must contain exactly position and active"
  for field in structureInfo.fieldNames do
    let some constant := env.find? (memory ++ field) | throwError "Missing V1 field {field}"
    match constant.type with
    | .forallE _ (.const actual _) (.const `Nat _) _ =>
        unless actual == memory do throwError "Unexpected memory field domain"
    | other => throwError "V1 field is not a scalar natural: {other}"
  let roots := #[
    `RelationalFoundations.NativeForgettingV1.Memory,
    `RelationalFoundations.NativeForgettingV1.Memory.mk,
    `RelationalFoundations.NativeForgettingV1.Production,
    `RelationalFoundations.NativeForgettingV1.Production.mk,
    `RelationalFoundations.NativeForgettingV1.Observation,
    `RelationalFoundations.NativeForgettingV1.Observation.mk,
    `RelationalFoundations.NativeForgettingV1.initial,
    `RelationalFoundations.NativeForgettingV1.view,
    `RelationalFoundations.NativeForgettingV1.Context,
    `RelationalFoundations.NativeForgettingV1.read,
    `RelationalFoundations.NativeForgettingV1.operation,
    `RelationalFoundations.NativeForgettingV1.produce,
    `RelationalFoundations.NativeForgettingV1.target,
    `RelationalFoundations.NativeForgettingV1.step,
    `RelationalFoundations.NativeForgettingV1.event,
    `RelationalFoundations.NativeForgettingV1.coordinate,
    `RelationalFoundations.NativeForgettingV1.observation,
    `RelationalFoundations.NativeForgettingV1.certify,
    `RelationalFoundations.NativeForgettingV1.outputRead,
    `RelationalFoundations.NativeForgettingV1.sweep,
    `RelationalFoundations.NativeForgettingV1.run,
    `RelationalFoundations.NativeForgettingV1.tick]
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
        throwError "V1 executable or its type retains historical material: {name}"
    let some info := env.find? name | throwError "Missing V1 dependency {name}"
    queue := queue ++ info.type.getUsedConstants
    if let .defnInfo data := info then
      queue := queue ++ data.value.getUsedConstants
  logInfo m!"FORGETTING_EXECUTION_V1_OK: {roots.size} executable/data roots; {visited.size} type/body dependencies; exactly two Nat fields; typed frontier and new certificates; no origin/history/support/replay inputs"

#audit_forgetting_v1
