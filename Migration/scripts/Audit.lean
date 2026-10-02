import Lean
import RelationalPerimeter

open Lean Elab Command

elab "#audit_foundations" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut failures : Array MessageData := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      let modText := mod.toString
      if modText.startsWith "Constitution." then
        let axioms ← collectAxioms name
        unless axioms.isEmpty do
          failures := failures.push m!"Foundation declaration {name} depends on axioms {axioms}"
        count := count + 1
  if count == 0 then throwError "Audit found no foundation declarations"
  unless failures.isEmpty do throwError "{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"CONSTITUTION_AUDIT_OK: {count} declarations, zero axiom dependencies"

#audit_foundations

elab "#audit_recent_computation" : command => do
  let modules := #[
    "RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableRelationalExecution",
    "RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableOutputComposition",
    "RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.AdaptiveRelationalExecution",
    "RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.UnboundedMixedExecution",
    "RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparation",
    "RelationalPerimeter.Computation.EndogenousOperationalDecomposition"]
  let env ← getEnv
  let mut count : Nat := 0
  let mut visited : Array String := #[]
  let mut failures : Array MessageData := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modText := env.header.moduleNames[idx.toNat]!.toString
      if modules.contains modText then
        unless visited.contains modText do visited := visited.push modText
        let axioms ← collectAxioms name
        unless axioms.isEmpty do
          failures := failures.push m!"Computation declaration {name} depends on axioms {axioms}"
        count := count + 1
  unless visited.size == modules.size do
    throwError "Recent computation audit did not visit all six modules"
  unless failures.isEmpty do throwError "{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"RECENT_COMPUTATION_AUDIT_OK: {count} declarations across {visited.size} modules, zero axiom dependencies"

#audit_recent_computation
