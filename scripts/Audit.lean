import Lean
import Tests.FoundationTests

open Lean Elab Command

elab "#audit_foundations" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut failures : Array MessageData := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      let modText := mod.toString
      if modText == "RelationalFoundations" || modText.startsWith "RelationalFoundations." || modText.startsWith "Tests." then
        let axioms ← collectAxioms name
        unless axioms.isEmpty do
          failures := failures.push m!"Foundation declaration {name} depends on axioms {axioms}"
        count := count + 1
  if count == 0 then throwError "Audit found no foundation declarations"
  unless failures.isEmpty do throwError "{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"AUDIT_OK: {count} declarations, zero axiom dependencies"

#audit_foundations
