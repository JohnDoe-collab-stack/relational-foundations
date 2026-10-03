import Lean
import RelationalPerimeter
import Tests.CertifiedGrouping

open Lean Elab Command

elab "#audit_foundations" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut generated : Array MessageData := #[]
  let mut failures : Array MessageData := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      let modText := mod.toString
      if modText == "RelationalPerimeter" || modText.startsWith "RelationalPerimeter." || modText.startsWith "Constitution." || modText.startsWith "Tests." || modText == "SegmentedResidualRole" || modText == "AbstractSegmentedTurning" || modText == "ExactTypeTransport" || modText == "StrongPerimetralTurning" then
        let axioms ← collectAxioms name
        unless axioms.isEmpty do
          let text := name.toString
          let legacy := modText.startsWith "RelationalPerimeter.Computation." &&
            !(modText.endsWith ".CertifiedRoleGrouping" || modText.endsWith ".HistoricalRoleGrouping" ||
              modText.endsWith ".RoleGroupingSemantics")
          let auxiliary := text.endsWith ".injEq" || text.endsWith ".congr_simp" ||
            text.endsWith ".eq_def" || text.contains "instRepr"
          if legacy && auxiliary then
            generated := generated.push m!"LEGACY_GENERATED_METADATA: {name}; dependencies {axioms}"
          else
            failures := failures.push m!"Mathematical declaration {name} depends on axioms {axioms}"
        count := count + 1
  if count == 0 then throwError "Audit found no foundation declarations"
  unless failures.isEmpty do throwError "{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"{MessageData.joinSep generated.toList "\n"}"
  logInfo m!"GROUPING_V5_MIGRATION_AUDIT_OK: {count - generated.size} mathematical declarations, zero axiom dependencies; {generated.size} legacy compiler metadata declarations inventoried separately"

#audit_foundations

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normal_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.every_normalizing_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.obligation_composes
/- AXIOM_AUDIT_END -/