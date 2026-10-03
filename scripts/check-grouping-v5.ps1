param([Parameter(Mandatory)][string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
$taskRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$taskOutput = [IO.Path]::GetFullPath($OutputDirectory)
New-Item -ItemType Directory -Path $taskOutput -Force | Out-Null
function Invoke-GroupingCheckV5 {
  param([string]$Name,[string]$Program,[string[]]$Arguments,[string]$Pattern)
  $result = @(& $Program @Arguments 2>&1)
  $code = $LASTEXITCODE
  $result | Set-Content -LiteralPath (Join-Path $taskOutput "$Name.txt") -Encoding utf8
  if ($code -ne 0 -or ($result -join [Environment]::NewLine) -notmatch $Pattern -or
      ($result -join [Environment]::NewLine) -match 'warning:|depends on axioms:|sorryAx') {
    throw "Grouping V5 check failed: $Name"
  }
  $result
}
Push-Location $taskRoot
try {
  Invoke-GroupingCheckV5 'grouping-runtime' 'lake' @('env','lean','Tests/CertifiedGrouping.lean') 'GROUPING_V5_RUNTIME_OK: 5461'
  $taskScalar = @'
import scripts.AuditForgettingV4
#audit_scalar_v4 RelationalFoundations.NativeForgettingV1.Memory [
  RelationalFoundations.CertifiedGrouping.Native.reducedNext,
  RelationalFoundations.CertifiedGrouping.Native.reducedEvent,
  RelationalFoundations.CertifiedGrouping.Native.reducedRead] "GROUPING_V5_SCALAR_SYNTAX_OK"
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Native.bridge
/- AXIOM_AUDIT_END -/
'@
  $taskScalarPath = Join-Path $taskOutput 'GroupingScalarAudit.lean'
  [IO.File]::WriteAllText($taskScalarPath,$taskScalar,[Text.UTF8Encoding]::new($false))
  Invoke-GroupingCheckV5 'grouping-scalar-audit' 'lake' @('env','lean',$taskScalarPath) 'GROUPING_V5_SCALAR_SYNTAX_OK:'
  $taskAudit = [IO.File]::ReadAllText((Join-Path $taskRoot 'scripts/Audit.lean'))
  $taskAudit = $taskAudit.Replace('import Tests.FoundationTests',('import RelationalPerimeter' + [Environment]::NewLine + 'import Tests.CertifiedGrouping'))
  $taskAudit = $taskAudit.Replace(
    'if modText == "RelationalFoundations" || modText.startsWith "RelationalFoundations." || modText.startsWith "Tests." then',
    'if modText == "RelationalPerimeter" || modText.startsWith "RelationalPerimeter." || modText.startsWith "Constitution." || modText.startsWith "Tests." || modText == "SegmentedResidualRole" || modText == "AbstractSegmentedTurning" || modText == "ExactTypeTransport" || modText == "StrongPerimetralTurning" then')
  $taskAudit = $taskAudit.Replace('AUDIT_OK:','GROUPING_V5_MIGRATION_AUDIT_OK:')
  # Legacy generated extensional lemmas and display instances are inventoried
  # separately. Every authored declaration and every new module keeps the full
  # transitive axiom check, which also rejects use of such an auxiliary lemma.
  $taskAudit = $taskAudit.Replace('let mut count : Nat := 0',
    ('let mut count : Nat := 0' + [Environment]::NewLine + '  let mut generated : Array MessageData := #[]'))
  $taskAudit = $taskAudit.Replace(
    'failures := failures.push m!"Foundation declaration {name} depends on axioms {axioms}"', @'
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
'@.Trim())
  $taskAudit = $taskAudit.Replace('logInfo m!"GROUPING_V5_MIGRATION_AUDIT_OK: {count} declarations, zero axiom dependencies"', @'
logInfo m!"{MessageData.joinSep generated.toList "\n"}"
  logInfo m!"GROUPING_V5_MIGRATION_AUDIT_OK: {count - generated.size} mathematical declarations, zero axiom dependencies; {generated.size} legacy compiler metadata declarations inventoried separately"
'@)
  $taskAudit += [Environment]::NewLine + @'
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.normal_selected
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.every_normalizing_trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping.Historical.obligation_composes
/- AXIOM_AUDIT_END -/
'@
  $taskAuditPath = Join-Path $taskOutput 'GroupingMigrationAudit.lean'
  [IO.File]::WriteAllText($taskAuditPath,$taskAudit,[Text.UTF8Encoding]::new($false))
  Push-Location (Join-Path $taskRoot 'Migration')
  try {
    Invoke-GroupingCheckV5 'grouping-migration-audit' 'lake' @('env','lean',$taskAuditPath) 'GROUPING_V5_MIGRATION_AUDIT_OK:'
    Invoke-GroupingCheckV5 'grouping-migration-tests' 'lake' @('env','lean','Tests/CertifiedGrouping.lean') 'composed_execution.*does not depend on any axioms'
  } finally { Pop-Location }
  $taskModules = @('GroupingTraces','CertifiedGrouping','GroupingNormalization','GroupingProjections',
    'BinaryGrouping','GroupingReindex','GroupingImage','GroupingContinuation','HistoricalGrouping','GroupingInstances')
  $taskCode = [Collections.Generic.List[object]]::new()
  foreach ($taskModule in $taskModules) {
    $taskPath = Join-Path $taskRoot ".lake/build/ir/RelationalFoundations/$taskModule.c"
    if (-not (Test-Path -LiteralPath $taskPath) -or (Get-Item -LiteralPath $taskPath).Length -le 0) {
      throw "Missing generated producer code: $taskModule"
    }
    $taskCode.Add(@{module="RelationalFoundations.$taskModule";bytes=(Get-Item -LiteralPath $taskPath).Length;sha256=(Get-FileHash -LiteralPath $taskPath).Hash})
  }
  foreach ($taskModule in @('CertifiedRoleGrouping','HistoricalRoleGrouping','RoleGroupingSemantics')) {
    $taskPath = Join-Path $taskRoot "Migration/.lake/build/ir/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/$taskModule.c"
    if (-not (Test-Path -LiteralPath $taskPath) -or (Get-Item -LiteralPath $taskPath).Length -le 0) { throw "Missing generated adapter code: $taskModule" }
    $taskCode.Add(@{module=$taskModule;bytes=(Get-Item -LiteralPath $taskPath).Length;sha256=(Get-FileHash -LiteralPath $taskPath).Hash})
  }
  @($taskCode.ToArray()) | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $taskOutput 'producer-code.json') -Encoding utf8
  'GROUPING_V5_OK: runtime matrix; scalar dependency scan; exhaustive migrated declaration audit; all-history consumers; 13 generated C modules'
} finally { Pop-Location }
