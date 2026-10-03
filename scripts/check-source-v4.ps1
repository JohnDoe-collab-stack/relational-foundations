$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'LeanSource.ps1')
$audited = @('RelationalFoundations.lean','Tests/FoundationTests.lean',
  'RelationalFoundations/DependencyPaths.lean','RelationalFoundations/FiniteRuleScope.lean',
  'RelationalFoundations/HeterogeneousInvariants.lean','RelationalFoundations/NativeForgettingContract.lean',
  'RelationalFoundations/TypedResourceOrder.lean','RelationalFoundations/ReducedContinuation.lean',
  'RelationalFoundations/ReducedWeakening.lean','Tests/CyclicSupport.lean','Tests/HiddenEncoding.lean',
  'Tests/RuleScope.lean','Tests/AuditCorrections.lean','scripts/AuditForgettingV4.lean','scripts/AuditReducedV4.lean','Tests/ForgettingAuditScope.lean',
  'RelationalFoundations/FiniteRuleCoordinates.lean','Tests/FiniteRuleCoordinates.lean')
foreach ($path in $audited) {
  $text = Get-Content -LiteralPath (Join-Path $root $path) -Raw
  if ([regex]::Matches($text,'/- AXIOM_AUDIT_BEGIN -/').Count -ne 1 -or
      [regex]::Matches($text,'/- AXIOM_AUDIT_END -/').Count -ne 1 -or
      $text.TrimEnd() -notmatch '/- AXIOM_AUDIT_END -/$') { throw "Terminal audit block differs: $path" }
}
. (Join-Path $PSScriptRoot 'ValidationManifestV4.ps1')
$files = @(Get-ValidationInputsV4 $root | Where-Object { $_.path.EndsWith('.lean',[StringComparison]::Ordinal) } | ForEach-Object {
  Get-Item -LiteralPath (Resolve-ValidationFileV4 $root $_.path) -Force
})
foreach ($file in $files) {
  if ((Get-Content -LiteralPath $file.FullName -Raw) -cmatch '\bnoncomputable\b') {
    throw "Forbidden marker in $($file.FullName)"
  }
}
"SOURCE_V4_OK: $($audited.Count) terminal audit blocks; $($files.Count) Lean sources scanned"
