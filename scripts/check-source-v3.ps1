$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'LeanSource.ps1')
$audited = @('RelationalFoundations.lean','Tests/FoundationTests.lean',
  'RelationalFoundations/DependencyPaths.lean','RelationalFoundations/FiniteRuleScope.lean',
  'RelationalFoundations/HeterogeneousInvariants.lean','RelationalFoundations/NativeForgettingContract.lean',
  'RelationalFoundations/TypedResourceOrder.lean','RelationalFoundations/ReducedContinuation.lean',
  'RelationalFoundations/ReducedWeakening.lean','Tests/CyclicSupport.lean','Tests/HiddenEncoding.lean',
  'Tests/RuleScope.lean','Tests/AuditCorrections.lean','scripts/AuditForgettingV3.lean')
foreach ($path in $audited) {
  $text = Get-Content -LiteralPath (Join-Path $root $path) -Raw
  if ([regex]::Matches($text,'/- AXIOM_AUDIT_BEGIN -/').Count -ne 1 -or
      [regex]::Matches($text,'/- AXIOM_AUDIT_END -/').Count -ne 1 -or
      $text.TrimEnd() -notmatch '/- AXIOM_AUDIT_END -/$') { throw "Terminal audit block differs: $path" }
}
$files = @(Get-ChildItem -LiteralPath $root -Recurse -File -Filter '*.lean' | Where-Object {
  $_.FullName.Replace('\','/') -notmatch '/(\.lake|reference)/'
})
foreach ($file in $files) {
  if ((Get-Content -LiteralPath $file.FullName -Raw) -cmatch '\bnoncomputable\b') {
    throw "Forbidden marker in $($file.FullName)"
  }
}
"SOURCE_V3_OK: $($audited.Count) terminal audit blocks; $($files.Count) Lean sources scanned"
