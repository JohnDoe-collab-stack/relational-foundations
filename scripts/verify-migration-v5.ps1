param([switch]$SkipBuild, [string]$ReportPath = '.lake/validation-v5-migration.json', [string]$LogTag = '')
$ErrorActionPreference = 'Stop'
$migrationRoot = Join-Path (Resolve-Path (Join-Path $PSScriptRoot '..')).Path 'Migration'
$reportPath = if ([IO.Path]::IsPathRooted($ReportPath)) { $ReportPath } else { Join-Path $migrationRoot $ReportPath }
$buildLog = if ($LogTag) { ".lake/migration-build-$LogTag.log" } else { '.lake/migration-build.log' }
$symbolsLog = if ($LogTag) { ".lake/public-symbols-$LogTag.log" } else { '.lake/public-symbols.log' }
$report = [ordered]@{ status='RUNNING'; checkedAtUtc=[DateTime]::UtcNow.ToString('o'); sources=0; publicSymbols=0; axiomAudit=''; recentComputationAudit=''; publicAudits=0; expectedFailures=0; stratification=''; boundaries='' }
New-Item -ItemType Directory -Path (Join-Path $migrationRoot '.lake') -Force | Out-Null
$report | ConvertTo-Json | Set-Content -LiteralPath $reportPath -Encoding utf8
Push-Location $migrationRoot
$priorLeanPath = $env:LEAN_PATH
try {
  $env:LEAN_PATH = $null
  $sources = @(Get-ChildItem -LiteralPath $migrationRoot -Recurse -Force -File -Filter '*.lean' | Where-Object {
    $_.FullName.Replace('\','/') -notlike '*/.lake/*' -and $_.FullName.Replace('\','/') -notlike '*/scripts/*'
  })
  $report.sources = $sources.Count
  foreach ($source in $sources) {
    $text = Get-Content -LiteralPath $source.FullName -Raw
    if ($text -cmatch '(?m)^\s*(axiom|unsafe)\s|\b(noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b') {
      throw "Forbidden construct: $($source.FullName)"
    }
  }
  if (-not $SkipBuild) {
    $build = @(& lake build 2>&1)
    $buildExit = $LASTEXITCODE
    $build | Set-Content -LiteralPath $buildLog -Encoding utf8
    if ($buildExit -ne 0 -or ($build -join "`n") -match 'warning:|depends on axioms:|sorryAx') {
      throw "Migrated build or public axiom audit failed; see $buildLog"
    }
    $report.publicAudits = [regex]::Matches(($build -join "`n"), 'does not depend on any axioms').Count
  }
  foreach ($source in $sources) {
    $relative = $source.FullName.Substring($migrationRoot.Length + 1)
    $olean = Join-Path '.lake/build/lib/lean' ([IO.Path]::ChangeExtension($relative,'.olean'))
    if (-not (Test-Path -LiteralPath $olean)) { throw "Missing compiled migration source: $relative" }
  }
  $audit = @(& lake env lean scripts/Audit.lean 2>&1)
  if ($LASTEXITCODE -ne 0) { throw ($audit -join "`n") }
  $auditText = $audit -join "`n"
  $foundationReceipt = [regex]::Match($auditText, 'CONSTITUTION_AUDIT_OK: \d+ declarations, zero axiom dependencies')
  $recentReceipt = [regex]::Match($auditText, 'RECENT_COMPUTATION_AUDIT_OK: \d+ declarations across 6 modules, zero axiom dependencies')
  if (-not $foundationReceipt.Success -or -not $recentReceipt.Success) {
    throw 'Migration exhaustive audit receipts missing'
  }
  $report.axiomAudit = $foundationReceipt.Value
  $report.recentComputationAudit = $recentReceipt.Value
  $symbols = @(& lake env lean scripts/CheckPublicSymbols.lean 2>&1)
  $symbolsExit = $LASTEXITCODE
  $symbols | Set-Content -LiteralPath $symbolsLog -Encoding utf8
  if ($symbolsExit -ne 0) { throw "Migration public symbol inventory failed; see $symbolsLog" }
  $report.publicSymbols = @(Import-Csv ../docs/migration-symbols.csv).Count
  & scripts/check-stratification-v5.ps1 --self-test
  if ($LASTEXITCODE -ne 0) { throw 'Migration stratification self-test failed' }
  $report.stratification = (& scripts/check-stratification-v5.ps1 | Out-String).Trim()
  if ($LASTEXITCODE -ne 0) { throw 'Migration stratification failed' }
  & scripts/check-import-boundaries-v3.ps1 --self-test
  if ($LASTEXITCODE -ne 0) { throw 'Migration boundary parser self-test failed' }
  foreach ($manifest in @('import-boundaries.txt','constitutive-normalizer-core-import-boundaries.txt','executed-history-import-boundaries.txt','measured-accounting-import-boundaries.txt')) {
    & scripts/check-import-boundaries-v3.ps1 (Join-Path 'scripts' $manifest)
    if ($LASTEXITCODE -ne 0) { throw "Migration import boundary failed: $manifest" }
  }
  $report.boundaries = 'Four transitive import boundary manifests passed'
  & scripts/check-expected-failures.ps1
  if ($LASTEXITCODE -ne 0) { throw 'Migrated expected-failure gates failed' }
  $report.expectedFailures = @(Get-Content scripts/expected-failures.tsv | Where-Object { $_ -and -not $_.StartsWith('#') }).Count
  $report.status = 'PASSED'
  $report | ConvertTo-Json | Set-Content -LiteralPath $reportPath -Encoding utf8
  $report | ConvertTo-Json
} catch {
  $report.status = 'FAILED'
  $report['error'] = $_.Exception.Message
  $report | ConvertTo-Json | Set-Content -LiteralPath $reportPath -Encoding utf8
  throw
} finally {
  $env:LEAN_PATH = $priorLeanPath
  Pop-Location
}
