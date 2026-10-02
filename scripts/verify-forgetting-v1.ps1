$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$reportPath = Join-Path $projectRoot 'docs/verification-forgetting-v1.json'
$migrationReportPath = Join-Path $projectRoot 'Migration/verification-forgetting-v1.json'
$referencePaths = @('docs/verification-result.json','Migration/verification-result.json')
$references = @($referencePaths | ForEach-Object {
  $path = Join-Path $projectRoot $_
  $receipt = Get-Content -LiteralPath $path -Raw | ConvertFrom-Json
  if ($receipt.status -ne 'PASSED') { throw "Acquired reference receipt is not PASSED: $_" }
  [ordered]@{ path=$_; sha256=(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash; checkedAtUtc=$receipt.checkedAtUtc }
})
$report = [ordered]@{
  status='RUNNING'; protocol='native-forgetting-v1'; checkedAtUtc=[DateTime]::UtcNow.ToString('o')
  scope='Finite independently admitted native observe/act/reuse suffixes; typed live references and new evaluations'
  referenceReceipts=$references; sourceFiles=0; axiomAudit=''; reducedExecution=''; forgettingExecution=''
  existingExpectedFailures=0; forgettingExpectedFailures=0; expectedFailures=0; totalExpectedFailures=0
}
$report | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $reportPath -Encoding utf8

function Assert-ReferenceReceipts {
  foreach ($entry in $references) {
    $actual = (Get-FileHash -LiteralPath (Join-Path $projectRoot $entry.path) -Algorithm SHA256).Hash
    if ($actual -ne $entry.sha256) { throw "Reference receipt changed: $($entry.path)" }
  }
}

Push-Location $projectRoot
try {
  # Full current foundation and migration checks, with distinct output paths.
  # The original repository can be used by other agents independently.
  $baseOutput = @(& pwsh -NoProfile -File scripts/verify.ps1 -SkipComparison -SkipReference `
    -ReportPath $reportPath -MigrationReportPath $migrationReportPath -LogTag 'forgetting-v1' 2>&1)
  $baseExit = $LASTEXITCODE
  $baseOutput | Set-Content -LiteralPath '.lake/protocol-forgetting-v1.log' -Encoding utf8
  if ($baseExit -ne 0) { throw 'Foundation or migration checks failed; see .lake/protocol-forgetting-v1.log' }
  $base = Get-Content -LiteralPath $reportPath -Raw | ConvertFrom-Json -AsHashtable
  if ($base.status -ne 'PASSED') { throw 'Missing complete base verification receipt' }
  foreach ($key in $base.Keys) { $report[$key] = $base[$key] }
  $report.status = 'RUNNING'
  $report.existingExpectedFailures = $base.expectedFailures
  $report.checkedAtUtc = [DateTime]::UtcNow.ToString('o')
  $report | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $reportPath -Encoding utf8

  $audit = @(& lake env lean scripts/AuditForgettingV1.lean 2>&1)
  if ($LASTEXITCODE -ne 0 -or ($audit -join "`n") -notmatch 'FORGETTING_EXECUTION_V1_OK:') {
    throw "V1 executable dependency audit failed: $($audit -join ' ')"
  }
  $report.forgettingExecution = ($audit -join "`n").Trim()

  $fixtureRoot = Join-Path $projectRoot 'Tests/ExpectedFailures/NativeForgettingV1'
  $fixtures = @(Get-ChildItem -LiteralPath $fixtureRoot -File -Filter '*.lean.fail')
  $manifest = @('ForgottenGlobalIdentityV1.lean.fail','ForgottenReorderedInputsV1.lean.fail','ForgottenWrongSortV1.lean.fail')
  if (@(Compare-Object ($manifest | Sort-Object) ($fixtures.Name | Sort-Object)).Count -ne 0) {
    throw 'V1 expected-failure catalogue differs from its explicit manifest'
  }
  $failureRoot = Join-Path $projectRoot '.lake/expected-failures-forgetting-v1'
  New-Item -ItemType Directory -Path $failureRoot -Force | Out-Null
  foreach ($fixture in $fixtures) {
    $target = Join-Path $failureRoot $fixture.Name.Substring(0,$fixture.Name.Length - 5)
    Copy-Item -LiteralPath $fixture.FullName -Destination $target
    $failure = @(& lake env lean $target 2>&1)
    $failureExit = $LASTEXITCODE
    $failure | Set-Content -LiteralPath ($target + '.log') -Encoding utf8
    if ($failureExit -eq 0 -or ($failure -join "`n") -notmatch 'Type mismatch|Application type mismatch') {
      throw "V1 fixture did not fail in the required way: $($fixture.Name): $($failure -join ' ')"
    }
    $report.forgettingExpectedFailures++
  }
  $report.expectedFailures = $report.existingExpectedFailures + $report.forgettingExpectedFailures
  $migration = Get-Content -LiteralPath $migrationReportPath -Raw | ConvertFrom-Json -AsHashtable
  if ($migration.status -ne 'PASSED') { throw 'Missing migration success receipt' }
  $report.totalExpectedFailures = $report.expectedFailures + $migration.expectedFailures
  Assert-ReferenceReceipts
  $migration['protocol'] = 'native-forgetting-v1'
  $migration | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $migrationReportPath -Encoding utf8
  $report['referenceReceiptsUnchanged'] = $true
  $report.status = 'PASSED'
  $report.checkedAtUtc = [DateTime]::UtcNow.ToString('o')
  $report | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $reportPath -Encoding utf8
  $report | ConvertTo-Json -Depth 8
} catch {
  $report.status = 'FAILED'
  $report['error'] = $_.Exception.Message
  $report | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $reportPath -Encoding utf8
  throw
} finally {
  Assert-ReferenceReceipts
  Pop-Location
}
