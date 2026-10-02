$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'ValidationManifestV2.ps1')
$reportPath = Join-Path $projectRoot 'docs/verification-forgetting-v2.json'
$migrationReportPath = Join-Path $projectRoot 'Migration/verification-forgetting-v2.json'
$manifestRelative = 'docs/manifest-forgetting-v2.json'
$manifestPath = Join-Path $projectRoot $manifestRelative
$basePath = Join-Path $projectRoot '.lake/verification-base-forgetting-v2.json'
$migrationBasePath = Join-Path $projectRoot '.lake/verification-migration-base-forgetting-v2.json'
$report = [ordered]@{
  status='RUNNING'; protocol='native-forgetting-validation-v2'; mathematicalProtocol='native-forgetting-v1'
  checkedAtUtc=[DateTime]::UtcNow.ToString('o'); scope='Finite independently admitted native observe/act/reuse suffixes'
  inputsVerifiedBefore=$false; inputsVerifiedAfter=$false; integrityTests=''; sourceFiles=0
  axiomAudit=''; reducedExecution=''; forgettingExecution=''; expectedFailures=0; totalExpectedFailures=0
  referenceReceipts=@(); validationSteps=@()
}
$steps = [Collections.Generic.List[object]]::new()
$manifest = $null

function Add-ValidationStepV2 {
  param([string]$Name, [string]$File, [string[]]$Arguments, [int]$ExitCode, [string]$LogPath, [string]$ExpectedExit)
  $steps.Add([ordered]@{
    name=$Name; file=$File; arguments=$Arguments; exitCode=$ExitCode; expectedExit=$ExpectedExit
    completedAtUtc=[DateTime]::UtcNow.ToString('o'); outputSha256=(Get-FileHash -LiteralPath $LogPath -Algorithm SHA256).Hash
  })
}

Push-Location $projectRoot
$priorLeanPath = $env:LEAN_PATH
try {
  $env:LEAN_PATH = $null
  $inputs = @(Get-ValidationInputsV2 $projectRoot)
  $manifest = New-InputManifestV2 $projectRoot $inputs
  $head = (& git rev-parse HEAD).Trim()
  if ($LASTEXITCODE -ne 0) { throw 'Cannot identify current Git revision' }
  $branch = (& git branch --show-current).Trim()
  if ($LASTEXITCODE -ne 0) { throw 'Cannot identify current Git branch' }
  $manifest['git'] = [ordered]@{ head=$head; branch=$branch; sourcesIdentifiedBy='Per-file bytes and SHA256, including uncommitted files' }
  $manifest['toolchain'] = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
  $manifest | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $manifestPath -Encoding utf8
  $report['inputManifest'] = [ordered]@{
    path=$manifestRelative; sha256=(Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash; fileCount=$manifest.fileCount
  }
  $report.referenceReceipts = @($manifest.files | Where-Object { $_.role -eq 'reference-receipt' } | ForEach-Object {
    $previous = Get-Content -LiteralPath (Resolve-ValidationFileV2 $projectRoot $_.path) -Raw | ConvertFrom-Json -AsHashtable
    if ($previous.status -cne 'PASSED') { throw "Prior receipt is not PASSED: $($_.path)" }
    [ordered]@{ path=$_.path; sha256=$_.sha256; checkedAtUtc=$previous.checkedAtUtc }
  })
  Assert-InputManifestV2 $projectRoot $manifest @(Get-ValidationInputsV2 $projectRoot)
  $report.inputsVerifiedBefore = $true
  $report | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $reportPath -Encoding utf8

  $integrityOutput = @(& pwsh -NoProfile -File scripts/test-validation-manifest-v2.ps1 2>&1)
  $integrityExit = $LASTEXITCODE
  $integrityLog = '.lake/manifest-tests-forgetting-v2.log'
  $integrityOutput | Set-Content -LiteralPath $integrityLog -Encoding utf8
  Add-ValidationStepV2 'manifest-integrity-tests' 'scripts/test-validation-manifest-v2.ps1' @() $integrityExit $integrityLog 'zero'
  if ($integrityExit -ne 0 -or ($integrityOutput -join "`n") -notmatch 'VALIDATION_MANIFEST_V2_TESTS_OK:') {
    throw "Manifest integrity tests failed: $($integrityOutput -join ' ')"
  }
  $report.integrityTests = ($integrityOutput -join "`n").Trim()

  $baseArguments = @('-SkipComparison','-SkipReference','-ReportPath','.lake/verification-base-forgetting-v2.json',
    '-MigrationReportPath','.lake/verification-migration-base-forgetting-v2.json','-LogTag','forgetting-v2')
  $baseOutput = @(& pwsh -NoProfile -File scripts/verify.ps1 @baseArguments 2>&1)
  $baseExit = $LASTEXITCODE
  $baseLog = '.lake/protocol-forgetting-v2.log'
  $baseOutput | Set-Content -LiteralPath $baseLog -Encoding utf8
  Add-ValidationStepV2 'foundation-and-migration' 'scripts/verify.ps1' $baseArguments $baseExit $baseLog 'zero'
  if ($baseExit -ne 0) { throw 'Foundation or migration validation failed; see .lake/protocol-forgetting-v2.log' }
  $base = Get-Content -LiteralPath $basePath -Raw | ConvertFrom-Json -AsHashtable
  if ($base.status -cne 'PASSED') { throw 'Missing base success receipt' }
  foreach ($key in $base.Keys) { $report[$key] = $base[$key] }
  $report.status = 'RUNNING'
  $report['existingExpectedFailures'] = $base.expectedFailures
  $report['forgettingExpectedFailures'] = 0

  $audit = @(& lake env lean scripts/AuditForgettingV1.lean 2>&1)
  $auditExit = $LASTEXITCODE
  $auditLog = '.lake/executable-audit-forgetting-v2.log'
  $audit | Set-Content -LiteralPath $auditLog -Encoding utf8
  Add-ValidationStepV2 'forgetting-executable-audit' 'scripts/AuditForgettingV1.lean' @('lake','env','lean') $auditExit $auditLog 'zero'
  if ($auditExit -ne 0 -or ($audit -join "`n") -notmatch 'FORGETTING_EXECUTION_V1_OK:') {
    throw "Executable dependency audit failed: $($audit -join ' ')"
  }
  $report.forgettingExecution = ($audit -join "`n").Trim()

  $fixtureDirectory = 'Tests/ExpectedFailures/NativeForgettingV1'
  $fixtureNames = @('ForgottenGlobalIdentityV1.lean.fail','ForgottenReorderedInputsV1.lean.fail','ForgottenWrongSortV1.lean.fail')
  $actualFixtures = @(Get-ChildItem -LiteralPath $fixtureDirectory -File -Filter '*.lean.fail')
  if (@(Compare-Object ($fixtureNames | Sort-Object) ($actualFixtures.Name | Sort-Object)).Count) {
    throw 'Native forgetting rejection catalogue differs'
  }
  $failureRoot = '.lake/expected-failures-forgetting-v2'
  New-Item -ItemType Directory -Path $failureRoot -Force | Out-Null
  foreach ($name in $fixtureNames) {
    $fixturePath = "$fixtureDirectory/$name"
    $target = Join-Path $failureRoot $name.Substring(0,$name.Length - 5)
    Copy-Item -LiteralPath $fixturePath -Destination $target
    $failure = @(& lake env lean $target 2>&1)
    $failureExit = $LASTEXITCODE
    $failureLog = $target + '.log'
    $failure | Set-Content -LiteralPath $failureLog -Encoding utf8
    Add-ValidationStepV2 $name $fixturePath @('lake','env','lean',$target) $failureExit $failureLog 'nonzero-type-mismatch'
    if ($failureExit -eq 0 -or ($failure -join "`n") -notmatch 'Type mismatch|Application type mismatch') {
      throw "Native forgetting rejection failed: $name"
    }
    $report.forgettingExpectedFailures++
  }
  $report.expectedFailures = $report.existingExpectedFailures + $report.forgettingExpectedFailures
  $migration = Get-Content -LiteralPath $migrationBasePath -Raw | ConvertFrom-Json -AsHashtable
  if ($migration.status -cne 'PASSED') { throw 'Migration success receipt missing' }
  $report.totalExpectedFailures = $report.expectedFailures + $migration.expectedFailures

  $null = Assert-ManifestLinkV2 $projectRoot $report.inputManifest
  Assert-InputManifestV2 $projectRoot $manifest @(Get-ValidationInputsV2 $projectRoot)
  if ((& git rev-parse HEAD).Trim() -cne $head -or (& git branch --show-current).Trim() -cne $branch) {
    throw 'Git revision or branch changed during validation'
  }
  $report.inputsVerifiedAfter = $true
  $migration['protocol'] = 'native-forgetting-validation-v2'
  $migration['mathematicalProtocol'] = 'native-forgetting-v1'
  $migration['inputManifest'] = $report.inputManifest
  $migration | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $migrationReportPath -Encoding utf8
  $report['migrationReceipt'] = [ordered]@{
    path='Migration/verification-forgetting-v2.json'; sha256=(Get-FileHash -LiteralPath $migrationReportPath -Algorithm SHA256).Hash
  }
  $report.validationSteps = @($steps.ToArray())
  $report['reproduce'] = 'pwsh -NoProfile -File scripts/verify-forgetting-v2.ps1'
  $report['checkSavedBundle'] = 'pwsh -NoProfile -File scripts/check-forgetting-v2.ps1'
  $report.status = 'PASSED'
  $report.checkedAtUtc = [DateTime]::UtcNow.ToString('o')
  $report | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $reportPath -Encoding utf8
  $bundleOutput = @(& pwsh -NoProfile -File scripts/check-forgetting-v2.ps1 2>&1)
  if ($LASTEXITCODE -ne 0 -or ($bundleOutput -join "`n") -notmatch 'VALIDATION_BUNDLE_V2_OK:') {
    throw "Saved validation bundle check failed: $($bundleOutput -join ' ')"
  }
  $report['bundleCheck'] = ($bundleOutput -join "`n").Trim()
  $report | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $reportPath -Encoding utf8
  $report | ConvertTo-Json -Depth 10
} catch {
  $report.status = 'FAILED'
  $report['error'] = $_.Exception.Message
  $report.validationSteps = @($steps.ToArray())
  $report | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $reportPath -Encoding utf8
  throw
} finally {
  $env:LEAN_PATH = $priorLeanPath
  Pop-Location
}
