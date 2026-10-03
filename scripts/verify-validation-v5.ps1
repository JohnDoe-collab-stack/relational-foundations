param([string]$OutputDirectory = '', [string]$FrozenManifest = '')
$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'ValidationManifestV5.ps1')
$runId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffZ') + '-' + [guid]::NewGuid().ToString('N').Substring(0,8)
if (-not $OutputDirectory) { $OutputDirectory = Join-Path $root ".lake/validation-v5/$runId" }
$outputRoot = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $outputRoot) { throw 'A V5 run writes a fresh directory; it never replaces prior evidence' }
New-Item -ItemType Directory -Path (Join-Path $outputRoot 'logs') -Force | Out-Null
$receiptPath = Join-Path $outputRoot 'receipt.json'
$steps = [Collections.Generic.List[object]]::new()
$report = [ordered]@{ status='RUNNING'; protocol='foundations-audit-validation-v5';
  startedAtUtc=[DateTime]::UtcNow.ToString('o'); platform=$(if ($IsWindows) { 'Windows' } else { 'Linux' });
  runId=$runId; inputsVerifiedBefore=$false; inputsVerifiedAfter=$false; validationSteps=@();
  parameters=@{ stochasticSeeds=@(); runtimeSeeds='0..12'; runtimeHorizons='0..24'; hiddenEncodingSeeds='0..2';
    hiddenEncodingHorizons='0..6'; groupingDimensions='0..6'; groupingPairs=5461;
    proofScope='All rule states and traces; all finite role histories; all native independently admitted suffixes' } }
function Save-ReceiptV5 {
  $report.validationSteps = @($steps.ToArray())
  $report | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $receiptPath -Encoding utf8
}
function Invoke-GateV5 {
  param([string]$Name,[string]$Source,[string]$Program,[string[]]$Arguments,[string]$ExpectedPattern,
    [string]$ExpectedExit='zero')
  $started = [DateTime]::UtcNow.ToString('o')
  $output = @(& $Program @Arguments 2>&1)
  $code = $LASTEXITCODE
  $logRelative = "logs/$Name.txt"
  $log = Join-Path $outputRoot $logRelative
  $output | Set-Content -LiteralPath $log -Encoding utf8
  $steps.Add([ordered]@{ name=$Name; source=$Source; program=$Program; arguments=$Arguments;
    startedAtUtc=$started; completedAtUtc=[DateTime]::UtcNow.ToString('o'); exitCode=$code;
    expectedExit=$ExpectedExit; expectedPattern=$ExpectedPattern; log=$logRelative;
    outputSha256=(Get-FileHash -LiteralPath $log).Hash })
  Save-ReceiptV5
  if (($ExpectedExit -ceq 'zero' -and $code -ne 0) -or ($ExpectedExit -cne 'zero' -and $code -eq 0) -or
      ($output -join "`n") -notmatch $ExpectedPattern -or
      ($ExpectedExit -ceq 'zero' -and ($output -join "`n") -match 'warning:|depends on axioms:|sorryAx')) {
    throw "V5 gate failed: $Name; see $log"
  }
}
Push-Location $root
$priorLeanPath = $env:LEAN_PATH
try {
  $env:LEAN_PATH = $null
  $versions = [ordered]@{ lean=(@(& lean --version) -join "`n"); lake=(@(& lake --version) -join "`n");
    powershell=$PSVersionTable.PSVersion.ToString(); os=[Runtime.InteropServices.RuntimeInformation]::OSDescription }
  if ($versions.lean -notmatch 'version 4\.33\.1,') { throw 'Lean 4.33.1 is required' }
  $report['versions'] = $versions
  $inputs = @(Get-ValidationInputsV5 $root)
  $manifestPath = Join-Path $outputRoot 'inputs.json'
  if ($FrozenManifest) { Copy-Item -LiteralPath $FrozenManifest -Destination $manifestPath }
  else {
    $manifest = New-InputManifestV5 $root $inputs
    $manifest['git'] = @{ baseHead=(& git rev-parse HEAD).Trim(); branch=(& git branch --show-current).Trim();
      sourceIdentity='All per-file bytes/SHA256 including uncommitted sources; baseHead is not a commit of the modified bundle' }
    $manifest | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $manifestPath -Encoding utf8
  }
  $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json -AsHashtable
  Assert-InputManifestV5 $root $manifest $inputs
  $report['inputManifest'] = @{ path='docs/validation-v5/inputs.json'; fileCount=$manifest.fileCount;
    sha256=(Get-FileHash -LiteralPath $manifestPath).Hash }
  $report.inputsVerifiedBefore = $true
  Save-ReceiptV5
  Invoke-GateV5 'source-audit-blocks' 'scripts/check-source-v5.ps1' 'pwsh' @('-NoProfile','-File','scripts/check-source-v5.ps1') 'SOURCE_V5_OK:'
  Invoke-GateV5 'manifest-integrity-tests' 'scripts/test-validation-manifest-v5.ps1' 'pwsh' @('-NoProfile','-File','scripts/test-validation-manifest-v5.ps1') 'VALIDATION_MANIFEST_V5_TESTS_OK:'
  Invoke-GateV5 'historical-receipts' 'scripts/check-historical-receipts-v5.ps1' 'pwsh' @('-NoProfile','-File','scripts/check-historical-receipts-v5.ps1','-OutputDirectory',$outputRoot) 'HISTORICAL_RECEIPTS_V5_OK:'
  $basePath = Join-Path $outputRoot 'foundation.json'
  $migrationPath = Join-Path $outputRoot 'migration.json'
  Invoke-GateV5 'foundation-and-migration' 'scripts/verify-v5.ps1' 'pwsh' @('-NoProfile','-File','scripts/verify-v5.ps1',
    '-SkipComparison','-SkipReference','-ReportPath',$basePath,'-MigrationReportPath',$migrationPath,'-LogTag',$runId) '"status": "PASSED"'
  $base = Get-Content -LiteralPath $basePath -Raw | ConvertFrom-Json -AsHashtable
  $migration = Get-Content -LiteralPath $migrationPath -Raw | ConvertFrom-Json -AsHashtable
  if ($base.status -cne 'PASSED' -or $migration.status -cne 'PASSED') { throw 'Missing foundation/migration success' }
  if ($base.sourceFiles -ne @($manifest.files | Where-Object { $_.role -ceq 'foundation-source' }).Count -or
      $migration.sources -ne @($manifest.files | Where-Object { $_.role -ceq 'migration-source' }).Count) {
    throw 'Compiled source scope differs from the exhaustive manifest'
  }
  $report['sourceFiles'] = $base.sourceFiles
  $report['axiomAudit'] = $base.axiomAudit
  $report['reducedExecution'] = $base.reducedExecution
  $report['migration'] = $migration
  $compiledAudit = Join-Path $root '.lake/build/lib/lean/scripts/AuditForgettingV4.olean'
  New-Item -ItemType Directory -Path (Split-Path $compiledAudit -Parent) -Force | Out-Null
  Invoke-GateV5 'forgetting-syntax-and-semantics' 'scripts/AuditForgettingV4.lean' 'lake' @('env','lean','-o',$compiledAudit,'scripts/AuditForgettingV4.lean') 'FORGETTING_V4_SEMANTIC_WITNESSES_OK:'
  $auditText = Get-Content -LiteralPath (Join-Path $outputRoot 'logs/forgetting-syntax-and-semantics.txt') -Raw
  foreach ($marker in @('FORGETTING_V4_SYNTAX_OK:','HIDDEN_ENCODING_V4_SYNTAX_ACCEPTED:','REPLAY_V4_SYNTAX_ACCEPTED:')) {
    if ($auditText -notmatch $marker) { throw "Required audit marker missing: $marker" }
  }
  Invoke-GateV5 'coordinate-consumers' 'Tests/FiniteRuleCoordinates.lean' 'lake' @('env','lean','Tests/FiniteRuleCoordinates.lean') 'higher_universe.*does not depend on any axioms'
  Invoke-GateV5 'local-replay-controls' 'Tests/ForgettingAuditScope.lean' 'lake' @('env','lean','Tests/ForgettingAuditScope.lean') 'AUDIT_V4_REPLAY_RUNTIME_OK:'
  Invoke-GateV5 'executable-controls' 'Tests/AuditCorrections.lean' 'lake' @('env','lean','Tests/AuditCorrections.lean') 'AUDIT_V3_RUNTIME_OK:'
  $failureDirectory = Join-Path $root ".lake/validation-v5-fixtures/$runId"
  New-Item -ItemType Directory -Path $failureDirectory -Force | Out-Null
  foreach ($name in @('ForgottenGlobalIdentityV1','ForgottenReorderedInputsV1','ForgottenWrongSortV1')) {
    $source = "Tests/ExpectedFailures/NativeForgettingV1/$name.lean.fail"
    $target = Join-Path $failureDirectory "$name.lean"
    Copy-Item -LiteralPath $source -Destination $target
    Invoke-GateV5 $name $source 'lake' @('env','lean',$target) 'Type mismatch|Application type mismatch' 'nonzero-type-mismatch'
  }
  foreach ($case in @(
      @('forbidden-dependency-rejected','ForbiddenDependency','Scalar name scan reached a forbidden constant:','nonzero-forbidden-name'),
      @('shape-rejected','WrongShape','Scalar memory must contain exactly position and active','nonzero-shape'))) {
    $source = "Tests/ExpectedFailures/ValidationV4/$($case[1]).lean.fail"
    $target = Join-Path $failureDirectory "$($case[1]).lean"
    Copy-Item -LiteralPath $source -Destination $target
    Invoke-GateV5 $case[0] $source 'lake' @('env','lean',$target) $case[2] $case[3]
  }
  $groupingDirectory = Join-Path $outputRoot 'grouping'
  Invoke-GateV5 'certified-grouping' 'scripts/check-grouping-v5.ps1' 'pwsh' @('-NoProfile','-File',
    'scripts/check-grouping-v5.ps1','-OutputDirectory',$groupingDirectory) 'GROUPING_V5_OK:'
  foreach ($name in @('MergedSourcesEqual','UniqueTransportFromTarget','FutureFromCurrent','NeutralEffective','NoRenormalization')) {
    $source = "Tests/ExpectedFailures/CertifiedGrouping/$name.lean.fail"
    $target = Join-Path $failureDirectory "$name.lean"
    Copy-Item -LiteralPath $source -Destination $target
    Invoke-GateV5 $name $source 'lake' @('env','lean',$target) 'Type mismatch|Application type mismatch|Not a definitional equality' 'nonzero-type-mismatch'
  }
  $report['foundationExpectedFailures'] = $base.expectedFailures
  $report['protocolExpectedFailures'] = @($steps.ToArray() | Where-Object { $_.expectedExit -cne 'zero' }).Count
  $report['totalExpectedFailures'] = $base.expectedFailures + $migration.expectedFailures + $report.protocolExpectedFailures
  $additional = [Collections.Generic.List[object]]::new()
  foreach ($pair in @(@($basePath,'foundation.json'),@($migrationPath,'migration.json'),
      @((Join-Path $root ".lake/build-$runId.log"),'logs/foundation-build.txt'),
      @((Join-Path $root ".lake/migration-$runId.log"),'logs/migration-protocol.txt'),
      @((Join-Path $root "Migration/.lake/migration-build-$runId.log"),'logs/migration-build.txt'),
      @((Join-Path $root "Migration/.lake/public-symbols-$runId.log"),'logs/migration-public-symbols.txt'))) {
    $target = Join-Path $outputRoot $pair[1]
    if ($pair[0] -cne $target) { Copy-Item -LiteralPath $pair[0] -Destination $target }
    $additional.Add(@{ path=$pair[1]; sha256=(Get-FileHash -LiteralPath $target).Hash })
  }
  foreach ($file in Get-ChildItem -LiteralPath $groupingDirectory -File) {
    $additional.Add(@{path=('grouping/' + $file.Name);sha256=(Get-FileHash -LiteralPath $file.FullName).Hash})
  }
  $report['additionalOutputs'] = @($additional.ToArray())
  Assert-InputManifestV5 $root $manifest @(Get-ValidationInputsV5 $root)
  if ((Get-FileHash -LiteralPath $manifestPath).Hash -cne $report.inputManifest.sha256) { throw 'Frozen input manifest changed' }
  $report.inputsVerifiedAfter = $true
  $report.status = 'PASSED'
  $report['completedAtUtc'] = [DateTime]::UtcNow.ToString('o')
  Save-ReceiptV5
  "VALIDATION_V5_OK: $($report.platform); $($manifest.fileCount) inputs; $($report.axiomAudit); $( $report.totalExpectedFailures ) expected failures; receipt $receiptPath"
} catch {
  $report.status = 'FAILED'
  $report['error'] = $_.Exception.Message
  Save-ReceiptV5
  throw
} finally {
  $env:LEAN_PATH = $priorLeanPath
  Pop-Location
}
