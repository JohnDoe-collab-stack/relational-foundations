param(
  [switch]$SkipComparison, [switch]$SkipReference, [switch]$SkipMigration,
  [string]$ReportPath = 'docs/verification-result.json',
  [string]$MigrationReportPath = 'Migration/verification-result.json',
  [string]$LogTag = 'verification'
)
$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'LeanSource.ps1')
Test-LeanSourceParser
$report = [ordered]@{ status='RUNNING'; checkedAtUtc=[DateTime]::UtcNow.ToString('o'); toolchain=''; sourceFiles=0; axiomAudit=''; reducedExecution=''; expectedFailures=0; comparison=''; migration=''; reference='' }
$reportPath = if ([IO.Path]::IsPathRooted($ReportPath)) { $ReportPath } else { Join-Path $projectRoot $ReportPath }
$migrationReportPath = if ([IO.Path]::IsPathRooted($MigrationReportPath)) { $MigrationReportPath } else { Join-Path $projectRoot $MigrationReportPath }
$buildLog = ".lake/build-$LogTag.log"
$migrationLog = ".lake/migration-$LogTag.log"
$migrationLogTag = if ($LogTag -eq 'verification') { '' } else { $LogTag }
$report | ConvertTo-Json | Set-Content -LiteralPath $reportPath -Encoding utf8

function Check-Reference {
  $baseline = Get-Content -LiteralPath (Join-Path $projectRoot 'docs/source-baseline.json') -Raw | ConvertFrom-Json
  foreach ($entry in $baseline.files) {
    $path = Join-Path $baseline.sourceRoot $entry.path
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { throw "Reference file missing: $($entry.path)" }
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash -ne $entry.sha256) {
      throw "Reference file changed since baseline: $($entry.path)"
    }
  }
  Push-Location $baseline.sourceRoot
  try {
    $currentFiles = @(& git ls-files --cached --others --exclude-standard) | Sort-Object -Unique
    if ($LASTEXITCODE -ne 0) { throw 'Cannot enumerate original repository' }
    $baselinePaths = @($baseline.files | ForEach-Object { $_.path }) | Sort-Object -Unique
    $existingFiles = @($currentFiles | Where-Object { Test-Path -LiteralPath $_ -PathType Leaf })
    if (@(Compare-Object $baselinePaths $existingFiles).Count -ne 0) { throw 'Original repository file set changed' }
    if ((& git rev-parse HEAD) -ne $baseline.head) { throw 'Original HEAD changed' }
    if ((& git branch --show-current) -ne $baseline.branch) { throw 'Original branch changed' }
  } finally { Pop-Location }
  Add-Type -AssemblyName System.IO.Compression.FileSystem
  $archive = [IO.Compression.ZipFile]::OpenRead((Join-Path $projectRoot 'reference/source.zip'))
  $sha = [Security.Cryptography.SHA256]::Create()
  try {
    if ($archive.Entries.Count -ne $baseline.files.Count) { throw 'Reference archive file count differs' }
    foreach ($entry in $baseline.files) {
      $zipEntry = $archive.GetEntry($entry.path.Replace('\','/'))
      if ($null -eq $zipEntry) { throw "Reference archive missing $($entry.path)" }
      $stream = $zipEntry.Open()
      try { $digest = [BitConverter]::ToString($sha.ComputeHash($stream)).Replace('-','') }
      finally { $stream.Dispose() }
      if ($digest -ne $entry.sha256) { throw "Reference archive hash differs for $($entry.path)" }
    }
  } finally { $sha.Dispose(); $archive.Dispose() }
  return "REFERENCE_OK: $($baseline.files.Count) files unchanged; recovery archive verified"
}

Push-Location $projectRoot
$priorLeanPath = $env:LEAN_PATH
try {
  $env:LEAN_PATH = $null
  if (-not $SkipReference) { $report.reference = Check-Reference }
  $sources = @(Get-Item 'RelationalFoundations.lean') +
    @(Get-ChildItem 'RelationalFoundations','Tests' -Filter '*.lean' -Recurse)
  $moduleFiles = @{}
  foreach ($file in $sources) {
    $relative = $file.FullName.Substring($projectRoot.Length + 1).Replace('\','/')
    $module = $relative.Substring(0,$relative.Length - 5).Replace('/','.')
    $moduleFiles[$module] = $file
    $rawText = Get-Content -LiteralPath $file.FullName -Raw
    $text = Remove-LeanComments -Source $rawText
    if ($text -cmatch '(?m)^\s*(axiom|unsafe)\s|\b(noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b') {
      throw "Forbidden construct in $relative"
    }
    foreach ($dependency in @(Get-LeanImports -Source $rawText)) {
      if ($dependency -ne 'Init' -and $dependency -notmatch '^(RelationalFoundations(?:\.|$)|Tests\.)') {
        throw "External dependency in $relative : $dependency"
      }
      if ($module -like 'RelationalFoundations*' -and $dependency -like 'Tests.*') {
        throw "Production depends on tests: $module -> $dependency"
      }
    }
    if ($rawText -match '(?m)[ \t]+$') { throw "Trailing whitespace in $relative" }
  }
  $queue = [Collections.Generic.Queue[string]]::new()
  $visited = [Collections.Generic.HashSet[string]]::new()
  $queue.Enqueue('RelationalFoundations')
  $queue.Enqueue('Tests.FoundationTests')
  while ($queue.Count -gt 0) {
    $module = $queue.Dequeue()
    if (-not $visited.Add($module)) { continue }
    if (-not $moduleFiles.ContainsKey($module)) { throw "Unknown imported module $module" }
    $text = Get-Content -LiteralPath $moduleFiles[$module].FullName -Raw
    foreach ($dependency in @(Get-LeanImports -Source $text)) {
      if ($dependency -ne 'Init') { $queue.Enqueue($dependency) }
    }
  }
  if ($visited.Count -ne $sources.Count) { throw 'Production or test module is unreachable from its public root' }
  $report.sourceFiles = $sources.Count
  $report.toolchain = (Get-Content lean-toolchain -Raw).Trim()
  $output = @(& lake build 2>&1)
  $buildExit = $LASTEXITCODE
  $output | Set-Content -LiteralPath $buildLog -Encoding utf8
  if ($buildExit -ne 0) { throw "Build failed. See $buildLog" }
  if (($output -join "`n") -match 'warning:|depends on axioms:|sorryAx') { throw 'Build contains warnings or forbidden axiom dependencies' }
  foreach ($module in $moduleFiles.Keys) {
    $olean = Join-Path '.lake/build/lib/lean' ($module.Replace('.','/') + '.olean')
    if (-not (Test-Path -LiteralPath $olean)) { throw "Missing compiled module $module" }
  }
  $audit = @(& lake env lean scripts/Audit.lean 2>&1)
  if ($LASTEXITCODE -ne 0) { throw ($audit -join "`n") }
  if (($audit -join "`n") -notmatch 'AUDIT_OK: \d+ declarations, zero axiom dependencies') { throw 'Exhaustive audit receipt missing' }
  $report.axiomAudit = ($audit -join "`n").Trim()
  $reducedAudit = @(& lake env lean scripts/AuditReduced.lean 2>&1)
  if ($LASTEXITCODE -ne 0) { throw ($reducedAudit -join "`n") }
  if (($reducedAudit -join "`n") -notmatch 'REDUCED_EXECUTION_OK:') { throw 'Reduced execution audit receipt missing' }
  $report.reducedExecution = ($reducedAudit -join "`n").Trim()

  $failureRoot = Join-Path $projectRoot '.lake/expected-failures'
  New-Item -ItemType Directory -Path $failureRoot -Force | Out-Null
  $fixtures = @(Get-ChildItem 'Tests/ExpectedFailures' -Filter '*.lean.fail')
  $expectedNames = @('BareEquivalence.lean.fail','BoundaryPositivity.lean.fail','CollapsedFragment.lean.fail','GenericFalseAdmission.lean.fail','JunctionAsGeneratedStep.lean.fail','RegimeFromJunction.lean.fail','Rigidity.lean.fail','TypedNumericInput.lean.fail','UnreachableReducedMemory.lean.fail')
  if (@(Compare-Object ($expectedNames | Sort-Object) ($fixtures.Name | Sort-Object)).Count -ne 0) {
    throw 'Expected-failure catalogue differs from its explicit manifest'
  }
  foreach ($fixture in $fixtures) {
    $target = Join-Path $failureRoot $fixture.Name.Substring(0,$fixture.Name.Length - 5)
    Copy-Item -LiteralPath $fixture.FullName -Destination $target
    $failureOutput = @(& lake env lean $target 2>&1)
    if ($LASTEXITCODE -eq 0) { throw "Expected failure compiled: $($fixture.Name)" }
    if (($failureOutput -join "`n") -notmatch 'Type mismatch|Application type mismatch') {
      throw "Unexpected failure mode in $($fixture.Name): $($failureOutput -join ' ')"
    }
    $report.expectedFailures++
  }
  if ($report.expectedFailures -ne $expectedNames.Count) { throw 'Expected-failure catalogue is incomplete' }

  if (-not $SkipComparison) {
    $baseline = Get-Content docs/source-baseline.json -Raw | ConvertFrom-Json
    # Recompile current reference sources outside the original repository:
    # cached original .olean files are not evidence for current source contents.
    $referenceBuild = Join-Path $projectRoot '.lake/reference-verification'
    New-Item -ItemType Directory -Path $referenceBuild -Force | Out-Null
    $env:LEAN_PATH = $referenceBuild
    foreach ($referenceModule in @('ExactTypeTransport','SegmentedResidualRole','AbstractSegmentedTurning','StrongPerimetralTurning')) {
      $referenceSource = Join-Path $referenceBuild ($referenceModule + '.lean')
      Copy-Item -LiteralPath (Join-Path $baseline.sourceRoot ($referenceModule + '.lean')) -Destination $referenceSource
      $referenceOutput = @(& lake env lean -o (Join-Path $referenceBuild ($referenceModule + '.olean')) $referenceSource 2>&1)
      $referenceExit = $LASTEXITCODE
      $referenceOutput | Set-Content -LiteralPath (Join-Path $referenceBuild ($referenceModule + '.log')) -Encoding utf8
      if ($referenceExit -ne 0) { throw "Fresh reference compilation failed: $referenceModule" }
    }
    $comparison = @(& lake env lean Comparison/Legacy.lean 2>&1)
    $comparisonExit = $LASTEXITCODE
    $comparison | Set-Content -LiteralPath '.lake/comparison-verification.log' -Encoding utf8
    if ($comparisonExit -ne 0) { throw 'Legacy comparison failed. See .lake/comparison-verification.log' }
    if (($comparison -join "`n") -match 'warning:|depends on axioms:|sorryAx') { throw 'Legacy comparison audit failed' }
    $expectedAudits = [regex]::Matches((Get-Content Comparison/Legacy.lean -Raw), '(?m)^#print axioms ').Count
    $actualAudits = [regex]::Matches(($comparison -join "`n"), 'does not depend on any axioms').Count
    if ($expectedAudits -eq 0 -or $actualAudits -ne $expectedAudits) { throw 'Legacy comparison audit receipt count differs' }
    $report.comparison = "COMPARISON_OK: $actualAudits audited results, no original source written"
    $env:LEAN_PATH = $null
  } else { $report.comparison = 'Skipped explicitly' }
  if (-not $SkipMigration) {
    $migrationOutput = @(& pwsh -NoProfile -File scripts/verify-migration.ps1 -ReportPath $migrationReportPath -LogTag $migrationLogTag 2>&1)
    $migrationExit = $LASTEXITCODE
    $migrationOutput | Set-Content -LiteralPath $migrationLog -Encoding utf8
    if ($migrationExit -ne 0) { throw "Migration verification failed; see $migrationLog" }
    $migrationReport = Get-Content -LiteralPath $migrationReportPath -Raw | ConvertFrom-Json
    if ($migrationReport.status -ne 'PASSED') { throw 'Migration success receipt missing' }
    $report.migration = "MIGRATION_OK: $($migrationReport.sources) sources; $($migrationReport.axiomAudit); $($migrationReport.expectedFailures) expected failures"
  } else { $report.migration = 'Skipped explicitly' }
  if (-not $SkipReference) { $report.reference = Check-Reference } else { $report.reference = 'Skipped explicitly' }
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
