Set-StrictMode -Version Latest

function Resolve-ValidationFileV2 {
  param([string]$Root, [string]$Relative)
  if ([string]::IsNullOrWhiteSpace($Relative) -or [IO.Path]::IsPathRooted($Relative) -or
      $Relative.Contains('\') -or $Relative.Contains(':') -or
      @($Relative.Split('/') | Where-Object { $_ -in @('', '.', '..') }).Count) {
    throw "Invalid relative validation path: $Relative"
  }
  $absoluteRoot = [IO.Path]::GetFullPath($Root).TrimEnd([IO.Path]::DirectorySeparatorChar)
  $resolved = [IO.Path]::GetFullPath((Join-Path $absoluteRoot $Relative))
  if (-not $resolved.StartsWith($absoluteRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Validation path escapes root: $Relative"
  }
  return $resolved
}

function Get-ValidationInputsV2 {
  param([string]$Root)
  $paths = [Collections.Generic.Dictionary[string,string]]::new([StringComparer]::Ordinal)
  $paths.Add('RelationalFoundations.lean', 'foundation-source')
  foreach ($directory in @('RelationalFoundations','Tests','Migration')) {
    foreach ($file in Get-ChildItem -LiteralPath (Join-Path $Root $directory) -Recurse -File) {
      $relative = [IO.Path]::GetRelativePath($Root,$file.FullName).Replace('\','/')
      if ($relative -match '(^|/)(\.lake|scripts)/') { continue }
      if ($file.Name.EndsWith('.lean.fail')) { $paths.Add($relative,'rejection-fixture') }
      elseif ($file.Extension -eq '.lean') {
        $role = if ($directory -eq 'Migration') { 'migration-source' } else { 'foundation-source' }
        $paths.Add($relative,$role)
      }
    }
  }
  foreach ($path in @(
      'scripts/verify-forgetting-v2.ps1','scripts/ValidationManifestV2.ps1',
      'scripts/check-forgetting-v2.ps1','scripts/test-validation-manifest-v2.ps1',
      'scripts/verify.ps1','scripts/verify-migration.ps1','scripts/LeanSource.ps1',
      'scripts/Audit.lean','scripts/AuditReduced.lean','scripts/AuditForgettingV1.lean',
      'Migration/scripts/Audit.lean','Migration/scripts/CheckPublicSymbols.lean',
      'Migration/scripts/check-stratification.ps1','Migration/scripts/check-import-boundaries.ps1',
      'Migration/scripts/check-expected-failures.ps1')) { $paths.Add($path,'validation-script') }
  foreach ($path in @('lakefile.toml','lean-toolchain','lake-manifest.json',
      'Migration/lakefile.toml','Migration/lean-toolchain','Migration/lake-manifest.json')) {
    $paths.Add($path,'build-configuration')
  }
  foreach ($path in @('Migration/scripts/stratification.tsv','Migration/scripts/expected-failures.tsv',
      'Migration/scripts/import-boundaries.txt','Migration/scripts/constitutive-normalizer-core-import-boundaries.txt',
      'Migration/scripts/executed-history-import-boundaries.txt','Migration/scripts/measured-accounting-import-boundaries.txt',
      'docs/migration-symbols.csv')) { $paths.Add($path,'validation-catalogue') }
  foreach ($path in @('docs/verification-result.json','Migration/verification-result.json',
      'docs/verification-forgetting-v1.json','Migration/verification-forgetting-v1.json')) {
    $paths.Add($path,'reference-receipt')
  }
  $paths.Add('scripts/verify-forgetting-v1.ps1','reference-protocol')
  foreach ($path in @('README.md','docs/oubli-certifie-continuations-natives-v1.fr.md',
      'docs/validation-oubli-natif-v2.fr.md')) { $paths.Add($path,'delivery-document') }
  $orderedPaths = [string[]]@($paths.Keys)
  [Array]::Sort($orderedPaths,[StringComparer]::Ordinal)
  foreach ($path in $orderedPaths) {
    $fullPath = Resolve-ValidationFileV2 $Root $path
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) { throw "Validation input missing: $path" }
    [pscustomobject]@{ path=$path; role=$paths[$path] }
  }
}

function New-InputManifestV2 {
  param([string]$Root, [object[]]$Inputs)
  $entries = @($Inputs | ForEach-Object {
    $fullPath = Resolve-ValidationFileV2 $Root $_.path
    [ordered]@{ path=$_.path; role=$_.role; bytes=(Get-Item -LiteralPath $fullPath).Length;
      sha256=(Get-FileHash -LiteralPath $fullPath -Algorithm SHA256).Hash }
  })
  return [ordered]@{
    schemaVersion=2; protocol='native-forgetting-validation-v2'; hashAlgorithm='SHA256'
    createdAtUtc=[DateTime]::UtcNow.ToString('o'); fileCount=$entries.Count; files=$entries
  }
}

function Assert-InputManifestV2 {
  param([string]$Root, [object]$Manifest, [object[]]$Inputs)
  if ($Manifest.schemaVersion -ne 2 -or $Manifest.protocol -cne 'native-forgetting-validation-v2' -or
      $Manifest.hashAlgorithm -cne 'SHA256') { throw 'Unsupported V2 input manifest' }
  if ($Manifest.fileCount -ne @($Manifest.files).Count) { throw 'Manifest file count differs' }
  $declared = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach ($entry in $Manifest.files) {
    $null = Resolve-ValidationFileV2 $Root $entry.path
    if ($declared.ContainsKey($entry.path)) { throw "Duplicate manifest path: $($entry.path)" }
    if ($entry.sha256 -cnotmatch '^[0-9A-F]{64}$' -or $entry.bytes -lt 0) { throw "Invalid manifest digest/size: $($entry.path)" }
    $declared.Add($entry.path,$entry)
  }
  if ($declared.Count -ne $Inputs.Count) { throw 'Validation input catalogue differs from manifest' }
  foreach ($inputFile in $Inputs) {
    if (-not $declared.ContainsKey($inputFile.path)) { throw "Unmanifested validation input: $($inputFile.path)" }
    $entry = $declared[$inputFile.path]
    if ($entry.role -cne $inputFile.role) { throw "Validation input role differs: $($inputFile.path)" }
    $fullPath = Resolve-ValidationFileV2 $Root $inputFile.path
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) { throw "Validation input missing: $($inputFile.path)" }
    if ((Get-Item -LiteralPath $fullPath).Length -ne $entry.bytes -or
        (Get-FileHash -LiteralPath $fullPath -Algorithm SHA256).Hash -cne $entry.sha256) {
      throw "Validation input changed: $($inputFile.path)"
    }
  }
}

function Assert-ManifestLinkV2 {
  param([string]$Root, [object]$Link)
  $manifestPath = Resolve-ValidationFileV2 $Root $Link.path
  if ($Link.path -cne 'docs/manifest-forgetting-v2.json' -or
      (Get-FileHash -LiteralPath $manifestPath -Algorithm SHA256).Hash -cne $Link.sha256) {
    throw 'Receipt-to-manifest digest differs'
  }
  $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json -AsHashtable
  if ($Link.fileCount -ne $manifest.fileCount) { throw 'Receipt-to-manifest file count differs' }
  return $manifest
}

function Assert-ValidationBundleV2 {
  param([string]$Root)
  $receiptPath = Resolve-ValidationFileV2 $Root 'docs/verification-forgetting-v2.json'
  $receipt = Get-Content -LiteralPath $receiptPath -Raw | ConvertFrom-Json -AsHashtable
  if ($receipt.status -cne 'PASSED' -or $receipt.protocol -cne 'native-forgetting-validation-v2' -or
      -not $receipt.inputsVerifiedBefore -or -not $receipt.inputsVerifiedAfter) { throw 'V2 success receipt missing' }
  $manifest = Assert-ManifestLinkV2 $Root $receipt.inputManifest
  Assert-InputManifestV2 $Root $manifest @(Get-ValidationInputsV2 $Root)
  $migrationPath = Resolve-ValidationFileV2 $Root $receipt.migrationReceipt.path
  if ($receipt.migrationReceipt.path -cne 'Migration/verification-forgetting-v2.json' -or
      (Get-FileHash -LiteralPath $migrationPath -Algorithm SHA256).Hash -cne $receipt.migrationReceipt.sha256) {
    throw 'Migration receipt digest differs'
  }
  $migration = Get-Content -LiteralPath $migrationPath -Raw | ConvertFrom-Json -AsHashtable
  if ($migration.status -cne 'PASSED' -or $migration.protocol -cne 'native-forgetting-validation-v2' -or
      $migration.inputManifest.path -cne $receipt.inputManifest.path -or
      $migration.inputManifest.sha256 -cne $receipt.inputManifest.sha256 -or
      $migration.inputManifest.fileCount -ne $manifest.fileCount) { throw 'Migration receipt-to-manifest link differs' }
  $expectedReferences = @('docs/verification-result.json','Migration/verification-result.json',
    'docs/verification-forgetting-v1.json','Migration/verification-forgetting-v1.json')
  if (@(Compare-Object ($expectedReferences | Sort-Object) (@($receipt.referenceReceipts | ForEach-Object { $_.path }) | Sort-Object)).Count) {
    throw 'The four prior receipts are not all identified'
  }
  foreach ($reference in $receipt.referenceReceipts) {
    $path = Resolve-ValidationFileV2 $Root $reference.path
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash -cne $reference.sha256) {
      throw "Reference receipt changed: $($reference.path)"
    }
  }
  $foundationCount = @($manifest.files | Where-Object { $_.role -eq 'foundation-source' }).Count
  $migrationCount = @($manifest.files | Where-Object { $_.role -eq 'migration-source' }).Count
  if ($receipt.sourceFiles -ne $foundationCount -or $migration.sources -ne $migrationCount) {
    throw 'Verified source counts differ from input manifest'
  }
  if ($receipt.axiomAudit -notmatch '^AUDIT_OK: \d+ declarations, zero axiom dependencies$' -or
      $receipt.forgettingExecution -notmatch '^FORGETTING_EXECUTION_V1_OK:' -or
      $receipt.expectedFailures -ne 12 -or $receipt.totalExpectedFailures -ne 31 -or $migration.expectedFailures -ne 19) {
    throw 'V2 verification evidence is incomplete'
  }
  if (@($receipt.validationSteps).Count -ne 6 -or $receipt.integrityTests -notmatch '^VALIDATION_MANIFEST_V2_TESTS_OK:') {
    throw 'V2 execution/integrity-test record is incomplete'
  }
  foreach ($step in $receipt.validationSteps) {
    if (@($manifest.files | Where-Object { $_.path -ceq $step.file }).Count -ne 1 -or
        $step.outputSha256 -cnotmatch '^[0-9A-F]{64}$' -or
        ($step.expectedExit -ceq 'zero' -and $step.exitCode -ne 0) -or
        ($step.expectedExit -ceq 'nonzero-type-mismatch' -and $step.exitCode -eq 0) -or
        $step.expectedExit -cnotin @('zero','nonzero-type-mismatch')) {
      throw "Recorded validation step differs: $($step.name)"
    }
  }
  return "VALIDATION_BUNDLE_V2_OK: $($manifest.fileCount) files; source/script/configuration digests and both receipts agree; four prior receipts preserved"
}
