Set-StrictMode -Version Latest

function Get-ValidationInputsV3 {
  param([string]$Root)
  $paths = [Collections.Generic.Dictionary[string,string]]::new([StringComparer]::Ordinal)
  foreach ($directory in @('RelationalFoundations','Tests','Migration','scripts','docs','.github')) {
    foreach ($file in Get-ChildItem -LiteralPath (Join-Path $Root $directory) -Recurse -File) {
      $relative = [IO.Path]::GetRelativePath($Root,$file.FullName).Replace('\','/')
      if ($relative -match '(^|/)\.lake/' -or $relative -match '^docs/validation-v3/' -or
          $relative -match '\.log$') { continue }
      $role = $null
      if ($file.Name.EndsWith('.lean.fail')) { $role = 'rejection-fixture' }
      elseif ($file.Extension -eq '.lean') {
        $role = if ($relative -match '(^|/)scripts/') { 'validation-script' }
          elseif ($directory -eq 'Migration') { 'migration-source' } else { 'foundation-source' }
      } elseif ($relative -match '(^|/)scripts/' -or $directory -eq 'scripts') { $role = 'validation-script' }
      elseif ($directory -eq 'docs') { $role = 'delivery-document' }
      elseif ($directory -eq '.github') { $role = 'ci-configuration' }
      elseif ($file.Name -in @('lakefile.toml','lean-toolchain','lake-manifest.json')) { $role = 'build-configuration' }
      elseif ($file.Name -in @('verification-result.json','verification-forgetting-v1.json','verification-forgetting-v2.json')) {
        $role = 'reference-receipt'
      }
      if ($role) { $paths.Add($relative,$role) }
    }
  }
  foreach ($path in @('RelationalFoundations.lean','README.md','AGENTS.md','.gitignore','.gitattributes',
      'lakefile.toml','lean-toolchain','lake-manifest.json')) {
    $paths.Add($path, $(if ($path -eq 'RelationalFoundations.lean') { 'foundation-source' } else { 'project-configuration' }))
  }
  $ordered = [string[]]@($paths.Keys)
  [Array]::Sort($ordered,[StringComparer]::Ordinal)
  foreach ($path in $ordered) {
    $fullPath = Resolve-ValidationFileV3 $Root $path
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) { throw "Validation input missing: $path" }
    [pscustomobject]@{ path=$path; role=$paths[$path] }
  }
}

function Resolve-ValidationFileV3 {
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

function New-InputManifestV3 {
  param([string]$Root, [object[]]$Inputs)
  $entries = @($Inputs | ForEach-Object {
    $fullPath = Resolve-ValidationFileV3 $Root $_.path
    [ordered]@{ path=$_.path; role=$_.role; bytes=(Get-Item -LiteralPath $fullPath -Force).Length;
      sha256=(Get-FileHash -LiteralPath $fullPath -Algorithm SHA256).Hash }
  })
  return [ordered]@{
    schemaVersion=3; protocol='foundations-audit-validation-v3'; hashAlgorithm='SHA256'
    createdAtUtc=[DateTime]::UtcNow.ToString('o'); fileCount=$entries.Count; files=$entries
  }
}

function Assert-InputManifestV3 {
  param([string]$Root, [object]$Manifest, [object[]]$Inputs)
  if ($Manifest.schemaVersion -ne 3 -or $Manifest.protocol -cne 'foundations-audit-validation-v3' -or
      $Manifest.hashAlgorithm -cne 'SHA256') { throw 'Unsupported V3 input manifest' }
  if ($Manifest.fileCount -ne @($Manifest.files).Count) { throw 'Manifest file count differs' }
  $declared = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach ($entry in $Manifest.files) {
    $null = Resolve-ValidationFileV3 $Root $entry.path
    if ($declared.ContainsKey($entry.path)) { throw "Duplicate manifest path: $($entry.path)" }
    if ($entry.sha256 -cnotmatch '^[0-9A-F]{64}$' -or $entry.bytes -lt 0) { throw "Invalid manifest digest/size: $($entry.path)" }
    $declared.Add($entry.path,$entry)
  }
  if ($declared.Count -ne $Inputs.Count) { throw 'Validation input catalogue differs from manifest' }
  foreach ($inputFile in $Inputs) {
    if (-not $declared.ContainsKey($inputFile.path)) { throw "Unmanifested validation input: $($inputFile.path)" }
    $entry = $declared[$inputFile.path]
    if ($entry.role -cne $inputFile.role) { throw "Validation input role differs: $($inputFile.path)" }
    $fullPath = Resolve-ValidationFileV3 $Root $inputFile.path
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) { throw "Validation input missing: $($inputFile.path)" }
    if ((Get-Item -LiteralPath $fullPath -Force).Length -ne $entry.bytes -or
        (Get-FileHash -LiteralPath $fullPath -Algorithm SHA256).Hash -cne $entry.sha256) {
      throw "Validation input changed: $($inputFile.path)"
    }
  }
}

function Assert-ManifestLinkV3 {
  param([string]$Root, [object]$Link)
  $path = Resolve-ValidationFileV3 $Root $Link.path
  if ((Get-FileHash -LiteralPath $path).Hash -cne $Link.sha256) { throw 'Receipt-to-manifest digest differs' }
  $manifest = Get-Content -LiteralPath $path -Raw | ConvertFrom-Json -AsHashtable
  if ($Link.fileCount -ne $manifest.fileCount) { throw 'Receipt-to-manifest file count differs' }
  return $manifest
}

function Assert-ValidationBundleV3 {
  param([string]$Root)
  $bundle = 'docs/validation-v3'
  $manifestPath = Resolve-ValidationFileV3 $Root "$bundle/inputs.json"
  $manifestSha = (Get-FileHash -LiteralPath $manifestPath).Hash
  $index = Get-Content -LiteralPath (Resolve-ValidationFileV3 $Root "$bundle/index.json") -Raw | ConvertFrom-Json -AsHashtable
  if ($index.protocol -cne 'foundations-audit-validation-v3' -or $index.inputManifestSha256 -cne $manifestSha -or
      @($index.receipts).Count -ne 2) { throw 'V3 bundle index differs' }
  $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json -AsHashtable
  Assert-InputManifestV3 $Root $manifest @(Get-ValidationInputsV3 $Root)
  $gateNames = @('source-audit-blocks','manifest-integrity-tests','historical-receipts','foundation-and-migration',
    'forgetting-syntax-and-semantics','executable-controls','ForgottenGlobalIdentityV1','ForgottenReorderedInputsV1',
    'ForgottenWrongSortV1','hidden-replay-rejected')
  foreach ($platform in @('Windows','Linux')) {
    $receiptRoot = Resolve-ValidationFileV3 $Root "$bundle/$platform"
    $receiptPath = Join-Path $receiptRoot 'receipt.json'
    $bound = @($index.receipts | Where-Object { $_.platform -ceq $platform })
    if ($bound.Count -ne 1 -or $bound[0].path -cne "$bundle/$platform/receipt.json" -or
        (Get-FileHash -LiteralPath $receiptPath).Hash -cne $bound[0].sha256) {
      throw "V3 indexed receipt digest differs: $platform"
    }
    $receipt = Get-Content -LiteralPath $receiptPath -Raw | ConvertFrom-Json -AsHashtable
    if ($receipt.status -cne 'PASSED' -or $receipt.protocol -cne 'foundations-audit-validation-v3' -or
        $receipt.platform -cne $platform -or -not $receipt.inputsVerifiedBefore -or -not $receipt.inputsVerifiedAfter -or
        $receipt.inputManifest.sha256 -cne $manifestSha -or $receipt.inputManifest.fileCount -ne $manifest.fileCount) {
      throw "Missing bound V3 success receipt for $platform"
    }
    if ($receipt.inputManifest.path -cne "$bundle/inputs.json" -or
        $receipt.versions.lean -notmatch 'version 4\.33\.1,' -or
        $receipt.sourceFiles -ne @($manifest.files | Where-Object { $_.role -eq 'foundation-source' }).Count -or
        $receipt.migration.sources -ne @($manifest.files | Where-Object { $_.role -eq 'migration-source' }).Count -or
        $receipt.totalExpectedFailures -ne 32 -or $receipt.migration.expectedFailures -ne 19 -or
        $receipt.axiomAudit -notmatch '^AUDIT_OK: \d+ declarations, zero axiom dependencies$') {
      throw "Incomplete V3 scope/counts for $platform"
    }
    if (@(Compare-Object ($gateNames | Sort-Object) (@($receipt.validationSteps | ForEach-Object { $_.name }) | Sort-Object)).Count) {
      throw "V3 gate catalogue differs for $platform"
    }
    foreach ($step in $receipt.validationSteps) {
      if (@($manifest.files | Where-Object { $_.path -ceq $step.source }).Count -ne 1 -or
          $step.outputSha256 -cnotmatch '^[0-9A-F]{64}$' -or
          $step.expectedExit -cnotin @('zero','nonzero-type-mismatch','nonzero-historical-dependency') -or
          ($step.expectedExit -ceq 'zero' -and $step.exitCode -ne 0) -or
          ($step.expectedExit -cne 'zero' -and $step.exitCode -eq 0)) { throw "Invalid recorded gate: $($step.name)" }
      $log = Resolve-ValidationFileV3 $receiptRoot $step.log
      if ((Get-FileHash -LiteralPath $log).Hash -cne $step.outputSha256 -or
          (Get-Content -LiteralPath $log -Raw) -notmatch $step.expectedPattern) {
        throw "V3 output differs: $platform/$($step.name)"
      }
    }
    foreach ($output in $receipt.additionalOutputs) {
      $path = Resolve-ValidationFileV3 $receiptRoot $output.path
      if ((Get-FileHash -LiteralPath $path).Hash -cne $output.sha256) { throw "V3 internal output differs: $($output.path)" }
    }
  }
  "VALIDATION_V3_BUNDLE_OK: $($manifest.fileCount) frozen inputs; Windows and Linux receipts and all output hashes verified"
}
