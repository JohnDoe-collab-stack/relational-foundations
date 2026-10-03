Set-StrictMode -Version Latest

function Resolve-ValidationFileV5 {
  param([string]$Root,[string]$Relative)
  if ([string]::IsNullOrWhiteSpace($Relative) -or [IO.Path]::IsPathRooted($Relative) -or
      $Relative.Contains('\') -or $Relative.Contains(':') -or
      @($Relative.Split('/') | Where-Object { $_ -in @('', '.', '..') }).Count) {
    throw "Invalid relative validation path: $Relative"
  }
  $base = [IO.Path]::GetFullPath($Root).TrimEnd([IO.Path]::DirectorySeparatorChar)
  $resolved = [IO.Path]::GetFullPath((Join-Path $base $Relative))
  $comparison = if ($IsWindows) { [StringComparison]::OrdinalIgnoreCase } else { [StringComparison]::Ordinal }
  if (-not $resolved.StartsWith($base + [IO.Path]::DirectorySeparatorChar,$comparison)) {
    throw "Validation path escapes root: $Relative"
  }
  $resolved
}

function Get-ValidationCatalogueV5 {
  param([string]$Root)
  $base = [IO.Path]::GetFullPath($Root)
  $queue = [Collections.Generic.Queue[string]]::new()
  $queue.Enqueue($base)
  $paths = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $folded = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
  while ($queue.Count) {
    foreach ($item in Get-ChildItem -LiteralPath $queue.Dequeue() -Force) {
      $path = [IO.Path]::GetRelativePath($base,$item.FullName).Replace('\','/')
      # Only these build caches and Git metadata are outside the scientific catalogue.
      if ($path -cin @('.git','.lake','Migration/.lake','Comparison/.lake')) { continue }
      $null = Resolve-ValidationFileV5 $base $path
      if (-not $folded.Add($path)) { throw "Case-colliding validation path: $path" }
      if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
        throw "Linked validation entry: $path"
      }
      if ($item.PSIsContainer) { $queue.Enqueue($item.FullName); continue }
      $role = if ($path.StartsWith('docs/validation-v5/',[StringComparison]::Ordinal)) { 'current-evidence' }
        elseif ($path -cmatch '^docs/validation-v[1-4]/') { 'historical-evidence' }
        elseif ($path.EndsWith('.lean.fail',[StringComparison]::Ordinal)) { 'rejection-fixture' }
        elseif ($path.EndsWith('.lean',[StringComparison]::Ordinal)) {
          if ($path -match '(^|/)scripts/') { 'validation-script' }
          elseif ($path.StartsWith('Migration/',[StringComparison]::Ordinal)) { 'migration-source' }
          elseif ($path.StartsWith('Comparison/',[StringComparison]::Ordinal)) { 'comparison-source' }
          elseif ($path.StartsWith('reference/',[StringComparison]::Ordinal)) { 'reference-material' }
          else { 'foundation-source' }
        }
        elseif ($path -match '(^|/)scripts/') { 'validation-script' }
        elseif ($path.StartsWith('.github/',[StringComparison]::Ordinal)) { 'ci-configuration' }
        elseif ($path.StartsWith('docs/',[StringComparison]::Ordinal)) { 'delivery-document' }
        elseif ($path.StartsWith('reference/',[StringComparison]::Ordinal)) { 'reference-material' }
        elseif ($item.Name -in @('lakefile.toml','lean-toolchain','lake-manifest.json')) { 'build-configuration' }
        else { 'auxiliary-input' }
      $paths.Add($path,[pscustomobject]@{path=$path;role=$role})
    }
  }
  $ordered = [string[]]@($paths.Keys)
  [Array]::Sort($ordered,[StringComparer]::Ordinal)
  foreach ($path in $ordered) { $paths[$path] }
}

function Get-ValidationInputsV5 {
  param([string]$Root)
  Get-ValidationCatalogueV5 $Root | Where-Object { $_.role -cne 'current-evidence' }
}

function New-InputManifestV5 {
  param([string]$Root,[object[]]$Inputs)
  $entries = @($Inputs | ForEach-Object {
    $file = Resolve-ValidationFileV5 $Root $_.path
    [ordered]@{path=$_.path;role=$_.role;bytes=(Get-Item -LiteralPath $file -Force).Length;
      sha256=(Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash}
  })
  [ordered]@{schemaVersion=5;protocol='foundations-audit-validation-v5';hashAlgorithm='SHA256';
    cataloguePolicy='all-ordinary-files-v5';createdAtUtc=[DateTime]::UtcNow.ToString('o');
    fileCount=$entries.Count;files=$entries}
}

function Assert-InputManifestV5 {
  param([string]$Root,[object]$Manifest,[object[]]$Inputs)
  if ($Manifest.schemaVersion -ne 5 -or $Manifest.protocol -cne 'foundations-audit-validation-v5' -or
      $Manifest.hashAlgorithm -cne 'SHA256' -or $Manifest.cataloguePolicy -cne 'all-ordinary-files-v5' -or
      $Manifest.fileCount -ne @($Manifest.files).Count) { throw 'Unsupported or incomplete V5 input manifest' }
  $declared = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $folded = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach ($entry in $Manifest.files) {
    $null = Resolve-ValidationFileV5 $Root $entry.path
    if (-not $folded.Add($entry.path)) { throw "Duplicate or case-colliding manifest path: $($entry.path)" }
    if ($entry.sha256 -cnotmatch '^[0-9A-F]{64}$' -or $entry.bytes -lt 0) { throw 'Invalid manifest digest or size' }
    $declared.Add($entry.path,$entry)
  }
  if ($declared.Count -ne $Inputs.Count) { throw 'Validation input catalogue differs from manifest' }
  foreach ($inputFile in $Inputs) {
    if (-not $declared.ContainsKey($inputFile.path)) { throw "Unmanifested validation input: $($inputFile.path)" }
    $entry = $declared[$inputFile.path]
    if ($entry.role -cne $inputFile.role) { throw "Validation input role differs: $($inputFile.path)" }
    $file = Resolve-ValidationFileV5 $Root $inputFile.path
    if ((Get-Item -LiteralPath $file -Force).Length -ne $entry.bytes -or
        (Get-FileHash -LiteralPath $file).Hash -cne $entry.sha256) { throw "Validation input changed: $($entry.path)" }
  }
}

function Get-ValidationGatesV5 {
  @('source-audit-blocks','manifest-integrity-tests','historical-receipts','foundation-and-migration',
    'forgetting-syntax-and-semantics','executable-controls','local-replay-controls','coordinate-consumers',
    'ForgottenGlobalIdentityV1','ForgottenReorderedInputsV1','ForgottenWrongSortV1',
    'forbidden-dependency-rejected','shape-rejected','certified-grouping',
    'MergedSourcesEqual','UniqueTransportFromTarget','FutureFromCurrent','NeutralEffective','NoRenormalization')
}

function Assert-ValidationBundleV5 {
  param([string]$Root)
  $bundle = 'docs/validation-v5'
  $indexPath = Resolve-ValidationFileV5 $Root "$bundle/index.json"
  $index = Get-Content -LiteralPath $indexPath -Raw | ConvertFrom-Json -AsHashtable
  $manifestPath = Resolve-ValidationFileV5 $Root "$bundle/inputs.json"
  $manifestSha = (Get-FileHash -LiteralPath $manifestPath).Hash
  if ($index.protocol -cne 'foundations-audit-validation-v5' -or $index.schemaVersion -ne 5 -or
      $index.inputManifestSha256 -cne $manifestSha -or @($index.receipts).Count -ne 2) { throw 'V5 bundle index differs' }
  $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json -AsHashtable
  $catalogue = @(Get-ValidationCatalogueV5 $Root)
  Assert-InputManifestV5 $Root $manifest @($catalogue | Where-Object { $_.role -cne 'current-evidence' })
  $evidence = @($catalogue | Where-Object { $_.role -ceq 'current-evidence' -and $_.path -cne "$bundle/index.json" })
  if ($index.evidenceCount -ne $evidence.Count -or @($index.files).Count -ne $evidence.Count) { throw 'V5 evidence catalogue differs' }
  $files = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach ($entry in $index.files) {
    $null = Resolve-ValidationFileV5 $Root $entry.path
    if ($files.ContainsKey($entry.path) -or $entry.sha256 -cnotmatch '^[0-9A-F]{64}$') { throw 'Invalid or duplicate evidence digest' }
    $files.Add($entry.path,$entry)
  }
  foreach ($file in $evidence) {
    if (-not $files.ContainsKey($file.path)) { throw "Unindexed evidence: $($file.path)" }
    $entry = $files[$file.path]
    $path = Resolve-ValidationFileV5 $Root $file.path
    if ((Get-Item -LiteralPath $path -Force).Length -ne $entry.bytes -or
        (Get-FileHash -LiteralPath $path).Hash -cne $entry.sha256) { throw "V5 evidence changed: $($file.path)" }
  }
  foreach ($platform in @('Windows','Linux')) {
    $bound = @($index.receipts | Where-Object { $_.platform -ceq $platform })
    $path = "$bundle/$platform/receipt.json"
    if ($bound.Count -ne 1 -or $bound[0].path -cne $path -or
        (Get-FileHash -LiteralPath (Resolve-ValidationFileV5 $Root $path)).Hash -cne $bound[0].sha256) {
      throw "V5 indexed receipt differs: $platform"
    }
    $receipt = Get-Content -LiteralPath (Resolve-ValidationFileV5 $Root $path) -Raw | ConvertFrom-Json -AsHashtable
    if ($receipt.status -cne 'PASSED' -or $receipt.protocol -cne 'foundations-audit-validation-v5' -or
        $receipt.platform -cne $platform -or -not $receipt.inputsVerifiedBefore -or -not $receipt.inputsVerifiedAfter -or
        $receipt.inputManifest.path -cne "$bundle/inputs.json" -or $receipt.inputManifest.sha256 -cne $manifestSha -or
        $receipt.inputManifest.fileCount -ne $manifest.fileCount -or $receipt.versions.lean -notmatch 'version 4\.33\.1,' -or
        $receipt.sourceFiles -ne @($manifest.files | Where-Object { $_.role -ceq 'foundation-source' }).Count -or
        $receipt.migration.sources -ne @($manifest.files | Where-Object { $_.role -ceq 'migration-source' }).Count -or
        $receipt.axiomAudit -notmatch '^AUDIT_OK: \d+ declarations, zero axiom dependencies$' -or
        $receipt.protocolExpectedFailures -ne @($receipt.validationSteps | Where-Object { $_.expectedExit -cne 'zero' }).Count -or
        $receipt.totalExpectedFailures -ne ($receipt.foundationExpectedFailures + $receipt.migration.expectedFailures + $receipt.protocolExpectedFailures)) {
      throw "V5 receipt scope differs: $platform"
    }
    if (@(Compare-Object (Get-ValidationGatesV5 | Sort-Object) (@($receipt.validationSteps | ForEach-Object { $_.name }) | Sort-Object)).Count) {
      throw "V5 gate catalogue differs: $platform"
    }
    $runRoot = Resolve-ValidationFileV5 $Root "$bundle/$platform"
    $boundOutputs = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    $null = $boundOutputs.Add('receipt.json')
    foreach ($step in $receipt.validationSteps) {
      if (@($manifest.files | Where-Object { $_.path -ceq $step.source }).Count -ne 1 -or
          $step.expectedExit -cnotin @('zero','nonzero-type-mismatch','nonzero-forbidden-name','nonzero-shape') -or
          ($step.expectedExit -ceq 'zero' -and $step.exitCode -ne 0) -or
          ($step.expectedExit -cne 'zero' -and $step.exitCode -eq 0)) { throw "Invalid V5 gate: $($step.name)" }
      $log = Resolve-ValidationFileV5 $runRoot $step.log
      if (-not $boundOutputs.Add($step.log) -or (Get-FileHash -LiteralPath $log).Hash -cne $step.outputSha256 -or
          (Get-Content -LiteralPath $log -Raw) -notmatch $step.expectedPattern) { throw "V5 gate output differs: $platform/$($step.name)" }
    }
    foreach ($output in $receipt.additionalOutputs) {
      $file = Resolve-ValidationFileV5 $runRoot $output.path
      if (-not $boundOutputs.Add($output.path) -or (Get-FileHash -LiteralPath $file).Hash -cne $output.sha256) {
        throw "V5 internal output differs: $platform/$($output.path)"
      }
    }
    $platformFiles = @($evidence | Where-Object { $_.path.StartsWith("$bundle/$platform/",[StringComparison]::Ordinal) })
    if ($platformFiles.Count -ne $boundOutputs.Count) { throw "Unbound V5 run outputs: $platform" }
    foreach ($file in $platformFiles) {
      if (-not $boundOutputs.Contains($file.path.Substring("$bundle/$platform/".Length))) { throw 'Unbound V5 run output' }
    }
  }
  "VALIDATION_V5_BUNDLE_OK: $($manifest.fileCount) frozen inputs; $($index.evidenceCount) evidence files; Windows/Linux bindings verified"
}
