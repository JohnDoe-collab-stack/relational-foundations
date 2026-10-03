# Coverage supplement V4.1. The original V4 protocols and their runs keep their bytes.
param([string]$Root = (Join-Path $PSScriptRoot '..'),[string]$OutputPath = '')
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV4.ps1')
$root = [IO.Path]::GetFullPath($Root)
$null = Assert-ValidationBundleV4 $root
$indexHash = (Get-FileHash -LiteralPath (Resolve-ValidationFileV4 $root 'docs/validation-v4/index.json')).Hash
$subject = Join-Path ([IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))) ('.lake/bundle-v4-coverage/' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $subject -Force | Out-Null
$basicPath = if ($OutputPath) { $OutputPath + '.basic.json' } else { Join-Path $subject '.lake/basic-receipt.json' }
if (Test-Path -LiteralPath $basicPath) { throw 'The coverage supplement preserves previous test receipts' }
if ($OutputPath -and (Test-Path -LiteralPath $OutputPath)) { throw 'The output receipt already exists' }
New-Item -ItemType Directory -Path (Split-Path $basicPath -Parent) -Force | Out-Null
& (Join-Path $PSScriptRoot 'test-validation-bundle-v4-r2.ps1') -Root $root -OutputPath $basicPath
$basic = Get-Content -LiteralPath $basicPath -Raw | ConvertFrom-Json -AsHashtable
if ($basic.status -cne 'PASSED' -or $basic.inputIndexSha256 -cne $indexHash) { throw 'Basic bundle tests did not match this bundle' }
foreach ($entry in @(Get-ValidationCatalogueV4 $root)) {
  $target = Resolve-ValidationFileV4 $subject $entry.path
  New-Item -ItemType Directory -Path (Split-Path $target -Parent) -Force | Out-Null
  Copy-Item -LiteralPath (Resolve-ValidationFileV4 $root $entry.path) -Destination $target -Force
}
$results = [Collections.Generic.List[object]]::new()
function Test-CoverageAttackV4 {
  param([string]$Name,[scriptblock]$Mutation,[scriptblock]$Restore,[string]$Expected)
  try {
    & $Mutation
    $reason = ''
    try { $null = Assert-ValidationBundleV4 $subject } catch { $reason = $_.Exception.Message }
    if (-not $reason -or $reason -notmatch $Expected) { throw "V4.1 coverage test failed: $Name ($reason)" }
    $results.Add(@{name=$Name;verdict='REJECTED';reason=$reason})
  } finally { & $Restore }
  $null = Assert-ValidationBundleV4 $subject
}

foreach ($cache in @('.lake/probe.txt','Migration/.lake/probe.txt','Comparison/.lake/probe.txt','.git/probe.txt')) {
  $target = Resolve-ValidationFileV4 $subject $cache
  New-Item -ItemType Directory -Path (Split-Path $target -Parent) -Force | Out-Null
  [IO.File]::WriteAllText($target,'Excluded build cache or Git metadata')
}
$null = Assert-ValidationBundleV4 $subject
$results.Add(@{name='allowed-caches-and-git-metadata';verdict='ACCEPTED'})
foreach ($extra in @('scripts/.adversarial.ps1','Tests/VisibleAdded.lean','Tests/nested/deep/extra.txt')) {
  $file = Resolve-ValidationFileV4 $subject $extra
  New-Item -ItemType Directory -Path (Split-Path $file -Parent) -Force | Out-Null
  Test-CoverageAttackV4 "extra:$extra" {
    [IO.File]::WriteAllText($file,'Added ordinary input')
    if ($IsWindows -and $extra -ceq 'scripts/.adversarial.ps1') { (Get-Item -LiteralPath $file -Force).Attributes = [IO.FileAttributes]::Hidden }
  } { Remove-Item -LiteralPath $file -Force } 'catalogue differs|Unmanifested'
}
$oldName = Resolve-ValidationFileV4 $subject 'Tests/FiniteRuleCoordinates.lean'
$newName = Resolve-ValidationFileV4 $subject 'Tests/FiniteRuleCoordinates.renamed.lean'
Test-CoverageAttackV4 'rename-source' { Move-Item -LiteralPath $oldName -Destination $newName } {
  Move-Item -LiteralPath $newName -Destination $oldName
} 'Unmanifested|catalogue differs'
$internal = Resolve-ValidationFileV4 $subject 'docs/validation-v4/Windows/logs/migration-build.txt'
$internalBytes = [IO.File]::ReadAllBytes($internal)
Test-CoverageAttackV4 'same-size-internal-output' {
  $bytes = [byte[]]$internalBytes.Clone()
  $bytes[$bytes.Length - 1] = $bytes[$bytes.Length - 1] -bxor 1
  [IO.File]::WriteAllBytes($internal,$bytes)
} { [IO.File]::WriteAllBytes($internal,$internalBytes) } 'V4 evidence changed'

$manifestPath = Resolve-ValidationFileV4 $subject 'docs/validation-v4/inputs.json'
$indexPath = Resolve-ValidationFileV4 $subject 'docs/validation-v4/index.json'
$manifestBytes = [IO.File]::ReadAllBytes($manifestPath)
$indexBytes = [IO.File]::ReadAllBytes($indexPath)
foreach ($attack in @('manifest-role','manifest-duplicate','manifest-case-collision','manifest-parent',
    'manifest-absolute','manifest-digest','manifest-size')) {
  Test-CoverageAttackV4 $attack {
    $manifest = [Text.Encoding]::UTF8.GetString($manifestBytes) | ConvertFrom-Json -AsHashtable
    switch ($attack) {
      'manifest-role' { $manifest.files[0].role = 'invented-role' }
      'manifest-duplicate' { $manifest.files += $manifest.files[0].Clone(); $manifest.fileCount++ }
      'manifest-case-collision' {
        $copy = $manifest.files[0].Clone(); $copy.path = $copy.path.ToUpperInvariant()
        $manifest.files += $copy; $manifest.fileCount++
      }
      'manifest-parent' { $manifest.files[0].path = '../outside' }
      'manifest-absolute' { $manifest.files[0].path = '/outside' }
      'manifest-digest' { $manifest.files[0].sha256 = '0' * 64 }
      'manifest-size' { $manifest.files[0].bytes++ }
    }
    $manifest | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $manifestPath -Encoding utf8
    # Rebind the outer manifest digest to exercise the actual path/role/content checks.
    $index = [Text.Encoding]::UTF8.GetString($indexBytes) | ConvertFrom-Json -AsHashtable
    $index.inputManifestSha256 = (Get-FileHash -LiteralPath $manifestPath).Hash
    $index | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $indexPath -Encoding utf8
  } {
    [IO.File]::WriteAllBytes($manifestPath,$manifestBytes)
    [IO.File]::WriteAllBytes($indexPath,$indexBytes)
  } 'role differs|Duplicate|case-colliding|Invalid relative|input changed'
}

function Update-TestEvidenceDigestV4 {
  param([object]$Index,[string]$Relative)
  $file = Resolve-ValidationFileV4 $subject $Relative
  $entry = @($Index.files | Where-Object { $_.path -ceq $Relative })
  if ($entry.Count -ne 1) { throw 'Test evidence binding is ambiguous' }
  $entry[0].bytes = (Get-Item -LiteralPath $file -Force).Length
  $entry[0].sha256 = (Get-FileHash -LiteralPath $file).Hash
}
$receiptRelative = 'docs/validation-v4/Windows/receipt.json'
$receiptPath = Resolve-ValidationFileV4 $subject $receiptRelative
$receiptBytes = [IO.File]::ReadAllBytes($receiptPath)
foreach ($attack in @('old-receipt-as-v4','receipt-manifest-binding')) {
  Test-CoverageAttackV4 $attack {
    if ($attack -ceq 'old-receipt-as-v4') {
      Copy-Item -LiteralPath (Resolve-ValidationFileV4 $subject 'docs/validation-v3/Windows/receipt.json') -Destination $receiptPath -Force
    } else {
      $receipt = [Text.Encoding]::UTF8.GetString($receiptBytes) | ConvertFrom-Json -AsHashtable
      $receipt.inputManifest.sha256 = '0' * 64
      $receipt | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $receiptPath -Encoding utf8
    }
    $index = [Text.Encoding]::UTF8.GetString($indexBytes) | ConvertFrom-Json -AsHashtable
    Update-TestEvidenceDigestV4 $index $receiptRelative
    @($index.receipts | Where-Object { $_.platform -ceq 'Windows' })[0].sha256 = (Get-FileHash -LiteralPath $receiptPath).Hash
    $index | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $indexPath -Encoding utf8
  } {
    [IO.File]::WriteAllBytes($receiptPath,$receiptBytes)
    [IO.File]::WriteAllBytes($indexPath,$indexBytes)
  } 'V4 receipt scope differs'
}
$extraRelative = 'docs/validation-v4/Windows/unbound.txt'
$extraPath = Resolve-ValidationFileV4 $subject $extraRelative
Test-CoverageAttackV4 'indexed-output-without-receipt-binding' {
  [IO.File]::WriteAllText($extraPath,'Indexed but not produced by any recorded gate')
  $index = [Text.Encoding]::UTF8.GetString($indexBytes) | ConvertFrom-Json -AsHashtable
  $index.files += @{path=$extraRelative;bytes=(Get-Item -LiteralPath $extraPath).Length;sha256=(Get-FileHash -LiteralPath $extraPath).Hash}
  $index.evidenceCount++
  $index | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $indexPath -Encoding utf8
} {
  Remove-Item -LiteralPath $extraPath
  [IO.File]::WriteAllBytes($indexPath,$indexBytes)
} 'Unbound V4 run outputs'
if (-not $IsWindows) {
  $casePath = Join-Path $subject 'tests'
  Test-CoverageAttackV4 'filesystem-case-collision' { New-Item -ItemType Directory -Path $casePath | Out-Null } {
    Remove-Item -LiteralPath $casePath
  } 'Case-colliding validation path'
} else {
  $results.Add(@{name='filesystem-case-collision';verdict='PREVENTED_BY_FILESYSTEM';
    reason='The case-colliding manifest is rejected by the portable verifier on both platforms'})
}
$null = Assert-ValidationBundleV4 $root
if ((Get-FileHash -LiteralPath (Resolve-ValidationFileV4 $root 'docs/validation-v4/index.json')).Hash -cne $indexHash) {
  throw 'Original bundle index changed'
}
$allCases = @($basic.cases) + @($results.ToArray())
if ($OutputPath) { @{protocol='complete-bundle-v4-coverage-1';status='PASSED';
  platform=$(if ($IsWindows) {'Windows'} else {'Linux'});inputIndexSha256=$indexHash;
  basicReceiptSha256=(Get-FileHash -LiteralPath $basicPath).Hash;cases=$allCases} |
    ConvertTo-Json -Depth 12 | Set-Content -LiteralPath $OutputPath -Encoding utf8 }
"VALIDATION_BUNDLE_V4_COVERAGE_OK: $($allCases.Count) explicit real-bundle cases; frozen original restored; platform-specific case creation identified"
