param([string]$Root = (Join-Path $PSScriptRoot '..'),[string]$OutputPath = '')
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV4.ps1')
$root = [IO.Path]::GetFullPath($Root)
$null = Assert-ValidationBundleV4 $root
$baseIndexHash = (Get-FileHash -LiteralPath (Resolve-ValidationFileV4 $root 'docs/validation-v4/index.json')).Hash
$subject = Join-Path ([IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))) ('.lake/bundle-v4-tests/' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $subject -Force | Out-Null
foreach ($entry in @(Get-ValidationCatalogueV4 $root)) {
  $target = Resolve-ValidationFileV4 $subject $entry.path
  New-Item -ItemType Directory -Path (Split-Path $target -Parent) -Force | Out-Null
  Copy-Item -LiteralPath (Resolve-ValidationFileV4 $root $entry.path) -Destination $target -Force
}
$null = Assert-ValidationBundleV4 $subject
$results = [Collections.Generic.List[object]]::new()
$results.Add(@{name='complete-real-bundle';verdict='ACCEPTED'})
function Test-BundleAttackV4 {
  param([string]$Name,[scriptblock]$Mutation,[scriptblock]$Restore,[string]$Expected)
  try {
    & $Mutation
    $reason = ''
    try { $null = Assert-ValidationBundleV4 $subject } catch { $reason = $_.Exception.Message }
    if (-not $reason -or $reason -notmatch $Expected) { throw "V4 real-bundle attack failed: $Name ($reason)" }
    $results.Add(@{name=$Name;verdict='REJECTED';reason=$reason})
  } finally { & $Restore }
  $null = Assert-ValidationBundleV4 $subject
}
foreach ($extra in @('Tests/.adversarial.lean','Tests/.adversarial.log','Tests/.adversarial.txt',
    'Tests/adversarial.log','adversarial.lean','notes.adversarial.txt',
    'docs/validation-v4/Windows/logs/.adversarial.txt','docs/validation-v4/Windows/extra.log',
    'docs/validation-v4/extra.lean')) {
  $file = Resolve-ValidationFileV4 $subject $extra
  Test-BundleAttackV4 "extra:$extra" {
    [IO.File]::WriteAllText($file,'extra')
    if ($IsWindows -and $extra -ceq 'Tests/.adversarial.lean') { (Get-Item -LiteralPath $file -Force).Attributes = [IO.FileAttributes]::Hidden }
  } { Remove-Item -LiteralPath $file -Force } 'catalogue differs|Unmanifested|Unindexed'
}
foreach ($path in @('RelationalFoundations/FiniteRuleCoordinates.lean','scripts/verify-validation-v4.ps1',
    'docs/validation-v4/Windows/logs/coordinate-consumers.txt','docs/validation-v4/Linux/receipt.json',
    'docs/validation-v3/index.json')) {
  $file = Resolve-ValidationFileV4 $subject $path
  $bytes = [IO.File]::ReadAllBytes($file)
  Test-BundleAttackV4 "same-size:$path" {
    $modified = [byte[]]$bytes.Clone()
    $modified[$modified.Length - 1] = $modified[$modified.Length - 1] -bxor 1
    [IO.File]::WriteAllBytes($file,$modified)
  } { [IO.File]::WriteAllBytes($file,$bytes) } 'changed|differs'
}
foreach ($path in @('Tests/FiniteRuleCoordinates.lean','docs/validation-v4/Linux/logs/coordinate-consumers.txt')) {
  $file = Resolve-ValidationFileV4 $subject $path
  $bytes = [IO.File]::ReadAllBytes($file)
  Test-BundleAttackV4 "missing:$path" { Remove-Item -LiteralPath $file } {
    [IO.File]::WriteAllBytes($file,$bytes)
  } 'catalogue differs'
}
$indexPath = Resolve-ValidationFileV4 $subject 'docs/validation-v4/index.json'
$originalIndex = [IO.File]::ReadAllBytes($indexPath)
foreach ($attack in @('source-binding','receipt-binding','duplicate-evidence','evidence-path-escape')) {
  Test-BundleAttackV4 $attack {
    $index = [Text.Encoding]::UTF8.GetString($originalIndex) | ConvertFrom-Json -AsHashtable
    switch ($attack) {
      'source-binding' { $index.inputManifestSha256 = '0' * 64 }
      'receipt-binding' { $index.receipts[0].sha256 = '0' * 64 }
      'duplicate-evidence' { $index.files[0] = $index.files[1].Clone() }
      'evidence-path-escape' { $index.files[0].path = '../outside' }
    }
    $index | ConvertTo-Json -Depth 15 | Set-Content -LiteralPath $indexPath -Encoding utf8
  } { [IO.File]::WriteAllBytes($indexPath,$originalIndex) } 'differs|duplicate|Invalid relative'
}
$link = Join-Path $subject 'linked'
Test-BundleAttackV4 'linked-directory' {
  if ($IsWindows) { New-Item -ItemType Junction -Path $link -Target (Join-Path $subject 'Tests') | Out-Null }
  else { New-Item -ItemType SymbolicLink -Path $link -Target (Join-Path $subject 'Tests') | Out-Null }
} { Remove-Item -LiteralPath $link -Force } 'Linked validation entry'
$null = Assert-ValidationBundleV4 $root
if ((Get-FileHash -LiteralPath (Resolve-ValidationFileV4 $root 'docs/validation-v4/index.json')).Hash -cne $baseIndexHash) {
  throw 'Original bundle index changed during adversarial tests'
}
if ($OutputPath) { @{protocol='complete-bundle-v4-integrity-tests-r2';status='PASSED';
  platform=$(if ($IsWindows) {'Windows'} else {'Linux'});inputIndexSha256=$baseIndexHash;cases=@($results.ToArray())} |
  ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $OutputPath -Encoding utf8 }
"VALIDATION_BUNDLE_V4_TESTS_OK: $($results.Count) explicit cases on the complete frozen source/evidence bundle"
