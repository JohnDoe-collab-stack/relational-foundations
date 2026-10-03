param([string]$OutputPath = '')
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV4.ps1')
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$subject = Join-Path $root ('.lake/manifest-v4-tests/' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path (Join-Path $subject 'Tests') -Force | Out-Null
New-Item -ItemType Directory -Path (Join-Path $subject 'scripts') -Force | Out-Null
[IO.File]::WriteAllText((Join-Path $subject 'Tests/Small.lean'),'def value : Nat := 0')
[IO.File]::WriteAllText((Join-Path $subject 'scripts/check.ps1'),'exit 0')
$manifest = New-InputManifestV4 $subject @(Get-ValidationInputsV4 $subject)
$results = [Collections.Generic.List[object]]::new()
function Test-RejectionV4 {
  param([string]$Name,[scriptblock]$Action,[string]$Expected)
  $reason = ''
  try { & $Action } catch { $reason = $_.Exception.Message }
  if (-not $reason -or $reason -notmatch $Expected) { throw "V4 integrity test failed: $Name ($reason)" }
  $results.Add(@{name=$Name;verdict='REJECTED';reason=$reason})
}
Assert-InputManifestV4 $subject $manifest @(Get-ValidationInputsV4 $subject)
$results.Add(@{name='valid';verdict='ACCEPTED'})
foreach ($extra in @('Tests/.hidden.lean','Tests/.hidden.log','Tests/.notes.txt','Tests/ordinary.log','extra.lean','README.extra')) {
  $path = Join-Path $subject $extra
  [IO.File]::WriteAllText($path,'input')
  if ($IsWindows -and $extra -ceq 'Tests/.hidden.lean') { (Get-Item -LiteralPath $path -Force).Attributes = [IO.FileAttributes]::Hidden }
  Test-RejectionV4 "extra:$extra" { Assert-InputManifestV4 $subject $manifest @(Get-ValidationInputsV4 $subject) } 'catalogue differs|Unmanifested'
  Remove-Item -LiteralPath $path -Force
}
$source = Join-Path $subject 'Tests/Small.lean'
$saved = [IO.File]::ReadAllBytes($source)
[IO.File]::WriteAllText($source,'def value : Nat := 1')
Test-RejectionV4 'same-size-edit' { Assert-InputManifestV4 $subject $manifest @(Get-ValidationInputsV4 $subject) } 'input changed'
[IO.File]::WriteAllBytes($source,$saved)
Remove-Item -LiteralPath $source
Test-RejectionV4 'missing-file' { Assert-InputManifestV4 $subject $manifest @(Get-ValidationInputsV4 $subject) } 'catalogue differs'
[IO.File]::WriteAllBytes($source,$saved)
foreach ($attack in @('duplicate','case-collision','invalid-parent','invalid-absolute','role','digest','size')) {
  $changed = ($manifest | ConvertTo-Json -Depth 10 | ConvertFrom-Json -AsHashtable)
  switch ($attack) {
    'duplicate' { $changed.files += $changed.files[0]; $changed.fileCount++ }
    'case-collision' { $copy = $changed.files[0].Clone(); $copy.path = $copy.path.ToUpperInvariant(); $changed.files += $copy; $changed.fileCount++ }
    'invalid-parent' { $changed.files[0].path = '../outside' }
    'invalid-absolute' { $changed.files[0].path = '/outside' }
    'role' { $changed.files[0].role = 'invented' }
    'digest' { $changed.files[0].sha256 = '0' * 64 }
    'size' { $changed.files[0].bytes++ }
  }
  Test-RejectionV4 $attack { Assert-InputManifestV4 $subject $changed @(Get-ValidationInputsV4 $subject) } 'Duplicate|case-colliding|Invalid relative|role differs|input changed'
}
$link = Join-Path $subject 'linked'
if ($IsWindows) { New-Item -ItemType Junction -Path $link -Target (Join-Path $subject 'Tests') | Out-Null }
else { New-Item -ItemType SymbolicLink -Path $link -Target (Join-Path $subject 'Tests') | Out-Null }
Test-RejectionV4 'linked-directory' { Get-ValidationCatalogueV4 $subject | Out-Null } 'Linked validation entry'
Remove-Item -LiteralPath $link -Force
if (-not $IsWindows) {
  $case = Join-Path $subject 'tests'
  New-Item -ItemType Directory -Path $case | Out-Null
  Test-RejectionV4 'filesystem-case-collision' { Get-ValidationCatalogueV4 $subject | Out-Null } 'Case-colliding'
  Remove-Item -LiteralPath $case
} else {
  # Windows cannot create both casings in this directory; the manifest test above checks the same policy.
  $results.Add(@{name='filesystem-case-collision';verdict='PREVENTED_BY_FILESYSTEM'})
}
Assert-InputManifestV4 $subject $manifest @(Get-ValidationInputsV4 $subject)
if ($OutputPath) { @{protocol='manifest-v4-integrity-tests';status='PASSED';cases=@($results.ToArray())} |
  ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $OutputPath -Encoding utf8 }
"VALIDATION_MANIFEST_V4_TESTS_OK: $($results.Count) explicit cases; hidden/auxiliary inputs, collisions, links and byte integrity"
