$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV3.ps1')
$fixtureRoot = Join-Path ([IO.Path]::GetTempPath()) ('rp-validation-v3-' + [guid]::NewGuid())
New-Item -ItemType Directory -Path $fixtureRoot | Out-Null
$rejections = 0
function Assert-RejectedV3 {
  param([scriptblock]$Action, [string]$Diagnostic)
  $message = $null
  try { & $Action } catch { $message = $_.Exception.Message }
  if (-not $message -or -not $message.Contains($Diagnostic)) { throw "Integrity rejection failed: expected '$Diagnostic', got '$message'" }
  $script:rejections++
}
try {
  $source = Join-Path $fixtureRoot 'source.lean'
  $scriptFile = Join-Path $fixtureRoot 'verify.ps1'
  Set-Content -LiteralPath $source -Value 'AAAA' -NoNewline
  Set-Content -LiteralPath $scriptFile -Value 'BBBB' -NoNewline
  $inputs = @([pscustomobject]@{ path='source.lean'; role='foundation-source' },
    [pscustomobject]@{ path='verify.ps1'; role='validation-script' })
  $manifest = New-InputManifestV3 $fixtureRoot $inputs
  Assert-InputManifestV3 $fixtureRoot $manifest $inputs

  # Changed content of equal length must still invalidate the result.
  Set-Content -LiteralPath $source -Value 'AAAZ' -NoNewline
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest $inputs } 'Validation input changed: source.lean'
  Set-Content -LiteralPath $source -Value 'AAAA' -NoNewline
  Set-Content -LiteralPath $scriptFile -Value 'BBBZ' -NoNewline
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest $inputs } 'Validation input changed: verify.ps1'
  Set-Content -LiteralPath $scriptFile -Value 'BBBB' -NoNewline

  Remove-Item -LiteralPath $source
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest $inputs } 'Validation input missing: source.lean'
  Set-Content -LiteralPath $source -Value 'AAAA' -NoNewline
  $added = @($inputs) + @([pscustomobject]@{ path='extra.lean'; role='foundation-source' })
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest $added } 'Validation input catalogue differs'
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest @($inputs[0]) } 'Validation input catalogue differs'

  $duplicate = New-InputManifestV3 $fixtureRoot @($inputs[0],$inputs[0])
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $duplicate $inputs } 'Duplicate manifest path'
  Assert-RejectedV3 { Resolve-ValidationFileV3 $fixtureRoot '../escape.lean' } 'Invalid relative validation path'
  $alteredRole = @([pscustomobject]@{ path='source.lean'; role='validation-script' },$inputs[1])
  Assert-RejectedV3 { Assert-InputManifestV3 $fixtureRoot $manifest $alteredRole } 'Validation input role differs'

  New-Item -ItemType Directory -Path (Join-Path $fixtureRoot 'docs') | Out-Null
  $manifestFile = Join-Path $fixtureRoot 'docs/manifest-forgetting-v3.json'
  $manifest | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $manifestFile -Encoding utf8
  $link = @{ path='docs/manifest-forgetting-v3.json'; sha256=(Get-FileHash -LiteralPath $manifestFile -Algorithm SHA256).Hash; fileCount=2 }
  $null = Assert-ManifestLinkV3 $fixtureRoot $link
  Add-Content -LiteralPath $manifestFile -Value ' '
  Assert-RejectedV3 { $null = Assert-ManifestLinkV3 $fixtureRoot $link } 'Receipt-to-manifest digest differs'
  Assert-InputManifestV3 $fixtureRoot $manifest $inputs
  if ($rejections -ne 9) { throw 'Integrity test catalogue is incomplete' }
  "VALIDATION_MANIFEST_V3_TESTS_OK: valid input/link accepted; $rejections integrity rejections; equal-length source/script changes, missing/added files, duplicate/traversal/role and manifest-link corruption detected"
} finally {
  $resolvedFixture = [IO.Path]::GetFullPath($fixtureRoot)
  $tempPrefix = [IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
  if (-not $resolvedFixture.StartsWith($tempPrefix,[StringComparison]::OrdinalIgnoreCase) -or
      -not ([IO.Path]::GetFileName($resolvedFixture)).StartsWith('rp-validation-v3-')) {
    throw 'Refusing cleanup outside the dedicated validation fixture'
  }
  Remove-Item -LiteralPath $resolvedFixture -Recurse -Force
}
