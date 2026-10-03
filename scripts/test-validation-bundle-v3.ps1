$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV3.ps1')
$sourceRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$fixtureRoot = Join-Path ([IO.Path]::GetTempPath()) ('rp-validation-v3-bundle-' + [guid]::NewGuid())
$null = Assert-ValidationBundleV3 $sourceRoot
New-Item -ItemType Directory -Path $fixtureRoot | Out-Null
$rejections = 0
function Assert-BundleRejectedV3 {
  param([string]$Diagnostic)
  $message = $null
  try { $null = Assert-ValidationBundleV3 $fixtureRoot } catch { $message = $_.Exception.Message }
  if (-not $message -or -not $message.Contains($Diagnostic)) { throw "Bundle corruption escaped: $Diagnostic; received: $message" }
  $script:rejections++
}
try {
  foreach ($inputFile in @(Get-ValidationInputsV3 $sourceRoot)) {
    $target = Resolve-ValidationFileV3 $fixtureRoot $inputFile.path
    New-Item -ItemType Directory -Path (Split-Path $target -Parent) -Force | Out-Null
    Copy-Item -LiteralPath (Resolve-ValidationFileV3 $sourceRoot $inputFile.path) -Destination $target
  }
  Copy-Item -LiteralPath (Join-Path $sourceRoot 'docs/validation-v3') -Destination (Join-Path $fixtureRoot 'docs/validation-v3') -Recurse
  $null = Assert-ValidationBundleV3 $fixtureRoot
  $receipt = Join-Path $fixtureRoot 'docs/validation-v3/Windows/receipt.json'
  $savedReceipt = [IO.File]::ReadAllBytes($receipt)
  Add-Content -LiteralPath $receipt -Value ' '
  Assert-BundleRejectedV3 'V3 indexed receipt digest differs'
  [IO.File]::WriteAllBytes($receipt,$savedReceipt)
  $log = Join-Path $fixtureRoot 'docs/validation-v3/Windows/logs/forgetting-syntax-and-semantics.txt'
  $savedLog = [IO.File]::ReadAllBytes($log)
  Add-Content -LiteralPath $log -Value ' '
  Assert-BundleRejectedV3 'V3 output differs'
  [IO.File]::WriteAllBytes($log,$savedLog)
  $internal = Join-Path $fixtureRoot 'docs/validation-v3/Linux/logs/migration-build.txt'
  $savedInternal = [IO.File]::ReadAllBytes($internal)
  Add-Content -LiteralPath $internal -Value ' '
  Assert-BundleRejectedV3 'V3 internal output differs'
  [IO.File]::WriteAllBytes($internal,$savedInternal)
  $manifest = Join-Path $fixtureRoot 'docs/validation-v3/inputs.json'
  $savedManifest = [IO.File]::ReadAllBytes($manifest)
  Add-Content -LiteralPath $manifest -Value ' '
  Assert-BundleRejectedV3 'V3 bundle index differs'
  [IO.File]::WriteAllBytes($manifest,$savedManifest)
  $null = Assert-ValidationBundleV3 $fixtureRoot
  if ($rejections -ne 4) { throw 'Bundle corruption catalogue is incomplete' }
  "VALIDATION_V3_BUNDLE_TESTS_OK: valid complete bundle accepted; four receipt/manifest/gate-log/internal-output corruptions rejected"
} finally {
  $resolvedFixture = [IO.Path]::GetFullPath($fixtureRoot)
  $tempPrefix = [IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
  if (-not $resolvedFixture.StartsWith($tempPrefix,[StringComparison]::OrdinalIgnoreCase) -or
      -not ([IO.Path]::GetFileName($resolvedFixture)).StartsWith('rp-validation-v3-bundle-')) {
    throw 'Refusing cleanup outside the dedicated bundle fixture'
  }
  Remove-Item -LiteralPath $resolvedFixture -Recurse -Force
}
