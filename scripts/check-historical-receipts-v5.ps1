param([Parameter(Mandatory)][string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$historical = Join-Path $OutputDirectory 'historical-99f0801'
$archive = Join-Path $OutputDirectory 'historical-99f0801.zip'
if (Test-Path -LiteralPath $historical) { throw 'Historical verification directory already exists' }
Push-Location $root
try {
  & git archive --format=zip --output=$archive 99f0801e0f91b6821944f8a4a09dedf7810fdf14
  if ($LASTEXITCODE -ne 0) { throw 'The historical 99f0801 object is required; use a full Git checkout' }
  Expand-Archive -LiteralPath $archive -DestinationPath $historical
  . (Join-Path $historical 'scripts/ValidationManifestV2.ps1')
  $null = Assert-ValidationBundleV2 $historical
  $oldManifest = Get-Content (Join-Path $historical 'docs/manifest-forgetting-v2.json') -Raw | ConvertFrom-Json
  foreach ($path in @('docs/manifest-forgetting-v2.json','docs/verification-forgetting-v2.json',
      'Migration/verification-forgetting-v2.json','docs/verification-forgetting-v1.json',
      'Migration/verification-forgetting-v1.json','docs/verification-result.json','Migration/verification-result.json')) {
    if ((Get-FileHash (Join-Path $root $path)).Hash -cne (Get-FileHash (Join-Path $historical $path)).Hash) {
      throw "Historical receipt has been modified: $path"
    }
  }
  $v4Archive = Join-Path $OutputDirectory 'historical-1887515.zip'
  $v4Root = Join-Path $OutputDirectory 'historical-1887515'
  & git archive --format=zip --output=$v4Archive 1887515c6321b0e99d86c843e0128b9db2099df0
  if ($LASTEXITCODE -ne 0) { throw 'The complete V4 snapshot 1887515 is required' }
  Expand-Archive -LiteralPath $v4Archive -DestinationPath $v4Root
  . (Join-Path $v4Root 'scripts/ValidationManifestV4.ps1')
  $null = Assert-ValidationBundleV4 $v4Root
  $historicalFiles = @(Get-ChildItem (Join-Path $v4Root 'docs/validation-v3'),(Join-Path $v4Root 'docs/validation-v4') -File -Recurse)
  foreach ($file in $historicalFiles) {
    $relative = [IO.Path]::GetRelativePath($v4Root,$file.FullName)
    if ((Get-FileHash -LiteralPath (Join-Path $root $relative)).Hash -cne (Get-FileHash -LiteralPath $file.FullName).Hash) {
      throw "Historical V3/V4 evidence changed: $relative"
    }
  }
  "HISTORICAL_RECEIPTS_V5_OK: V2 snapshot 99f0801 and V4 snapshot 1887515 independently verified; seven old receipts and $($historicalFiles.Count) V3/V4 evidence files unchanged"
} finally { Pop-Location }
