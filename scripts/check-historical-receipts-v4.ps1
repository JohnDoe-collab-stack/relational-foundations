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
  "HISTORICAL_RECEIPTS_V4_OK: $($oldManifest.fileCount) V2 input hashes match public snapshot 99f0801; seven historical manifest/receipt files unchanged"
} finally { Pop-Location }
