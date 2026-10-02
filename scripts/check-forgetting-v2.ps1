$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'ValidationManifestV2.ps1')
Assert-ValidationBundleV2 $projectRoot
