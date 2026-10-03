$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV3.ps1')
Assert-ValidationBundleV3 (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
