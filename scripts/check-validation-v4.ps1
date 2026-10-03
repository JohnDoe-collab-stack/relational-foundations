param([string]$Root = (Join-Path $PSScriptRoot '..'))
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV4.ps1')
Assert-ValidationBundleV4 ([IO.Path]::GetFullPath($Root))
