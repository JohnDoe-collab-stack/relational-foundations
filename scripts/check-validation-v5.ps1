param([string]$Root = (Join-Path $PSScriptRoot '..'))
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'ValidationManifestV5.ps1')
Assert-ValidationBundleV5 ([IO.Path]::GetFullPath($Root))
