# Compatibility entry point for the migrated standalone project.
& (Join-Path $PSScriptRoot '../../scripts/verify-migration.ps1') @args
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
