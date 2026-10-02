$ErrorActionPreference = "Stop"
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$manifest = Join-Path $PSScriptRoot "expected-failures.tsv"
$entries = [System.Collections.Generic.List[object]]::new()
$known = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
foreach ($line in Get-Content -LiteralPath $manifest) {
  if ([string]::IsNullOrWhiteSpace($line) -or $line.StartsWith('#')) { continue }
  $parts = $line.Split("`t")
  if ($parts.Count -ne 3 -or [string]::IsNullOrWhiteSpace($parts[2])) { throw "invalid expected-failure inventory row" }
  $fixture, $kind, $diagnostic = $parts
  if (-not $fixture.StartsWith('Tests/ExpectedFailure/') -or -not $fixture.EndsWith('.lean.fail') -or $fixture.Contains('..')) { throw "invalid fixture path: $fixture" }
  if (-not $known.Add($fixture)) { throw "duplicate fixture: $fixture" }
  if ($kind -cnotin @('privacy', 'dependent-type', 'semantic-type', 'termination')) { throw "unknown fixture category: $kind" }
  if (-not (Test-Path -LiteralPath (Join-Path $repoRoot $fixture) -PathType Leaf)) { throw "orphan fixture entry: $fixture" }
  $entries.Add([PSCustomObject]@{ Path=$fixture; Category=$kind; Diagnostic=$diagnostic })
}
$actual = @(Get-ChildItem -LiteralPath (Join-Path $repoRoot 'Tests/ExpectedFailure') -Recurse -File -Filter '*.lean.fail')
if ($entries.Count -eq 0) { throw "empty expected-failure inventory" }
foreach ($file in $actual) {
  $relative = [IO.Path]::GetRelativePath($repoRoot, $file.FullName).Replace('\','/')
  if (-not $known.Contains($relative)) { throw "uninventoried fixture: $relative" }
}
if ($actual.Count -ne $entries.Count) { throw "fixture inventory mismatch" }
Push-Location $repoRoot
try {
  foreach ($entry in $entries) {
    $output = @(& lake env lean $entry.Path 2>&1)
    $status = $LASTEXITCODE
    if ($status -eq 0) { throw "$($entry.Path): unexpectedly compiled" }
    if ($status -ge 124 -or $status -lt 0) { throw "$($entry.Path): interrupted or timed out ($status)" }
    $joined = $output -join "`n"
    if (-not $joined.Contains($entry.Diagnostic)) { throw "$($entry.Path): failed for an unexpected reason`n$joined" }
    Write-Output "EXPECTED_FAILURE_OK`t$($entry.Category)`t$($entry.Path)"
  }
} finally { Pop-Location }
Write-Output "Verified expected failures: $($entries.Count) fixtures, each executed once; privacy, dependent-type, semantic-type and termination remain distinct."
$global:LASTEXITCODE = 0
