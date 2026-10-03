$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path

function Test-ImportBoundaryGraph {
  param(
    [Parameter(Mandatory = $true)][string]$SourceRoot,
    [Parameter(Mandatory = $true)][string]$Manifest,
    [Parameter(Mandatory = $true)][string[]]$Files
  )

  $rootModule = $null
  $forbidden = @{}
  foreach ($rawLine in Get-Content -LiteralPath $Manifest) {
    $line = $rawLine.Trim()
    if ($line.Length -eq 0 -or $line.StartsWith("#")) { continue }
    $parts = $line -split '\s+', 2
    if ($parts.Count -ne 2) { throw ($Manifest + ": malformed boundary entry '$line'") }
    switch ($parts[0]) {
      "root" { $rootModule = $parts[1] }
      "forbidden" { $forbidden[$parts[1]] = $true }
      default { throw ($Manifest + ": unknown boundary entry '$($parts[0])'") }
    }
  }
  if (-not $rootModule) { throw ($Manifest + ": missing root entry") }

  $localModules = @{}
  $imports = @{}
  foreach ($file in $Files) {
    $relative = [IO.Path]::GetRelativePath($SourceRoot, $file)
    $moduleName = $relative.Substring(0, $relative.Length - 5).Replace('\', '.').Replace('/', '.')
    $localModules[$moduleName] = $true
    $imports[$moduleName] = [Collections.Generic.List[string]]::new()
    foreach ($line in Get-Content -LiteralPath $file) {
      if ($line -cmatch '^\s*import\s+(.+)$') {
        $targets = ($Matches[1] -split '--', 2)[0]
        foreach ($target in ($targets -split '\s+')) {
          if ($target) { $imports[$moduleName].Add($target) }
        }
      }
    }
  }
  if (-not $localModules.ContainsKey($rootModule)) {
    throw ($Manifest + ": root module '$rootModule' has no local source")
  }

  $queue = [Collections.Generic.Queue[string]]::new()
  $queue.Enqueue($rootModule)
  $visited = @{ $rootModule = $true }
  $paths = @{ $rootModule = $rootModule }
  while ($queue.Count -gt 0) {
    $current = $queue.Dequeue()
    foreach ($dependency in $imports[$current]) {
      if (-not $localModules.ContainsKey($dependency)) { continue }
      if ($forbidden.ContainsKey($dependency)) {
        throw "forbidden import path: $($paths[$current]) -> $dependency"
      }
      if (-not $visited.ContainsKey($dependency)) {
        $visited[$dependency] = $true
        $paths[$dependency] = "$($paths[$current]) -> $dependency"
        $queue.Enqueue($dependency)
      }
    }
  }
}

if ($args.Count -gt 0 -and $args[0] -eq "--self-test") {
  $fixture = Join-Path ([IO.Path]::GetTempPath()) ("rp-import-boundary-" + [guid]::NewGuid())
  New-Item -ItemType Directory -Path $fixture | Out-Null
  try {
    Set-Content -LiteralPath (Join-Path $fixture "Root.lean") -Value "import Middle" -NoNewline
    Set-Content -LiteralPath (Join-Path $fixture "Middle.lean") -Value "import Forbidden" -NoNewline
    Set-Content -LiteralPath (Join-Path $fixture "Forbidden.lean") -Value "/- fixture -/" -NoNewline
    Set-Content -LiteralPath (Join-Path $fixture "boundaries.txt") -Value @("root Root", "forbidden Forbidden")
    $fixtureFiles = Get-ChildItem -LiteralPath $fixture -File -Filter "*.lean" | Sort-Object FullName | ForEach-Object FullName
    $message = $null
    try {
      Test-ImportBoundaryGraph -SourceRoot $fixture -Manifest (Join-Path $fixture "boundaries.txt") -Files $fixtureFiles
    } catch {
      $message = $_.Exception.Message
    }
    $expected = "forbidden import path: Root -> Middle -> Forbidden"
    if ($message -ne $expected) {
      throw "indirect import-boundary self-test failed: $message"
    }

    Set-Content -LiteralPath (Join-Path $fixture "Root.lean") -Value "import Forbidden" -NoNewline
    $message = $null
    try {
      Test-ImportBoundaryGraph -SourceRoot $fixture -Manifest (Join-Path $fixture "boundaries.txt") -Files $fixtureFiles
    } catch {
      $message = $_.Exception.Message
    }
    $expected = "forbidden import path: Root -> Forbidden"
    if ($message -ne $expected) {
      throw "direct import-boundary self-test failed: $message"
    }
  } finally {
    Remove-Item -LiteralPath $fixture -Recurse -Force
  }
  exit 0
}

Push-Location $repoRoot
try {
  $files = @(Get-ChildItem -LiteralPath $repoRoot -Recurse -File -Filter '*.lean' | Where-Object {
    $_.FullName.Replace('\','/') -notlike '*/.lake/*' -and $_.FullName.Replace('\','/') -notlike '*/scripts/*'
  } | ForEach-Object FullName)
  $manifestArgument = if ($args.Count -gt 0) { $args[0] } else { "scripts/import-boundaries.txt" }
  $manifestPath = if ([IO.Path]::IsPathRooted($manifestArgument)) {
    $manifestArgument
  } else {
    Join-Path $repoRoot $manifestArgument
  }
  Test-ImportBoundaryGraph -SourceRoot $repoRoot -Manifest $manifestPath -Files $files
} finally {
  Pop-Location
}
