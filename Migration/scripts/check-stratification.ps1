$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$manifestPath = Join-Path $repoRoot "scripts/stratification.tsv"

function Remove-LeanComments {
  param([Parameter(Mandatory = $true)][string]$Source)

  $result = [Text.StringBuilder]::new($Source.Length)
  $index = 0
  $blockDepth = 0
  $inLineComment = $false
  $inString = $false
  $escaped = $false
  while ($index -lt $Source.Length) {
    $current = $Source[$index]
    $next = if ($index + 1 -lt $Source.Length) { $Source[$index + 1] } else { [char]0 }

    if ($inLineComment) {
      if ($current -eq "`n") {
        [void]$result.Append($current)
        $inLineComment = $false
      } else {
        [void]$result.Append(' ')
      }
      $index += 1
      continue
    }

    if ($blockDepth -gt 0) {
      if ($current -eq '/' -and $next -eq '-') {
        [void]$result.Append(' ')
        [void]$result.Append(' ')
        $blockDepth += 1
        $index += 2
      } elseif ($current -eq '-' -and $next -eq '/') {
        [void]$result.Append(' ')
        [void]$result.Append(' ')
        $blockDepth -= 1
        $index += 2
      } else {
        [void]$result.Append($(if ($current -eq "`n") { "`n" } else { ' ' }))
        $index += 1
      }
      continue
    }

    if ($inString) {
      [void]$result.Append($current)
      if ($escaped) {
        $escaped = $false
      } elseif ($current -eq '\') {
        $escaped = $true
      } elseif ($current -eq '"') {
        $inString = $false
      }
      $index += 1
      continue
    }

    if ($current -eq '-' -and $next -eq '-') {
      [void]$result.Append(' ')
      [void]$result.Append(' ')
      $inLineComment = $true
      $index += 2
    } elseif ($current -eq '/' -and $next -eq '-') {
      [void]$result.Append(' ')
      [void]$result.Append(' ')
      $blockDepth = 1
      $index += 2
    } else {
      [void]$result.Append($current)
      if ($current -eq '"') { $inString = $true }
      $index += 1
    }
  }
  if ($blockDepth -ne 0) { throw "unterminated Lean block comment" }
  return $result.ToString()
}

function Get-LeanImports {
  param([Parameter(Mandatory = $true)][string]$Source)
  $withoutComments = Remove-LeanComments -Source $Source
  $pattern = '(?m)^[ \t]*import[ \t]*(?:\r?\n[ \t]*)?([A-Z][A-Za-z0-9_'']*(?:\.[A-Za-z0-9_'']+)*)'
  return @([regex]::Matches($withoutComments, $pattern) | ForEach-Object { $_.Groups[1].Value })
}

if ($args.Count -gt 0 -and $args[0] -eq "--self-test") {
  $fixture = @'
/- import Forbidden.Direct
   /- import Forbidden.Nested -/
-/
-- import Forbidden.Line
import
  Allowed.Split
/- a comment between commands -/
import Allowed.Direct -- import Forbidden.Trailing
'@
  $actual = @(Get-LeanImports -Source $fixture)
  $expected = @("Allowed.Split", "Allowed.Direct")
  if (($actual -join ',') -ne ($expected -join ',')) {
    throw "stratification parser self-test failed: $($actual -join ',')"
  }
  exit 0
}

$entries = @{}
$lineNumber = 0
foreach ($line in Get-Content -LiteralPath $manifestPath) {
  $lineNumber += 1
  if ($line.Length -eq 0 -or $line.StartsWith('#')) { continue }
  $parts = $line -split "`t", 4
  if ($parts.Count -ne 4) { throw "$manifestPath`:${lineNumber}: expected four tab-separated fields" }
  $module, $stratum, $status, $responsibility = $parts
  if ($entries.ContainsKey($module)) { throw "$manifestPath`:${lineNumber}: duplicate module $module" }
  if ($stratum -notin @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9')) {
    throw "$manifestPath`:${lineNumber}: unknown stratum $stratum"
  }
  if ($status -ne 'enforced') {
    throw "$manifestPath`:${lineNumber}: every production module must be enforced, found $status"
  }
  if ([string]::IsNullOrWhiteSpace($responsibility)) {
    throw "$manifestPath`:${lineNumber}: empty responsibility"
  }
  $entries[$module] = [pscustomobject]@{ Stratum = $stratum; Status = $status }
}

$relativeFiles = @(Get-ChildItem -LiteralPath $repoRoot -Recurse -File -Filter '*.lean' | Where-Object {
  $_.FullName -notlike '*\.lake\*' -and $_.FullName -notlike '*\Tests\*' -and $_.FullName -notlike '*\scripts\*'
} | ForEach-Object { [IO.Path]::GetRelativePath($repoRoot,$_.FullName).Replace('\','/') })
$filesByModule = @{}
$imports = @{}
foreach ($relative in $relativeFiles) {
  $module = $relative.Substring(0, $relative.Length - 5).Replace('\', '.').Replace('/', '.')
  $filesByModule[$module] = $relative
  $source = Get-Content -LiteralPath (Join-Path $repoRoot $relative) -Raw
  $imports[$module] = @(Get-LeanImports -Source $source)
}

$missing = @($filesByModule.Keys | Where-Object { -not $entries.ContainsKey($_) } | Sort-Object)
$stale = @($entries.Keys | Where-Object { -not $filesByModule.ContainsKey($_) } | Sort-Object)
if ($missing.Count -gt 0) { throw "unclassified production modules: $($missing -join ', ')" }
if ($stale.Count -gt 0) { throw "manifest modules without source: $($stale -join ', ')" }

$allowed = @{
  U = @('U')
  F = @('U','F')
  G = @('U','G')
  S = @('U','G','S')
  B = @('U','F','G','S','B')
  E = @('U','G','S','B','E')
  M = @('U','G','S','B','E','M')
  R = @('U','F','G','S','B','E','R')
  X = @('U','G','S','R','X')
  P = @('U','G','S','E','R','X','P')
  K = @('U','K')
  D = @('U','G','S','E','R','X','P','K','D')
  Q = @('U','F','G','S','B','E','M','R','X','P','K','D','Q')
  N = @('U','G','S','B','E','M','R','X','P','K','D','Q','N')
  A0 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N')
  A1 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0')
  A2 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1')
  A3 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2')
  A4 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3')
  A5 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4')
  A6 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5')
  A7 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6')
  A8 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7')
  A9 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8')
}

foreach ($root in ($entries.Keys | Sort-Object)) {
  $queue = [Collections.Generic.Queue[string]]::new()
  $queue.Enqueue($root)
  $paths = @{ $root = $root }
  while ($queue.Count -gt 0) {
    $current = $queue.Dequeue()
    foreach ($dependency in $imports[$current]) {
      if (-not $entries.ContainsKey($dependency)) { continue }
      $path = "$($paths[$current]) -> $dependency"
      if ($entries[$dependency].Stratum -notin $allowed[$entries[$current].Stratum]) {
        throw "forbidden stratification path ($($entries[$current].Stratum) -> $($entries[$dependency].Stratum)): $path"
      }
      if (-not $paths.ContainsKey($dependency)) {
        $paths[$dependency] = $path
        $queue.Enqueue($dependency)
      }
    }
  }
}

$publicRoots = @('SegmentedResidualRole','AbstractSegmentedTurning','ExactTypeTransport','StrongPerimetralTurning','RelationalPerimeter')
$reachable = @{}
$queue = [Collections.Generic.Queue[string]]::new()
foreach ($root in $publicRoots) {
  if (-not $entries.ContainsKey($root)) { throw "missing public root in manifest: $root" }
  $reachable[$root] = $true
  $queue.Enqueue($root)
}
while ($queue.Count -gt 0) {
  $current = $queue.Dequeue()
  foreach ($dependency in $imports[$current]) {
    if ($entries.ContainsKey($dependency) -and -not $reachable.ContainsKey($dependency)) {
      $reachable[$dependency] = $true
      $queue.Enqueue($dependency)
    }
  }
}
$orphans = @($entries.Keys | Where-Object { -not $reachable.ContainsKey($_) } | Sort-Object)
if ($orphans.Count -gt 0) { throw "production modules unreachable from public Lake roots: $($orphans -join ', ')" }

Write-Output "Verified stratification inventory: $($entries.Count) production modules, all enforced, no orphan."
