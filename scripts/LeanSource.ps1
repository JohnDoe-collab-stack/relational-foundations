function Remove-LeanComments {
  param([Parameter(Mandatory = $true)][string]$Source)
  $result = [Text.StringBuilder]::new($Source.Length)
  $index=0; $depth=0; $line=$false; $string=$false; $escaped=$false
  while ($index -lt $Source.Length) {
    $current=$Source[$index]
    $next=if($index+1 -lt $Source.Length){$Source[$index+1]}else{[char]0}
    if ($line) {
      if($current -eq "`n"){$line=$false; [void]$result.Append($current)}else{[void]$result.Append(' ')}
      $index++; continue
    }
    if ($depth -gt 0) {
      if($current -eq '/' -and $next -eq '-'){$depth++; [void]$result.Append('  '); $index+=2}
      elseif($current -eq '-' -and $next -eq '/'){$depth--; [void]$result.Append('  '); $index+=2}
      else{[void]$result.Append($(if($current -eq "`n"){"`n"}else{' '})); $index++}
      continue
    }
    if ($string) {
      [void]$result.Append($(if($current -eq "`n"){"`n"}else{' '}))
      if($escaped){$escaped=$false}elseif($current -eq '\'){$escaped=$true}elseif($current -eq '"'){$string=$false}
      $index++; continue
    }
    if($current -eq '-' -and $next -eq '-'){$line=$true; [void]$result.Append('  '); $index+=2}
    elseif($current -eq '/' -and $next -eq '-'){$depth=1; [void]$result.Append('  '); $index+=2}
    elseif($current -eq '"'){$string=$true; [void]$result.Append(' '); $index++}
    else{[void]$result.Append($current); $index++}
  }
  if($depth -ne 0 -or $string){throw 'Unterminated Lean comment or string'}
  $result.ToString()
}

function Get-LeanImports {
  param([Parameter(Mandatory = $true)][string]$Source)
  $code=Remove-LeanComments -Source $Source
  $pattern='(?m)^[ \t]*import[ \t]*(?:\r?\n[ \t]*)?([A-Z][A-Za-z0-9_'']*(?:\.[A-Za-z0-9_'']+)*(?:[ \t]+[A-Z][A-Za-z0-9_'']*(?:\.[A-Za-z0-9_'']+)*)*)'
  @([regex]::Matches($code,$pattern) | ForEach-Object { $_.Groups[1].Value -split '[ \t]+' })
}

function Test-LeanSourceParser {
  $sample=@'
/- import Forbidden.Comment /- import Forbidden.Nested -/ -/
-- import Forbidden.Line
import
  Init
import RelationalFoundations.History Tests.Separators
def text := "import Forbidden.String"
'@
  $actual=@(Get-LeanImports -Source $sample)
  if(($actual -join ',') -cne 'Init,RelationalFoundations.History,Tests.Separators') {
    throw 'Lean source parser self-test failed'
  }
}
