# Three blind spots in `Print Assumptions`, all live on the installed toolchain.
#
#   pwsh Audits/Coq/PrintAssumptions/verify.ps1
#
# Category (see ../../../README.md): **audit**.  No proof of `False` is produced
# here.  What is measured is that Rocq's own audit command answers a question
# about a constant with `Closed under the global context` when the honest answer
# names an axiom or a disabled kernel check.
#
# Each of the three is paired with a control that the same procedure reports
# CORRECTLY, so "the audit is silent" is a measurement rather than an absence.
#
#   1. rocq#21825 — the type of a definition is not traversed.  Live on every
#      released Coq/Rocq up to and including 9.2.0; the fix (merged 2026-03-26)
#      is carried only by the V9.3+rc1 prerelease.
#        ViaType.v       axiom in the TYPE      -> silent      (defect)
#                        axiom in the BODY      -> reported    (control)
#        GuardViaType.v  guard flag via TYPE    -> silent      (extension)
#        GuardViaBody.v  guard flag via BODY    -> reported    (control)
#      The extension is the part that matters: the same blind spot drops a
#      `bypass_check` flag, which CATALOG.md §1.4 asserts is always named.
#
#   2. rocq#20550 — `abstract` generates its side-effect constant with the
#      global typing flags, not the declaration's local ones.  `kind:
#      inconsistency`, fixed on master/v9.3 only, live on 9.2.0.
#        Abstract.v      with `abstract`        -> silent      (defect)
#                        without `abstract`     -> reported    (control)
#      Containment is measured too: `rocqchk` rejects the .vo.
#
#   3. rocq#22164 — `-impredicative-set` is invisible across a file boundary.
#      The SAME .vo files give two different audits depending on how the
#      reading session was invoked.
#        impred/         predicative reader     -> silent
#                        impredicative reader   -> `Set is impredicative`
#
# Needs `rocq` and `rocqchk` on PATH.

$ErrorActionPreference = 'Stop'
$src  = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("pa-blindspots-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $work -Force | Out-Null
New-Item -ItemType Directory -Path (Join-Path $work 'impred') -Force | Out-Null

$version = (& coqc --version 2>&1 | Select-Object -First 1)
Write-Host "Toolchain: $version"
Write-Host ""

$failures = 0
function Check([string] $label, [bool] $ok, [string] $detail) {
  if ($ok) { Write-Host ("  [ok]   {0}" -f $label) }
  else { Write-Host ("  [FAIL] {0}" -f $label) -ForegroundColor Red; if ($detail) { Write-Host ("         {0}" -f $detail) }; $script:failures++ }
}

try {
  Copy-Item (Join-Path $src '*.v') $work
  Copy-Item (Join-Path $src 'impred/*.v') (Join-Path $work 'impred')
  Push-Location $work

  # ---------------------------------------------------------------- 1 -------
  Write-Host "1. rocq#21825 — the type of a definition is not traversed"
  $out = & rocq c -R . "" ViaType.v 2>&1 | Out-String
  Check "ViaType.v compiles" ($LASTEXITCODE -eq 0) $out.Trim()
  # First answer is the defect, second is the control.
  $lines = @($out -split "`r?`n" | Where-Object { $_ -ne '' })
  Check "axiom in the TYPE  -> 'Closed under the global context'" `
    ($lines.Count -ge 1 -and $lines[0] -match 'Closed under the global context') ($out.Trim())
  Check "axiom in the BODY  -> reported (control)" `
    ($out -match 'ax3 : nat') ($out.Trim())

  $g1 = & rocq c -R . "" GuardViaType.v 2>&1 | Out-String
  Check "guard flag via TYPE -> silent" `
    (($LASTEXITCODE -eq 0) -and ($g1 -match 'Closed under the global context') -and ($g1 -notmatch 'assumed to be guarded')) $g1.Trim()
  $g2 = & rocq c -R . "" GuardViaBody.v 2>&1 | Out-String
  Check "guard flag via BODY -> 'loop is assumed to be guarded.' (control)" `
    (($LASTEXITCODE -eq 0) -and ($g2 -match 'assumed to be guarded')) $g2.Trim()

  # ---------------------------------------------------------------- 2 -------
  Write-Host ""
  Write-Host "2. rocq#20550 -- abstract loses the declarations typing flags"
  $a = & rocq c -R . "" Abstract.v 2>&1 | Out-String
  Check "Abstract.v compiles" ($LASTEXITCODE -eq 0) $a.Trim()
  $alines = @($a -split "`r?`n" | Where-Object { $_ -ne '' })
  Check "with abstract    -> Closed under the global context" `
    ($alines.Count -ge 1 -and $alines[0] -match 'Closed under the global context') $a.Trim()
  Check "without abstract -> relies on an unsafe hierarchy. (control)" `
    ($a -match 'relies on an unsafe hierarchy') $a.Trim()

  $chk = & rocqchk -R . "" -o Abstract 2>&1 | Out-String
  $chkCode = $LASTEXITCODE
  Check "CONTAINED: rocqchk rejects the .vo the local audit called clean" `
    ($chkCode -ne 0) ($chk | Select-Object -Last 1)

  # ---------------------------------------------------------------- 3 -------
  Write-Host ""
  Write-Host "3. rocq#22164 -- cross-file -impredicative-set is invisible"
  Push-Location (Join-Path $work 'impred')
  & rocq c -impredicative-set -R . "" prereq.v 2>&1 | Out-Null
  Check "prereq.v compiles WITH the flag" ($LASTEXITCODE -eq 0) ""

  $pre = & rocq c -R . "" consumer.v 2>&1 | Out-String
  $preCode = $LASTEXITCODE
  Check "predicative reader   -> silent for both constants" `
    (($preCode -eq 0) -and (([regex]::Matches($pre, 'Closed under the global context')).Count -eq 2)) $pre.Trim()

  $imp = & rocq c -impredicative-set -R . "" consumer.v 2>&1 | Out-String
  Check "impredicative reader -> 'Set is impredicative', SAME .vo" `
    ((([regex]::Matches($imp, 'Set is impredicative')).Count -eq 2)) $imp.Trim()
  # The in-file `Fail` is the control, and it is not vacuous: with the flag on,
  # the definition it guards SUCCEEDS, so `Fail` reports `The command has not
  # failed!` and this run exits non-zero.  That message is the assertion.
  Check "...and the in-file Fail control is not vacuous" `
    ($imp -match 'The command has not failed') $imp.Trim()
  Pop-Location
  Pop-Location
} finally {
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Host ""
if ($failures -eq 0) { Write-Host "All Print Assumptions blind spots behaved as documented." }
else { Write-Host ("{0} measurement(s) deviated from the documented behaviour." -f $failures) -ForegroundColor Red }
exit ([int]($failures -ne 0))
