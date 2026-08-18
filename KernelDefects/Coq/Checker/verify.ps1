# Reproduce and verify the rocqchk VM-bytecode artifact (rocq#22352).
#
#   pwsh KernelDefects/Coq/Checker/verify.ps1
#
# This exhibit cannot join ../verify.ps1's one-file-per-coqc loop: the defect
# needs a hand-spliced object file, so the artifact is a build procedure rather
# than a .v file.  Everything it asserts is listed below, and the control is the
# load-bearing part -- acceptance of the exploit means something only because the
# same sources over an UNSPLICED Defs.vo are rejected.
#
# Asserted, in order:
#   1. two honest compilations of Defs.v, differing only in one constant's value,
#      agree byte-for-byte on `opaques` and `summary`  (splice.py checks this)
#   2. CONTROL: Evil.v over the honest Defs.vo is REJECTED by rocq c
#   3. Evil.v over the spliced Defs.vo is ACCEPTED, exit 0
#   4. Print Assumptions boom  ==  "Closed under the global context"
#   5. rocqchk -bytecode-compiler yes  on Evil      -> ACCEPTS
#   6. rocqchk (default)               on Evil      -> REJECTS, "Type error"
#   7. rocqchk BOTH modes              on Defs alone-> ACCEPT (the spliced file
#      is itself well typed; only its bytecode segment lies)
#   8. Downstream.v -- a plain `Require Import Evil` -- is ACCEPTED, its own
#      Print Assumptions is clean, and rocqchk -bytecode-compiler yes accepts it
#
# Needs `rocq`, `rocqchk` and `python` on PATH.  Measured on Rocq 9.2
# (vo_version 90299); upstream reports the defect present since 8.20.

$ErrorActionPreference = 'Stop'
$src  = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("rocqchk-vm-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $work -Force | Out-Null
New-Item -ItemType Directory -Path (Join-Path $work 'd1') -Force | Out-Null
New-Item -ItemType Directory -Path (Join-Path $work 'd2') -Force | Out-Null
New-Item -ItemType Directory -Path (Join-Path $work 'ctl') -Force | Out-Null

$version = (& coqc --version 2>&1 | Select-Object -First 1)
Write-Host "Toolchain: $version"
Write-Host ""

$failures = 0
function Check([string] $label, [bool] $ok, [string] $detail) {
  if ($ok) { Write-Host ("  [ok]   {0}" -f $label) }
  else { Write-Host ("  [FAIL] {0}" -f $label) -ForegroundColor Red; if ($detail) { Write-Host ("         {0}" -f $detail) }; $script:failures++ }
}

try {
  # --- 1. the two honest compilations -------------------------------------
  Copy-Item (Join-Path $src 'Defs.v') (Join-Path $work 'd1/Defs.v')
  (Get-Content (Join-Path $src 'Defs.v') -Raw).Replace('idb true', 'idb false') |
    Set-Content -NoNewline (Join-Path $work 'd2/Defs.v')

  foreach ($d in 'd1', 'd2') {
    Push-Location (Join-Path $work $d)
    & rocq c -boot -R . "" -noinit Defs.v 2>&1 | Out-Null
    $ok = ($LASTEXITCODE -eq 0)
    Pop-Location
    Check "honest compilation $d" $ok "rocq c failed in $d"
  }

  # --- splice ---------------------------------------------------------------
  Push-Location $work
  $spliceOut = & python (Join-Path $src 'splice.py') 'd1/Defs.vo' 'd2/Defs.vo' 'Defs.vo' 2>&1 | Out-String
  $spliceOk = ($LASTEXITCODE -eq 0)
  Pop-Location
  Check "splice library(d1) + vmlibrary(d2)" $spliceOk $spliceOut.Trim()
  if (-not $spliceOk) { throw "cannot continue without a spliced object file" }
  Write-Host ("         {0}" -f $spliceOut.Trim())

  Copy-Item (Join-Path $src 'Evil.v')       $work
  Copy-Item (Join-Path $src 'Downstream.v') $work

  # --- 2. CONTROL: the same sources over an honest Defs.vo ------------------
  Copy-Item (Join-Path $work 'd1/Defs.v')  (Join-Path $work 'ctl/Defs.v')
  Copy-Item (Join-Path $work 'd1/Defs.vo') (Join-Path $work 'ctl/Defs.vo')
  Copy-Item (Join-Path $src  'Evil.v')     (Join-Path $work 'ctl/Evil.v')
  Push-Location (Join-Path $work 'ctl')
  $ctl = & rocq c -boot -R . "" -noinit Evil.v 2>&1 | Out-String
  $ctlCode = $LASTEXITCODE
  Pop-Location
  Check "CONTROL: Evil.v over an UNSPLICED Defs.vo is rejected" `
    (($ctlCode -ne 0) -and ($ctl -match 'while it is expected to have type')) $ctl.Trim()

  # --- 3/4. the exploit and its audit ---------------------------------------
  Push-Location $work
  & rocq c -boot -R . "" -noinit Evil.v 2>&1 | Out-Null
  $evilOk = ($LASTEXITCODE -eq 0)
  Check "Evil.v over the SPLICED Defs.vo is accepted (exit 0)" $evilOk ""

  Set-Content (Join-Path $work 'Chk.v') "Require Import Evil.`nPrint Assumptions boom.`n"
  $audit = & rocq c -boot -R . "" -noinit Chk.v 2>&1 | Out-String
  Check "Print Assumptions boom == Closed under the global context" `
    ($audit -match 'Closed under the global context') $audit.Trim()

  # --- 5/6. the two checker modes disagree ----------------------------------
  $chkVm = & rocqchk -boot -bytecode-compiler yes -R . "" Evil 2>&1 | Out-String
  $chkVmCode = $LASTEXITCODE
  Check "rocqchk -bytecode-compiler yes ACCEPTS the False" `
    (($chkVmCode -eq 0) -and ($chkVm -match 'Modules were successfully checked')) ($chkVm | Select-Object -Last 1)

  $chkDef = & rocqchk -boot -R . "" Evil 2>&1 | Out-String
  $chkDefCode = $LASTEXITCODE
  Check "rocqchk (default) REJECTS it, with a type error" `
    (($chkDefCode -ne 0) -and ($chkDef -match 'Type error')) ($chkDef | Select-Object -Last 1)

  # --- 7. the spliced file is itself fine -----------------------------------
  $defsVm  = & rocqchk -boot -bytecode-compiler yes -R . "" Defs 2>&1 | Out-String
  $defsVmCode = $LASTEXITCODE
  $defsDef = & rocqchk -boot -R . "" Defs 2>&1 | Out-String
  $defsDefCode = $LASTEXITCODE
  Check "rocqchk accepts the spliced Defs ALONE in both modes" `
    (($defsVmCode -eq 0) -and ($defsDefCode -eq 0)) "vm=$defsVmCode default=$defsDefCode"

  # --- 8. the escape through a plain Require --------------------------------
  & rocq c -boot -R . "" -noinit Downstream.v 2>&1 | Out-Null
  $downOk = ($LASTEXITCODE -eq 0)
  Check "Downstream.v -- a plain Require -- is accepted" $downOk ""

  Set-Content (Join-Path $work 'Chk2.v') "Require Import Downstream.`nPrint Assumptions consequence.`nPrint Assumptions anything.`n"
  $audit2 = & rocq c -boot -R . "" -noinit Chk2.v 2>&1 | Out-String
  $clean2 = ([regex]::Matches($audit2, 'Closed under the global context')).Count
  Check "downstream Print Assumptions clean for both constants" ($clean2 -eq 2) $audit2.Trim()

  $chkDown = & rocqchk -boot -bytecode-compiler yes -R . "" Downstream 2>&1 | Out-String
  Check "rocqchk -bytecode-compiler yes accepts the downstream library too" `
    ($chkDown -match 'Modules were successfully checked') ($chkDown | Select-Object -Last 1)
  Pop-Location
} finally {
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Host ""
if ($failures -eq 0) { Write-Host "The rocqchk VM-bytecode artifact behaved as documented." }
else { Write-Host ("{0} check(s) deviated from the documented behaviour." -f $failures) -ForegroundColor Red }
exit ([int]($failures -ne 0))
