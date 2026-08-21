# Measures `leanchecker`'s verdict on an axiom-free `False`.
#
#   pwsh Audits/Lean/Checkers/reducebool/verify.ps1
#
# CATALOG.md §4.7 said the Lean column of its checker table was empty "for a
# structural reason rather than a lucky one", on the grounds that the kernel's
# only compiled-code hook is `Lean.reduceBool` and `leanchecker` "cannot replay
# it at all".  Both halves are false on v4.33.0, and this measures both.
#
# Four modules, one construction.  The only difference between the accepted
# `False` and the rejected one is WHICH MODULE the evaluated constant lives in.
#
#   P.Base           the evaluated constant, in its own module   -> exit 0
#   P.Boom           `boom : False`, axiom-free, probe IMPORTED  -> exit 0  <-- the finding
#   P.Downstream     the same `False` across a plain `import`    -> exit 0
#   P.LocalControl   the same `False`, probe MODULE-LOCAL        -> exit 1  <-- the control
#
# The control's message is the evidence that `leanchecker` replays the hook
# rather than declining it:
#
#   uncaught exception: while replaying declaration 'rb_nativeL':
#   (kernel) (interpreter) unknown declaration 'probeL'
#
# It names the declaration it was replaying.  The interpreter it calls resolves
# imported constants and not constants local to the module under replay, so
# moving one definition to an imported module flips the verdict.
#
# Requires: elan, and the v4.33.0 toolchain.

[CmdletBinding()]
param()

$ErrorActionPreference = 'Continue'
$here = $PSScriptRoot
$toolchain = 'leanprover/lean4:v4.33.0'

Push-Location $here
try {
  Write-Output "== building (elan run $toolchain lake build) =="
  & elan run $toolchain lake build 2>&1 | Where-Object { $_ -notmatch '^trace' } | Out-String | Write-Output
  if ($LASTEXITCODE -ne 0) { Write-Output "BUILD FAILED"; exit 1 }

  $checker = Join-Path (Split-Path (& elan which lean)) 'leanchecker.exe'
  if (-not (Test-Path $checker)) {
    Write-Output "leanchecker not found at $checker -- skipping."
    exit 0
  }

  $env:LEAN_PATH = Join-Path $here '.lake/build/lib/lean'

  # module        -> expected exit code
  $expected = [ordered]@{
    'P.Base'         = 0
    'P.Boom'         = 0
    'P.Downstream'   = 0
    'P.LocalControl' = 1
  }

  $fail = 0
  Write-Output "== leanchecker verdicts =="
  foreach ($m in $expected.Keys) {
    $out  = & $checker $m 2>&1 | Out-String
    $code = $LASTEXITCODE
    $want = $expected[$m]
    $verdict = if ($code -eq 0) { 'ACCEPTED' } else { 'REJECTED' }
    if ($code -eq $want) {
      Write-Output ("  {0,-16} exit {1}  {2}  ok" -f $m, $code, $verdict)
    } else {
      Write-Output ("  {0,-16} exit {1}  {2}  MISMATCH (expected exit {3})" -f $m, $code, $verdict, $want)
      Write-Output ($out.Trim() -split "`n" | ForEach-Object { "      $_" })
      $fail++
    }
  }

  if ($fail -eq 0) {
    Write-Output ""
    Write-Output "All 4 as recorded: leanchecker accepts an axiom-free `False` when the"
    Write-Output "evaluated constant is imported, and refuses the identical construction"
    Write-Output "when it is module-local."
    exit 0
  } else {
    Write-Output ""
    Write-Output "$fail mismatch(es). If P.Boom now REJECTS, the checker gained the"
    Write-Output "ability to replay a module-under-check's own compiled code, and"
    Write-Output "CATALOG.md §4.7 should be revisited -- that is the intended signal."
    exit 1
  }
}
finally {
  Pop-Location
}
