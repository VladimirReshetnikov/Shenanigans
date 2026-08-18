# Reproduce and verify the non-transitive-def-eq artifacts.
#
#   pwsh KernelDefects/Lean/DefEq/verify.ps1
#   pwsh KernelDefects/Lean/DefEq/verify.ps1 -Toolchains v4.33.0,v4.34.0-rc1
#   pwsh KernelDefects/Lean/DefEq/verify.ps1 -SkipLeanChecker
#
# These modules are NOT `prelude` (they import `Lean`), so they get their own
# script rather than joining ../verify.ps1's loop, for the same reason
# ../Universes/verify.ps1 does: `leanchecker --fresh` on that closure re-checks
# the whole Lean library once per module.
#
# v4.33.0 is the floor.  `Environment.addDeclCore` gained a `maxRecDepth`
# parameter there, so on v4.31.0/v4.32.2 these files fail to ELABORATE (at
# `OfNat Declaration 8000`) without ever reaching the kernel.  That is an API
# change, not a change in the defect: upstream's arena tests, which bypass the
# frontend entirely, are accepted by the official kernel back to v4.28.0.
#
# Every expected outcome below is asserted.  The control is the load-bearing
# part — acceptance of an exhibit means something only because the same
# procedure on the same toolchain rejects the deliberately-broken twins.

[CmdletBinding()]
param(
  [string[]] $Toolchains = @('v4.33.0'),
  [switch]   $SkipLeanChecker
)

$ErrorActionPreference = 'Continue'
$env:LEAN_NUM_THREADS = '0'

$src  = $PSScriptRoot
$ctl  = Join-Path (Split-Path $PSScriptRoot -Parent) 'Controls'
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("shenanigans-defeq-" + [System.Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force -Path $work | Out-Null

# Each exhibit's `#guard_msgs` asserts BOTH that the kernel accepted its
# `False` AND that `#print axioms` reported nothing, so exit 0 is the assertion.
$exhibits = [ordered]@{
  'EquivManagerMissingIH' = 'lean4#14806 — recursor whose rule drops the IH'
  'EquivManagerStuckSort' = 'lean4#14806 + #14807 — stuck result sort, projected'
  'SubstStuckSort'        = 'lean4#14807 alone — no cache involved'
}

foreach ($m in $exhibits.Keys) { Copy-Item (Join-Path $src "$m.lean") $work }
Copy-Item (Join-Path $ctl 'DefEqCollisionControl.lean') $work

$failures = 0
Push-Location $work
try {
  foreach ($tc in $Toolchains) {
    Write-Output ""
    Write-Output "=================== $tc ==================="

    foreach ($m in $exhibits.Keys) {
      $out = & elan run "leanprover/lean4:$tc" lean --trust=0 "$m.lean" 2>&1
      $ex  = $LASTEXITCODE
      Write-Output "  exhibit  $m -> exit $ex   (expect 0: False accepted, audit clean)"
      Write-Output "           $($exhibits[$m])"
      if ($ex -ne 0) { $out | ForEach-Object { "      $_" }; $failures++ }
    }

    # The control's three `#guard_msgs` each assert `error: kernel error`, so
    # exit 0 means the kernel DID refuse all three broken twins.
    $out = & elan run "leanprover/lean4:$tc" lean --trust=0 DefEqCollisionControl.lean 2>&1
    $ex  = $LASTEXITCODE
    Write-Output "  control  DefEqCollisionControl -> exit $ex   (expect 0: all three refused)"
    if ($ex -ne 0) { $out | ForEach-Object { "      $_" }; $failures++ }
  }

  # Lean's own shipped judge, run once on the newest toolchain asked for.
  # Expected to ACCEPT: `leanchecker` shares Lean's kernel and is not an
  # independent verifier, so it inherits both defects.  The independent
  # checkers that do catch them are in the arena — see the report.
  #
  # Note the missing `--fresh`: these modules import `Lean`, so `--fresh` would
  # re-check that entire closure from an empty environment.
  if (-not $SkipLeanChecker) {
    $tc = $Toolchains[-1]
    Write-Output ""
    Write-Output "=================== leanchecker ($tc) ==================="
    $env:LEAN_PATH = $work
    $m = 'SubstStuckSort'
    & elan run "leanprover/lean4:$tc" lean -o "$m.olean" "$m.lean" 2>&1 |
      ForEach-Object { "  [lean] $_" }
    if ($LASTEXITCODE -ne 0) {
      Write-Output "  !! could not build the .olean"; $failures++
    } else {
      & elan run "leanprover/lean4:$tc" leanchecker $m 2>&1 |
        ForEach-Object { "  [leanchecker] $_" }
      $verdict = if ($LASTEXITCODE -eq 0) { 'accept' } else { 'reject' }
      Write-Output "  leanchecker -> $verdict   (expect accept: it shares Lean's own kernel)"
      if ($verdict -ne 'accept') { $failures++ }
    }
  }
} finally {
  Pop-Location
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Output ""
if ($failures -eq 0) { Write-Output "All non-transitive-def-eq artifacts behaved as documented." }
else { Write-Output "$failures check(s) deviated from the documented behaviour." }
exit ([int]($failures -ne 0))
