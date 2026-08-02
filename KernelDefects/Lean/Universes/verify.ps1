# Reproduce and verify the universe-spelling artifacts.
#
#   pwsh KernelDefects/Lean/Universes/verify.ps1
#   pwsh KernelDefects/Lean/Universes/verify.ps1 -Toolchains v4.32.2,v4.33.0-rc1
#   pwsh KernelDefects/Lean/Universes/verify.ps1 -SkipLeanChecker
#
# These modules are NOT `prelude` (unlike ../Accelerators/), so they cannot join
# the sibling verify.ps1's loop: they import `Lean.CoreM`, and `leanchecker
# --fresh` on that closure re-checks the whole Lean library.  That run is done
# once here rather than once per module, and it is what -SkipLeanChecker turns
# off.
#
# Every expected outcome below is asserted.  The control is the load-bearing
# part: acceptance of the exhibit means something only because the same
# procedure on the same toolchain rejects the honestly-spelled twin.

[CmdletBinding()]
param(
  [string[]] $Toolchains = @('v4.32.2'),
  [switch]   $SkipLeanChecker
)

$ErrorActionPreference = 'Continue'
$env:LEAN_NUM_THREADS = '0'

$src  = $PSScriptRoot
$ctl  = Join-Path (Split-Path $PSScriptRoot -Parent) 'Controls'
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("shenanigans-universes-" + [System.Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force -Path $work | Out-Null

Copy-Item (Join-Path $src 'ImaxPropLaundering.lean') $work
Copy-Item (Join-Path $src 'MutualResultLevel.lean')  $work
Copy-Item (Join-Path $ctl 'ImaxPropControl.lean')    $work

# The measurement module's expected table, in order.  `master` after lean4#14615
# flips the two "alone" rows to ACCEPTED; no released toolchain does.
$expectedTable = @(
  'rejected  W : Sort (imax 1 0)                       -- alone'
  'rejected  W : Sort (max 0 0)                        -- alone'
  'ACCEPTED  W : Sort 0                                -- alone'
  'ACCEPTED  D : Sort 0        , W : Sort (imax 1 0)   -- laundered'
  'ACCEPTED  D : Sort 0        , W : Sort (max 0 0)    -- laundered'
  'rejected  D : Sort (imax 1 0), W : Sort 0           -- REVERSED'
  'rejected  D : Sort (max 0 0) , W : Sort 0           -- REVERSED'
)

$failures = 0
Push-Location $work
try {
  foreach ($tc in $Toolchains) {
    Write-Output ""
    Write-Output "=================== $tc ==================="

    # 1. The exhibit.  `#guard_msgs` inside the file asserts that `#print axioms`
    #    reports nothing for every `False` it proves, so exit 0 IS the assertion.
    $out = & elan run "leanprover/lean4:$tc" lean --trust=0 ImaxPropLaundering.lean 2>&1
    $ex  = $LASTEXITCODE
    Write-Output "  exhibit      lean --trust=0 -> exit $ex   (expect 0: False accepted, audit clean)"
    if ($ex -ne 0) { $out | ForEach-Object { "      $_" }; $failures++ }

    # 2. The control.  Its `#guard_msgs` asserts `(kernel) invalid projection`,
    #    so exit 0 means the kernel DID refuse the honestly-spelled projection.
    $out = & elan run "leanprover/lean4:$tc" lean --trust=0 ImaxPropControl.lean 2>&1
    $ex  = $LASTEXITCODE
    Write-Output "  control      lean --trust=0 -> exit $ex   (expect 0: projection refused)"
    if ($ex -ne 0) { $out | ForEach-Object { "      $_" }; $failures++ }

    # 3. The laundering measurement.
    $out = @(& elan run "leanprover/lean4:$tc" lean MutualResultLevel.lean 2>&1)
    $rows = @($out | Where-Object { $_ -match '^(ACCEPTED|rejected)' })
    Write-Output "  measurement  $($rows.Count) rows"
    if ($rows.Count -ne $expectedTable.Count) {
      Write-Output "  !! UNEXPECTED: got $($rows.Count) rows, expected $($expectedTable.Count)"
      $out | ForEach-Object { "      $_" }
      $failures++
    } else {
      $rowFailures = 0
      for ($i = 0; $i -lt $rows.Count; $i++) {
        if ($rows[$i].TrimEnd() -ne $expectedTable[$i]) {
          Write-Output "  !! UNEXPECTED row $i"
          Write-Output "       got      $($rows[$i])"
          Write-Output "       expected $($expectedTable[$i])"
          $rowFailures++
        }
      }
      $failures += $rowFailures
      if ($rowFailures -eq 0) { Write-Output "               all 7 rows as documented (incl. both REVERSED controls)" }
    }
  }

  # 4. Lean's own shipped judge, run once on the newest toolchain asked for.
  #    Expected to ACCEPT: `leanchecker` shares Lean's kernel and is not an
  #    independent verifier, so it inherits the defect.  `nanoda`, which is
  #    independent, rejects the construction (per lean4#14613's commit message).
  #
  #    Note the missing `--fresh`, unlike ../verify.ps1.  The exhibit imports
  #    `Lean.CoreM`, so `--fresh` re-checks that entire closure from an empty
  #    environment, which takes far longer than the rest of this script put
  #    together.  The plain form re-checks this module against its imports, which
  #    is the question that matters here — the defect is in the module, not in
  #    Lean's own oleans.
  if (-not $SkipLeanChecker) {
    $tc = $Toolchains[-1]
    Write-Output ""
    Write-Output "=================== leanchecker ($tc) ==================="
    $env:LEAN_PATH = $work
    & elan run "leanprover/lean4:$tc" lean -o ImaxPropLaundering.olean ImaxPropLaundering.lean 2>&1 |
      ForEach-Object { "  [lean] $_" }
    if ($LASTEXITCODE -ne 0) {
      Write-Output "  !! could not build the .olean"; $failures++
    } else {
      & elan run "leanprover/lean4:$tc" leanchecker ImaxPropLaundering 2>&1 |
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
if ($failures -eq 0) { Write-Output "All universe-spelling artifacts behaved as documented." }
else { Write-Output "$failures check(s) deviated from the documented behaviour." }
exit ([int]($failures -ne 0))
