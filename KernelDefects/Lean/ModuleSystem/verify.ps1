# Reproduce and verify the module-boundary artifact.
#
#   pwsh KernelDefects/Lean/ModuleSystem/verify.ps1
#   pwsh KernelDefects/Lean/ModuleSystem/verify.ps1 -Toolchains v4.32.2,v4.33.0-rc1
#
# This one is a Lake PACKAGE rather than a loose module, because the defect only
# exists across a module boundary.  The package is copied to a scratch directory
# outside this repository before building, so it never joins any workspace here.
#
# Four things are asserted per toolchain, and the third and fourth are the ones
# that make the first mean anything:
#
#   Consumer  a SAFE `theorem Paradox : False` is accepted            (exit 0)
#   Audit     `#print axioms` reports nothing for all three theorems  (#guard_msgs)
#             and the imported `partialFalse` really is an axiom stub with
#             isUnsafe = false                                        (logError if not)
#   Control   the same `partial` definition used from a safe theorem in the SAME
#             module is REJECTED by the kernel                        (#guard_msgs)
#   leanchecker  rejects the built .olean — the audit is blind, the judge is not

[CmdletBinding()]
param(
  [string[]] $Toolchains = @('v4.32.2'),
  [switch]   $SkipLeanChecker
)

$ErrorActionPreference = 'Continue'
$src = Join-Path $PSScriptRoot 'paradox'

$failures = 0
foreach ($tc in $Toolchains) {
  Write-Output ""
  Write-Output "=================== $tc ==================="
  $w = Join-Path ([System.IO.Path]::GetTempPath()) ("shenanigans-modsys-" + [System.Guid]::NewGuid().ToString('N'))
  New-Item -ItemType Directory -Force -Path $w | Out-Null
  Copy-Item -Recurse (Join-Path $src '*') $w
  Remove-Item -Recurse -Force (Join-Path $w '.lake') -ErrorAction SilentlyContinue
  Set-Content -Path (Join-Path $w 'lean-toolchain') -Value "leanprover/lean4:$tc"
  Push-Location $w
  try {
    $out = & elan run "leanprover/lean4:$tc" lake build 2>&1
    if ($LASTEXITCODE -ne 0) {
      Write-Output "  !! lake build failed"; $out | Select-Object -Last 6 | ForEach-Object { "      $_" }; $failures++
      continue
    }
    Write-Output "  build       ok"

    foreach ($m in @(
        @{ f = 'Paradox/Consumer.lean'; why = 'a SAFE `theorem Paradox : False` is accepted' },
        @{ f = 'Paradox/Audit.lean';    why = '`#print axioms` reports nothing; stub is a safe axiom' },
        @{ f = 'Paradox/Control.lean';  why = 'same-module use is REJECTED by the kernel' })) {
      $o = & elan run "leanprover/lean4:$tc" lake lean $m.f 2>&1
      $ex = $LASTEXITCODE
      Write-Output ("  {0,-22} exit {1}   ({2})" -f (Split-Path $m.f -Leaf), $ex, $m.why)
      if ($ex -ne 0) { $o | Select-Object -First 6 | ForEach-Object { "      $_" }; $failures++ }
    }

    if (-not $SkipLeanChecker) {
      $env:LEAN_PATH = (Join-Path $w ".lake\build\lib\lean")
      $lc = & elan run "leanprover/lean4:$tc" leanchecker Paradox.Consumer 2>&1
      $lcex = $LASTEXITCODE
      $verdict = if ($lcex -eq 0) { 'ACCEPT' } else { 'reject' }
      Write-Output "  leanchecker            -> $verdict   (expect reject; it replays against the real environment)"
      $lc | Where-Object { $_ -match 'partial declaration' } | Select-Object -First 1 | ForEach-Object { "      $_" }
      # leanchecker only ships from v4.28.0; treat "could not run at all" as informational
      if ($verdict -eq 'ACCEPT') {
        Write-Output "  !! UNEXPECTED: leanchecker accepted a proof of False"; $failures++
      }
    }
  } finally {
    Pop-Location
    Remove-Item -Recurse -Force $w -ErrorAction SilentlyContinue
  }
}

Write-Output ""
if ($failures -eq 0) { Write-Output "The module-boundary artifact behaved as documented." }
else { Write-Output "$failures check(s) deviated from the documented behaviour." }
exit ([int]($failures -ne 0))
