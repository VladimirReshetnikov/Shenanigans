# The kernel applies quotient computation rules to USER-declared constants.
#
#   pwsh KernelDefects/Lean/Quotient/verify.ps1
#   pwsh KernelDefects/Lean/Quotient/verify.ps1 -Toolchains v4.33.0,v4.33.1,v4.34.0-rc2
#
# `Kernel.Environment.quotInit` decides whether the kernel may fire
# `quot_reduce_rec`, and its own docstring promises what the flag means:
#
#     "When the flag is set, the type checker can assume that the `Quot`
#      declarations in the environment have indeed been added by the kernel and
#      not by the user."
#
# But the flag is not established, it is GUESSED -- `src/Lean/Environment.lean`:
#
#     quotInit := !imports.isEmpty  -- We assume `Init.Prelude` initializes quotient module
#
# A `prelude` module chain that never reaches `Init.Prelude` has a non-empty
# import list and has never run `init_quot`, so the flag is true while `Quot`,
# `Quot.mk` and `Quot.lift` are FREE NAMES.  `quot_reduce_rec` (src/kernel/quot.h)
# is keyed on exactly those names plus an arity, and does NO type checking:
#
#     expr const & f = args[arg_pos];
#     expr r = mk_app(f, app_arg(mk));       // Quot.lift .. f .. (Quot.mk _ _ a) ==> f a
#
# Two builds are asserted per toolchain, and the second is what makes the first
# mean anything:
#
#   EXHIBIT  named `Quot.mk` / `Quot.lift`  -> the kernel ACCEPTS `MyFalse`
#   CONTROL  the identical shapes, renamed  -> the kernel REJECTS it
#
# The proof is submitted as ONE self-contained term through
# `Kernel.Environment.addDeclCore`, into a FRESH environment, so no earlier
# declaration can have primed anything.  It uses no axiom and no `sorry`.

[CmdletBinding()]
param([string[]] $Toolchains = @('v4.33.1'))

$Toolchains = $Toolchains | ForEach-Object { $_ -split ',' } | Where-Object { $_ }

$ErrorActionPreference = 'Continue'
$here = $PSScriptRoot
$failures = 0

foreach ($tc in $Toolchains) {
  Write-Output "=============== $tc ==============="

  # `.olean` headers are toolchain-specific, so build in a per-toolchain dir.
  $work = Join-Path ([System.IO.Path]::GetTempPath()) ("quotfree-" + [System.Guid]::NewGuid().ToString('N').Substring(0,8))
  New-Item -ItemType Directory -Force -Path (Join-Path $work 'Q') | Out-Null

  & elan run "leanprover/lean4:$tc" lean --trust=0 -o (Join-Path $work 'Q/Base.olean') (Join-Path $here 'Q/Base.lean') 2>&1 |
    Where-Object { $_ -match 'error' } | ForEach-Object { Write-Output "  base: $_" }
  $env:LEAN_PATH = $work
  & elan run "leanprover/lean4:$tc" lean --trust=0 -o (Join-Path $work 'Q/Boom.olean') (Join-Path $here 'Q/Boom.lean') 2>&1 |
    Where-Object { $_ -match 'error' } | ForEach-Object { Write-Output "  boom: $_" }

  if (-not (Test-Path (Join-Path $work 'Q/Boom.olean'))) {
    Write-Output "  could not build the prelude modules on $tc -- skipping"
    Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
    continue
  }

  $out = & elan run "leanprover/lean4:$tc" lean --trust=0 (Join-Path $here 'exploit.lean') 2>&1 | Out-String
  $exhibit = ($out -split "`n" | Where-Object { $_ -match 'EXHIBIT' }) -join ''
  $control = ($out -split "`n" | Where-Object { $_ -match 'CONTROL' }) -join ''

  if ($exhibit -match 'ACCEPTED') {
    Write-Output '  exhibit   the kernel ACCEPTS a closed, axiom-free MyFalse'
  } else {
    Write-Output "  exhibit   UNEXPECTED -- expected the kernel to accept it"
    Write-Output "      $exhibit"
    $failures++
  }
  if ($control -match 'rejected') {
    Write-Output '  control   rejected, as it must be (the names are the whole difference)'
  } else {
    Write-Output "  control   UNEXPECTED -- the control must be rejected"
    Write-Output "      $control"
    $failures++
  }

  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Output ""
if ($failures -eq 0) {
  Write-Output "quotInit/quot_reduce_rec behaved as documented on: $($Toolchains -join ', ')"
  exit 0
} else {
  Write-Output "$failures assertion(s) failed. If the EXHIBIT is now rejected, the route is"
  Write-Output "closed and this directory becomes a regression witness."
  exit 1
}
