# Measures `nanoda`'s verdict on the universe-spelling defect this repository
# ships an exhibit for — rather than citing it.
#
#   pwsh Audits/Lean/Checkers/verify.ps1
#
# CATALOG.md §2.5 and §3.0 state that `nanoda` "decides all three semantically",
# and lean4#14613's commit message says "`nanoda` rejects it".  Both are
# citations.  This script measures them, and it measures the case that actually
# matters here: not the honest `Sort 0` spelling that nanoda's own regression
# test uses, but the NON-NORMAL `Sort (imax 1 0)` spelling that
# ../../../KernelDefects/Lean/Universes/ turns into an axiom-free `False` on
# every released Lean toolchain.
#
# Three cases, and the first is what makes the other two mean anything:
#
#   control    a well-formed export                     -> ACCEPT
#   honest     nanoda's own ProjFromProp test, Sort 0    -> reject
#   non-normal  the same with Sort (imax 1 0)             -> reject
#
# The non-normal export is DERIVED here from nanoda's own test resource by a
# single-line edit, rather than vendored, so the provenance stays visible and
# their file stays theirs (Apache-2.0).
#
# Requires: cargo, and the Upstream/nanoda_lib submodule checked out.

[CmdletBinding()]
param([switch] $SkipBuild)

$ErrorActionPreference = 'Continue'
$repo    = (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$nanoda  = Join-Path $repo 'Upstream/nanoda_lib'
$srcDir  = Join-Path $nanoda 'test_resources/ProjFromProp'

if (-not (Test-Path (Join-Path $srcDir 'export'))) {
  Write-Output "Upstream/nanoda_lib is not checked out (git submodule update --init). Skipping."
  exit 0
}

$bin = Join-Path $nanoda 'target/release/nanoda_bin.exe'
if (-not $SkipBuild -or -not (Test-Path $bin)) {
  Write-Output "Building nanoda (cargo build --release) ..."
  Push-Location $nanoda
  & cargo build --release 2>&1 | Select-Object -Last 2
  Pop-Location
}
if (-not (Test-Path $bin)) { Write-Output "  !! nanoda did not build"; exit 1 }

$work = Join-Path ([System.IO.Path]::GetTempPath()) ("nanoda-check-" + [guid]::NewGuid().ToString('N').Substring(0,8))
New-Item -ItemType Directory -Force -Path (Join-Path $work 'nonnormal') | Out-Null
New-Item -ItemType Directory -Force -Path (Join-Path $work 'control')   | Out-Null
New-Item -ItemType Directory -Force -Path (Join-Path $work 'honest')    | Out-Null

# --- derive the non-normal export -------------------------------------------
# `Wrap`'s type in nanoda's resource is `{"ie":14,"sort":0}` — the honest,
# syntactic `Prop`.  Replace it with `Sort (imax 1 0)`, which denotes `Prop` and
# is the spelling the released Lean kernel reads as "not a proposition".
$lines  = Get-Content (Join-Path $srcDir 'export')
$edited = foreach ($l in $lines) {
  if ($l.Trim() -eq '{"ie":14,"sort":0}') {
    '{"il":3,"succ":0}'                 # level 3 = 1
    '{"il":4,"imax":[3,0]}'             # level 4 = imax 1 0, which denotes 0
    '{"ie":14,"sort":4}'                # Wrap : Sort (imax 1 0)
  } else { $l }
}
if (($edited -join "`n") -eq ($lines -join "`n")) {
  Write-Output "  !! the anchor line {""ie"":14,""sort"":0} was not found — nanoda's resource changed"
  exit 1
}
Set-Content -Path (Join-Path $work 'nonnormal/export') -Value $edited
Copy-Item (Join-Path $nanoda 'test_resources/Empty/export') (Join-Path $work 'control/export')
# Run nanoda's own resource under OUR config too, so all three cases are driven
# identically and a rejection can only be a type error, never a missing file.
Copy-Item (Join-Path $srcDir 'export') (Join-Path $work 'honest/export')

function Write-Config($dir) {
  Set-Content -Path (Join-Path $work "$dir/config.json") -Value @'
{
  "export_file_path": "export",
  "permitted_axioms": [],
  "unpermitted_axiom_hard_error": true,
  "print_success_message": true,
  "pp_to_stdout": false
}
'@
}
Write-Config 'nonnormal'; Write-Config 'control'; Write-Config 'honest'

# --- run --------------------------------------------------------------------
$cases = @(
  @{ Name = 'control   (well-formed export)';          Dir = Join-Path $work 'control'; Expect = 'accept' },
  @{ Name = "honest    (nanoda's own, Sort 0)";        Dir = Join-Path $work 'honest'; Expect = 'reject' },
  @{ Name = 'non-normal (Sort (imax 1 0))';             Dir = Join-Path $work 'nonnormal'; Expect = 'reject' }
)

$failures = 0
foreach ($c in $cases) {
  Push-Location $c.Dir
  $out  = & $bin 'config.json' 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location
  $verdict = if ($code -eq 0) { 'accept' } else { 'reject' }
  if ($verdict -eq $c.Expect) {
    Write-Output ("  OK    {0,-36} {1} (exit {2})" -f $c.Name, $verdict, $code)
  } else {
    $failures++
    Write-Output ("  FAIL  {0,-36} expected {1}, got {2} (exit {3})" -f $c.Name, $c.Expect, $verdict, $code)
    Write-Output (($out.Trim() -split "`n" | Select-Object -First 4) -join "`n")
  }
  if ($verdict -eq 'reject') {
    $why = ($out -split "`n" | Where-Object { $_ -match 'panicked at|Error' } | Select-Object -First 1)
    if ($why) { Write-Output ("        " + $why.Trim()) }
    # A rejection is only evidence if it is a TYPE error. Anything else — a
    # missing file, a parse failure — is the harness misreporting.
    if ($out -notmatch 'infer_proj prop') {
      $failures++
      Write-Output "        !! rejected, but NOT with 'infer_proj prop' — this is not a type error"
    }
  }
}

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue
Write-Output ""
if ($failures -eq 0) { Write-Output "nanoda behaved as documented on all 3 cases." ; exit 0 }
else { Write-Output "$failures case(s) deviated." ; exit 1 }
