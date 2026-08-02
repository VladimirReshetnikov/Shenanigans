# Asserts that every Coq exhibit in this directory behaves as its header
# documents on the installed toolchain.
#
#   pwsh KernelDefects/Coq/verify.ps1
#
# Most exhibits here are proofs of False on an AFFECTED toolchain that are fixed
# upstream, so they must be REJECTED on a current one: acceptance signals a
# regression.  ModuleSystem/UniverseFlagDesync is the exception — rocq#22287 is
# OPEN, so it must be ACCEPTED, and its companion Import case must be rejected.
# The paradoxes moved to ../../Paradoxes/ and are checked by
# ../../Paradoxes/verify.ps1.

$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("coq-shenanigans-" + [guid]::NewGuid().ToString('N').Substring(0,8))
New-Item -ItemType Directory -Path $work -Force | Out-Null

$version = (& coqc --version 2>&1 | Select-Object -First 1)
Write-Host "Toolchain: $version"
Write-Host ""

# name; relative path; expected 'accept' or 'reject'; substring required in output
$cases = @(
  @{ Name = 'GuardChecker/HigherOrderFixpoint';  Path = 'GuardChecker/HigherOrderFixpoint.v';  Expect = 'reject'; Needle = 'Recursive definition of russell is ill-formed' },
  @{ Name = 'GuardChecker/NestedMutualCrossCall';Path = 'GuardChecker/NestedMutualCrossCall.v';Expect = 'reject'; Needle = 'Recursive definition of F is ill-formed' },
  @{ Name = 'GuardChecker/UniformArgsLet';       Path = 'GuardChecker/UniformArgsLet.v';       Expect = 'reject'; Needle = 'Recursive definition of F_let is ill-formed' },
  @{ Name = 'ModuleSystem/AliasChainDeltaResolver'; Path = 'ModuleSystem/AliasChainDeltaResolver.v'; Expect = 'reject'; Needle = 'Unable to unify' },
  # rocq#22287 is OPEN: this one must be ACCEPTED, with a clean audit, and coqchk
  # must reject the .vo it produces.  Ordered before the Import case, which needs
  # that .vo to exist.
  @{ Name = 'ModuleSystem/UniverseFlagDesync';      Path = 'ModuleSystem/UniverseFlagDesync.v';      Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'reject' },
  @{ Name = 'ModuleSystem/UniverseFlagDesyncImport';Path = 'ModuleSystem/UniverseFlagDesyncImport.v';Expect = 'reject'; Needle = 'Universe inconsistency' }
)

$failures = 0
foreach ($c in $cases) {
  $src = Join-Path $root $c.Path
  $dst = Join-Path $work ([System.IO.Path]::GetFileName($c.Path))
  Copy-Item $src $dst -Force

  Push-Location $work
  $output = & coqc ([System.IO.Path]::GetFileName($c.Path)) 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location

  $accepted = ($code -eq 0)
  $wantAccept = ($c.Expect -eq 'accept')
  $verdictOk = ($accepted -eq $wantAccept)
  $needleOk = $output -match [regex]::Escape($c.Needle)

  # For the open case, the independent checker's verdict is half the finding.
  $chkOk = $true
  if ($c.ContainsKey('Coqchk')) {
    Push-Location $work
    $null = & coqchk -silent ([System.IO.Path]::GetFileNameWithoutExtension($c.Path)) 2>&1
    $chkCode = $LASTEXITCODE
    Pop-Location
    $chkVerdict = if ($chkCode -eq 0) { 'accept' } else { 'reject' }
    $chkOk = ($chkVerdict -eq $c.Coqchk)
    if (-not $chkOk) {
      Write-Host ("        coqchk expected {0}, got {1}" -f $c.Coqchk, $chkVerdict) -ForegroundColor Red
    }
  }

  if ($verdictOk -and $needleOk -and $chkOk) {
    $suffix = if ($c.ContainsKey('Coqchk')) { " (coqchk $($c.Coqchk)s)" } else { "" }
    Write-Host ("  OK    {0,-38} {1} (exit {2}){3}" -f $c.Name, $c.Expect, $code, $suffix)
  } else {
    $failures++
    Write-Host ("  FAIL  {0,-38} expected {1}, exit {2}" -f $c.Name, $c.Expect, $code) -ForegroundColor Red
    if (-not $needleOk) { Write-Host ("        missing expected text: " + $c.Needle) -ForegroundColor Red }
    Write-Host ($output.Trim() -split "`n" | Select-Object -First 6 | Out-String)
  }
}

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue

Write-Host ""
if ($failures -eq 0) {
  Write-Host ("All {0} Coq exhibits behaved as documented." -f $cases.Count)
  exit 0
} else {
  Write-Host ("{0} of {1} exhibits did NOT behave as documented." -f $failures, $cases.Count) -ForegroundColor Red
  exit 1
}
