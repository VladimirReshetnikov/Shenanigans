# Asserts that every Coq exhibit in this directory behaves as its header
# documents on the installed toolchain.
#
#   pwsh KernelDefects/Coq/verify.ps1
#
# Some exhibits here are proofs of False on an AFFECTED toolchain that are fixed
# upstream, so they must be REJECTED on a current one: acceptance signals a
# regression.  Two are LIVE and must be ACCEPTED instead:
#   ModuleSystem/UniverseFlagDesync  rocq#22287, OPEN.  coqchk REJECTS it, and
#                                    its companion Import case is rejected too.
#   GuardChecker/WrongEnvReduction   rocq#21839, fixed in 9.2.1 — but the
#                                    installed toolchain is 9.2.0, inside the
#                                    affected range.  coqchk ACCEPTS it, and so
#                                    does its Escape half.  That combination is
#                                    unique in this repository.
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
  @{ Name = 'GuardChecker/UniformArgsHiddenSelfCall'; Path = 'GuardChecker/UniformArgsHiddenSelfCall.v'; Expect = 'reject'; Needle = 'Recursive definition of F2 is ill-formed' },
  @{ Name = 'ModuleSystem/WithDefUniverses';       Path = 'ModuleSystem/WithDefUniverses.v';       Expect = 'reject'; Needle = 'universe inconsistency' },
  @{ Name = 'Conversion/RegisterInlineVM';         Path = 'Conversion/RegisterInlineVM.v';         Expect = 'reject'; Needle = 'while it is expected to have type' },
  # rocq#22287 is OPEN: this one must be ACCEPTED, with a clean audit, and coqchk
  # must reject the .vo it produces.  Ordered before the Import case, which needs
  # that .vo to exist.
  # rocq#21839 is fixed in 9.2.1 but the installed toolchain is 9.2.0, inside the
  # affected range — so this one is LIVE, and it is the only exhibit here that
  # BOTH `Print Assumptions` and `coqchk` report nothing about.  Ordered before
  # its Escape half, which needs the .vo.
  @{ Name = 'GuardChecker/WrongEnvReduction';       Path = 'GuardChecker/WrongEnvReduction.v';       Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'GuardChecker/WrongEnvReductionEscape'; Path = 'GuardChecker/WrongEnvReductionEscape.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'ModuleSystem/UniverseFlagDesync';      Path = 'ModuleSystem/UniverseFlagDesync.v';      Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'reject' },
  @{ Name = 'ModuleSystem/UniverseFlagDesyncImport';Path = 'ModuleSystem/UniverseFlagDesyncImport.v';Expect = 'reject'; Needle = 'Universe inconsistency' },
  # rocq#22366 is OPEN: `Unset Guard Checking` is not attributed through a
  # functor application with `Parameter Inline`, so the audit goes silent.  The
  # exhibit must be ACCEPTED with a clean audit and rejected by rocqchk; the
  # controls must be accepted and must NAME the flag, which is what isolates the
  # defect to the `Inline` token.
  @{ Name = 'ModuleSystem/GuardFlagThroughFunctor';        Path = 'ModuleSystem/GuardFlagThroughFunctor.v';        Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'reject' },
  @{ Name = 'ModuleSystem/GuardFlagThroughFunctorControls';Path = 'ModuleSystem/GuardFlagThroughFunctorControls.v';Expect = 'accept'; Needle = 'assumed to be guarded' },

  # ------------------------------------------------------------------------
  # The 2026-08-20 wave.  Nine kind:inconsistency issues reported to Rocq's
  # maintainers by OpenAI and credited in the issue bodies to "an LLM and
  # @dselsam".  Every exhibit below is OPEN upstream with an unmerged fix, so
  # each must be ACCEPTED here, with a clean audit, and -- unlike #22287 and
  # #22366 -- `coqchk` must ACCEPT them too.  That combination was unique to
  # rocq#21839 until this wave; it is not any more, which is what
  # Conversion/AuditBlindSextet.v measures.
  #
  # Order matters: an Escape/Require/Sextet case needs its exhibit's .vo, and
  # the harness copies each file into one flat scratch directory in list order.
  # ------------------------------------------------------------------------
  @{ Name = 'Conversion/LetinRelevanceShift'; Path = 'Conversion/LetinRelevanceShift.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'Conversion/LetinRelevanceShiftControls'; Path = 'Conversion/LetinRelevanceShiftControls.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/LetinRelevanceShiftEscape'; Path = 'Conversion/LetinRelevanceShiftEscape.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'CoFixGuard/CofixWrongEnvRectree'; Path = 'CoFixGuard/CofixWrongEnvRectree.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'CoFixGuard/CofixWrongEnvRectreeControls'; Path = 'CoFixGuard/CofixWrongEnvRectreeControls.v'; Expect = 'accept'; Needle = 'assumed to be guarded' },
  @{ Name = 'CoFixGuard/CofixWrongEnvRectreeEscape'; Path = 'CoFixGuard/CofixWrongEnvRectreeEscape.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'CoFixGuard/NestedMutualCofixRectree'; Path = 'CoFixGuard/NestedMutualCofixRectree.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'CoFixGuard/NestedMutualCofixRectreeControls'; Path = 'CoFixGuard/NestedMutualCofixRectreeControls.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'GuardChecker/UniformArgsLetBinder'; Path = 'GuardChecker/UniformArgsLetBinder.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'GuardChecker/UniformArgsLetBinderControls'; Path = 'GuardChecker/UniformArgsLetBinderControls.v'; Expect = 'reject'; Needle = 'Recursive definition of russell_zeta is ill-formed' },
  @{ Name = 'GuardChecker/UniformArgsLetBinderRequire'; Path = 'GuardChecker/UniformArgsLetBinderRequire.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'ModuleSystem/LetinOrderSubtyping'; Path = 'ModuleSystem/LetinOrderSubtyping.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'ModuleSystem/LetinParamSubtyping'; Path = 'ModuleSystem/LetinParamSubtyping.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'reject' },
  @{ Name = 'ModuleSystem/LetinOrderSubtypingControls'; Path = 'ModuleSystem/LetinOrderSubtypingControls.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'ModuleSystem/LetinOrderSubtypingEscape'; Path = 'ModuleSystem/LetinOrderSubtypingEscape.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'ModuleSystem/LetinOrderSubtypingUnsealed'; Path = 'ModuleSystem/LetinOrderSubtypingUnsealed.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Universes/LetinVarianceInference'; Path = 'Universes/LetinVarianceInference.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' },
  @{ Name = 'Universes/LetinVarianceInferenceControls'; Path = 'Universes/LetinVarianceInferenceControls.v'; Expect = 'accept'; Needle = 'let hidden :=' },
  @{ Name = 'Universes/LetinVarianceInferenceEscape'; Path = 'Universes/LetinVarianceInferenceEscape.v'; Expect = 'accept'; Needle = 'Closed under the global context' },

  # AuditBlindSextet.v is the file that falsifies CATALOG.md section 4.1's claim
  # that rocq#21839 is "the only one" both audits miss and that escapes a plain
  # Require.  It must come last: it Requires the six exhibits above it.
  @{ Name = 'Conversion/AuditBlindLetinConv'; Path = 'Conversion/AuditBlindLetinConv.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindCofixEnv'; Path = 'Conversion/AuditBlindCofixEnv.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindNestedCofix'; Path = 'Conversion/AuditBlindNestedCofix.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindUniformArgs'; Path = 'Conversion/AuditBlindUniformArgs.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindCumulLetin'; Path = 'Conversion/AuditBlindCumulLetin.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindSubtypeLetin'; Path = 'Conversion/AuditBlindSubtypeLetin.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindStuckCase'; Path = 'Conversion/AuditBlindStuckCase.v'; Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'Conversion/AuditBlindUipControl'; Path = 'Conversion/AuditBlindUipControl.v'; Expect = 'accept'; Needle = 'relies on definitional UIP' },
  @{ Name = 'Conversion/AuditBlindControls'; Path = 'Conversion/AuditBlindControls.v'; Expect = 'accept'; Needle = '' },
  @{ Name = 'Conversion/AuditBlindSextet'; Path = 'Conversion/AuditBlindSextet.v'; Expect = 'accept'; Needle = 'Closed under the global context'; Coqchk = 'accept' }
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
