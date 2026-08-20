# Asserts that every escape-hatch exhibit behaves as its header documents.
#
#   pwsh EscapeHatches/verify.ps1
#
# Unlike ../KernelDefects/, these files are SUPPOSED to work: each one is a
# sanctioned route to `False`, and the claim being checked is that the route is
# still open and that the audit reports what the file says it reports.
#
# Every Lean file carries its own `#guard_msgs` assertions, including the exact
# `#print axioms` output, so "lean exits 0" already means every documented
# message matched.  For Coq there is no `#guard_msgs`, so expected substrings
# are asserted here.
#
# Everything is compiled in a scratch directory outside the repository.

$ErrorActionPreference = 'Continue'
$root = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("escape-hatches-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $work -Force | Out-Null

Write-Host ("Lean:  " + ((& lean --version 2>&1) | Select-Object -First 1))
Write-Host ("Rocq:  " + ((& coqc --version 2>&1) | Select-Object -First 1))
Write-Host ""

$failures = 0

function Test-Case {
  param($Name, $Command, $Arguments, $Expect, $Needles)
  Push-Location $work
  $output = & $Command @Arguments 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location

  $accepted = ($code -eq 0)
  $verdictOk = ($accepted -eq ($Expect -eq 'accept'))
  $missing = @($Needles | Where-Object { $output -notmatch [regex]::Escape($_) })

  if ($verdictOk -and $missing.Count -eq 0) {
    Write-Host ("  OK    {0,-34} {1} (exit {2})" -f $Name, $Expect, $code)
  } else {
    $script:failures++
    Write-Host ("  FAIL  {0,-34} expected {1}, exit {2}" -f $Name, $Expect, $code) -ForegroundColor Red
    foreach ($m in $missing) { Write-Host ("        missing expected text: " + $m) -ForegroundColor Red }
    Write-Host (($output.Trim() -split "`n" | Select-Object -First 8) -join "`n")
  }
}

# --- Lean -------------------------------------------------------------------
# Each file's own `#guard_msgs` blocks assert the messages; exit 0 is the verdict.
$leanAccept = @(
  'Sorry', 'Axioms', 'Unsafe', 'NativeDecide', 'Metaprogramming', 'Misreading',
  'ArenaTrustedMetadata'
)
foreach ($m in $leanAccept) {
  Copy-Item (Join-Path $root "Lean/$m.lean") $work -Force
  Test-Case -Name "Lean/$m" -Command 'lean' -Arguments @("$m.lean") -Expect 'accept' -Needles @()
}

# The one Lean check that cannot live in a `#guard_msgs` block: a *parse* error.
Copy-Item (Join-Path $root 'Lean/Misreading.BareCyrillic.lean') $work -Force
Test-Case -Name 'Lean/Misreading.BareCyrillic' -Command 'lean' `
  -Arguments @('Misreading.BareCyrillic.lean') -Expect 'reject' -Needles @('expected token')

# --- Rocq -------------------------------------------------------------------
$coqCases = @(
  @{ Name = 'Coq/Assumptions'; File = 'Assumptions.v'; Flags = @();
     Needles = @('admitted_false : False',
                 'everything_inhabited : forall A : Type, A',
                 'strictly_bigger_obligation_1') },
  @{ Name = 'Coq/TypingFlags'; File = 'TypingFlags.v'; Flags = @();
     Needles = @('loop is assumed to be guarded.',
                 'Curry is assumed to be positive.',
                 'universe_false relies on an unsafe hierarchy.',
                 'check_guarded: true') },
  @{ Name = 'Coq/RewriteRules'; File = 'RewriteRules.v'; Flags = @('-allow-rewrite-rules');
     Needles = @('raise : forall A : Type, A',
                 'Rewrite rules are allowed (subject reduction might be broken)') },
  @{ Name = 'Coq/ImpredicativeSet'; File = 'ImpredicativeSet.v'; Flags = @('-impredicative-set');
     Needles = @('Set is impredicative', 'classic : forall P : Prop, P \/ ~ P') },
  @{ Name = 'Coq/ComputeMachines'; File = 'ComputeMachines.v'; Flags = @();
     Needles = @('Closed under the global context') },
  @{ Name = 'Coq/Misreading'; File = 'Misreading.v'; Flags = @();
     Needles = @('Closed under the global context',
                 'Relation.zero_is_one', 'Notated.looks_absurd') },
  # The two hatches of CATALOG.md 1.2 that leave no audit trace at all.
  # ORDER MATTERS: each *Downstream Requires the one above it.
  @{ Name = 'Coq/ExtractConstant'; File = 'ExtractConstant.v'; Flags = @();
     Needles = @('Closed under the global context',
                 'Extraction NoInline:', 'nth_safe', 'secret',
                 'Extraction Foreign Constant:') },
  @{ Name = 'Coq/ExtractConstantUnchecked'; File = 'ExtractConstantUnchecked.v'; Flags = @();
     Needles = @('Extraction NoInline:', 'flag', 'pick') },
  @{ Name = 'Coq/ExtractConstantDownstream'; File = 'ExtractConstantDownstream.v'; Flags = @();
     Needles = @('Closed under the global context', 'secret') },
  @{ Name = 'Coq/DeclareMLModule'; File = 'DeclareMLModule.v'; Flags = @();
     Needles = @('Closed under the global context', 'Loaded ML Modules:',
                 'rocq-runtime.plugins.derive') },
  @{ Name = 'Coq/DeclareMLModuleDownstream'; File = 'DeclareMLModuleDownstream.v'; Flags = @();
     Needles = @('Closed under the global context', 'rocq-runtime.plugins.derive') }
)
foreach ($c in $coqCases) {
  Copy-Item (Join-Path $root "Coq/$($c.File)") $work -Force
  Test-Case -Name $c.Name -Command 'coqc' -Arguments ($c.Flags + @($c.File)) `
    -Expect 'accept' -Needles $c.Needles
}

# Controls: the two flag-gated files must FAIL without their flag.
Test-Case -Name 'Coq/RewriteRules (no flag)' -Command 'coqc' -Arguments @('RewriteRules.v') `
  -Expect 'reject' -Needles @('requires passing the flag "-allow-rewrite-rules"')
Test-Case -Name 'Coq/ImpredicativeSet (no flag)' -Command 'coqc' -Arguments @('ImpredicativeSet.v') `
  -Expect 'reject' -Needles @('Cannot enforce Set+1 <= Set')

# --- Extraction: what the emitted OCaml actually says -----------------------
# Every assertion above this line is about what Rocq reports. These are about
# what Rocq WRITES OUT, which is where the cost of `Extract Constant` lands.
Write-Host ""
Write-Host "  -- extraction: the emitted OCaml ---------------------------------"

function Test-Emitted {
  param($Name, $File, $Needles)
  $path = Join-Path $work $File
  if (-not (Test-Path $path)) {
    $script:failures++
    Write-Host ("  FAIL  {0,-34} {1} was not emitted" -f $Name, $File) -ForegroundColor Red
    return
  }
  $text = Get-Content $path -Raw
  $missing = @($Needles | Where-Object { $text -notmatch [regex]::Escape($_) })
  if ($missing.Count -eq 0) {
    Write-Host ("  OK    {0,-34} emitted" -f $Name)
  } else {
    $script:failures++
    Write-Host ("  FAIL  {0,-34} emitted, wrong content" -f $Name) -ForegroundColor Red
    foreach ($m in $missing) { Write-Host ("        missing: " + $m) -ForegroundColor Red }
  }
}

Test-Emitted 'ExtractConstant emitted code'    'ExtractConstant_payload.ml' `
  @('let secret = true',
    'let nth_safe = (fun l i -> Some (try List.nth l i with _ -> 0))',
    '(<=) n (Stdlib.Int.succ n)')
Test-Emitted 'ExtractConstant junk'       'ExtractConstant_junk.ml' `
  @('let junk = let let let ( ( (')
Test-Emitted 'ExtractConstant arity'      'ExtractConstant_arity.ml' `
  @('let pick = (fun l i x -> None)')
Test-Emitted 'ExtractConstant shadow'     'ExtractConstant_shadow.ml' `
  @('let flag = false')
Test-Emitted 'ExtractConstant downstream' 'ExtractConstant_downstream.ml' `
  @('let secret = true')

Write-Host ""
Write-Host "  -- extraction: OCaml's verdict, and the running program ----------"

Copy-Item (Join-Path $root 'Coq/ExtractConstant.driver.ml') $work -Force
Test-Case -Name 'Coq/ExtractConstant driver' -Command 'ocamlfind' `
  -Arguments @('ocamlopt', 'ExtractConstant_payload.mli', 'ExtractConstant_payload.ml',
               'ExtractConstant.driver.ml', '-o', 'driver.exe') `
  -Expect 'accept' -Needles @()
Test-Case -Name 'Coq/ExtractConstant disagrees' `
  -Command (Join-Path $work 'driver.exe') -Arguments @() -Expect 'accept' `
  -Needles @('DISAGREES  secret_false             Coq: false    extracted: true',
             'DISAGREES  nth_safe_out_of_range    Coq: None     extracted: Some 0',
             'DISAGREES  grows_true               Coq: true     extracted: false',
             '3/3 disagreements')

# CONTROLS. The OCaml compiler is the only checker anywhere in this pipeline,
# and these are the two cases where it fires. `coqc` accepted both above --
# that gap between the two exit codes IS the exhibit.
Test-Case -Name 'Coq/ExtractConstant junk (control)' -Command 'ocamlfind' `
  -Arguments @('ocamlc', '-c', 'ExtractConstant_junk.mli', 'ExtractConstant_junk.ml') `
  -Expect 'reject' -Needles @('Error: Syntax error')
Test-Case -Name 'Coq/ExtractConstant arity (control)' -Command 'ocamlfind' `
  -Arguments @('ocamlc', '-c', 'ExtractConstant_arity.mli', 'ExtractConstant_arity.ml') `
  -Expect 'reject' -Needles @('does not match the interface')

Write-Host ""
Write-Host "  -- both hatches: coqchk has no opinion ---------------------------"

foreach ($m in @('ExtractConstant', 'DeclareMLModule')) {
  Test-Case -Name "Coq/$m coqchk" -Command 'coqchk' -Arguments @('-o', $m) `
    -Expect 'accept' `
    -Needles @('Modules were successfully checked',
               '* Axioms: <none>',
               '* Constants/Inductives relying on type-in-type: <none>',
               '* Constants/Inductives relying on unsafe (co)fixpoints: <none>',
               '* Inductives whose positivity is assumed: <none>')
}

# `Declare ML Module`'s own controls live inside DeclareMLModule.v as `Fail`
# commands (bad findlib package name; the command inside a Section), so that
# file's exit 0 already asserts both refusals.

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue

$total = $leanAccept.Count + 1 + $coqCases.Count + 2 + 5 + 4 + 2
Write-Host ""
if ($failures -eq 0) {
  Write-Host ("All {0} escape-hatch exhibits behaved as documented." -f $total)
  exit 0
} else {
  Write-Host ("{0} of {1} exhibits did NOT behave as documented." -f $failures, $total) -ForegroundColor Red
  exit 1
}
