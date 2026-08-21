# Asserts lean4#14875 on every toolchain given.
#
#   pwsh KernelDefects/Lean/ModuleSystem/classrec/verify.ps1
#   pwsh KernelDefects/Lean/ModuleSystem/classrec/verify.ps1 -Toolchains v4.32.2,v4.33.0,v4.33.1,v4.34.0-rc1,v4.34.0-rc2
#
# A `public class inductive`'s generated recursor keeps a reference to a
# declaration the producer saw only through `import all`.  That dependency is
# dropped from the producer's EXPORTED view, so a downstream module may bind the
# same global name to something else -- and the recursor, checked against the
# original, is then interpreted against the replacement.
#
# Five things are asserted, and the last two are what make the first three mean
# something:
#
#   1. the exhibit builds                                        exit 0
#   2. `boom : False` reports NO axioms        (asserted in-file by #guard_msgs)
#   3. `leanchecker` REJECTS the consumer      -- the cross-check does hold here
#   4. CONTROL `import all` -> `import`: the producer stops building
#   5. CONTROL withdraw the redefinition: `Unknown constant `ClassHidden``
#
# Control 5 is the finding stated as a measurement: with the redefinition gone
# the name is not visible to the consumer at all, which is exactly the claim
# that the exported view omits a dependency the exported recursor still has.

[CmdletBinding()]
param([string[]] $Toolchains = @('v4.33.1'))

# `pwsh -File script.ps1 -Toolchains a,b,c` hands the whole list over as ONE
# string, unlike calling the script from inside PowerShell.  Split defensively so
# both invocations behave the same.
$Toolchains = $Toolchains | ForEach-Object { $_ -split ',' } | Where-Object { $_ }

$ErrorActionPreference = 'Continue'
$here = $PSScriptRoot
$failures = 0

function Build-In([string] $dir, [string] $tc) {
  Push-Location $dir
  try {
    if (Test-Path '.lake') { Remove-Item -Recurse -Force '.lake' }
    Set-Content -Path (Join-Path $dir 'lean-toolchain') -Value "leanprover/lean4:$tc"
    $out = & elan run "leanprover/lean4:$tc" lake build 2>&1 | Out-String
    return @{ Code = $LASTEXITCODE; Out = $out }
  } finally { Pop-Location }
}

foreach ($tc in $Toolchains) {
  Write-Output "=============== $tc ==============="

  # 1 + 2 -- the exhibit.  #print axioms is asserted inside ClassConsumer.lean,
  # so a clean build IS the audit assertion.
  $r = Build-In $here $tc
  if ($r.Code -eq 0) {
    Write-Output '  exhibit                 exit 0    (boom : False, #guard_msgs asserts no axioms)'
  } else {
    Write-Output "  exhibit                 exit $($r.Code)  UNEXPECTED -- expected it to build"
    Write-Output ($r.Out.Trim() -split "`n" | Select-Object -Last 6 | ForEach-Object { "      $_" })
    $failures++
  }

  # 3 -- leanchecker must reject.  Resolve it through `elan run` for the
  # toolchain UNDER TEST, not through `elan which`, which answers for the
  # default toolchain: a v4.33.1 checker reading a v4.34.0-rc2 `.olean` fails
  # with `incompatible header`, which is a harness artefact and not a verdict.
  $env:LEAN_PATH = Join-Path $here '.lake/build/lib/lean'
  $co = & elan run "leanprover/lean4:$tc" leanchecker 'IS.ClassConsumer' 2>&1 | Out-String
  $ccode = $LASTEXITCODE
  if ($ccode -ne 0 -and $co -match 'already been declared') {
    Write-Output "  leanchecker             reject    (constant has already been declared 'ClassHidden')"
  } else {
    Write-Output "  leanchecker             exit $ccode  UNEXPECTED -- expected a rejection"
    Write-Output ($co.Trim() -split "`n" | Select-Object -Last 4 | ForEach-Object { "      $_" })
    $failures++
  }

  # 4 + 5 -- the controls, each built in its own scratch copy.
  $controls = @(
    @{ Name = 'control: plain `import`'; File = 'IS/ClassProducer.lean'
       From = 'import all IS.ClassHidden'; To = 'import IS.ClassHidden'
       Needle = 'type mismatch' }
    @{ Name = 'control: no redefinition'; File = 'IS/ClassConsumer.lean'
       From = 'public inductive ClassHidden : Prop where'; To = '-- redefinition withdrawn'
       Needle = "Unknown constant" }
  )

  foreach ($c in $controls) {
    $work = Join-Path ([System.IO.Path]::GetTempPath()) ("classrec-" + [System.Guid]::NewGuid().ToString('N').Substring(0,8))
    Copy-Item -Recurse -Force $here $work
    if (Test-Path (Join-Path $work '.lake')) { Remove-Item -Recurse -Force (Join-Path $work '.lake') }
    $target = Join-Path $work $c.File
    $text = Get-Content -Raw $target
    Set-Content -Path $target -Value ($text -replace [regex]::Escape($c.From), $c.To)

    $cr = Build-In $work $tc
    if ($cr.Code -ne 0 -and $cr.Out -match [regex]::Escape($c.Needle)) {
      Write-Output ("  {0,-22} exit {1}    rejected as documented ({2})" -f $c.Name, $cr.Code, $c.Needle)
    } else {
      Write-Output ("  {0,-22} exit {1}    UNEXPECTED -- expected a failure mentioning '{2}'" -f $c.Name, $cr.Code, $c.Needle)
      Write-Output ($cr.Out.Trim() -split "`n" | Select-Object -Last 5 | ForEach-Object { "      $_" })
      $failures++
    }
    Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
  }
}

# Leave the tree on its pinned toolchain.
Set-Content -Path (Join-Path $here 'lean-toolchain') -Value 'leanprover/lean4:v4.33.1'

Write-Output ""
if ($failures -eq 0) {
  Write-Output "lean4#14875 behaved as documented on: $($Toolchains -join ', ')"
  exit 0
} else {
  Write-Output "$failures assertion(s) failed. If the EXHIBIT now fails to build, #14875 has been"
  Write-Output "fixed -- that is the intended regression signal, and this directory becomes a"
  Write-Output "regression witness the way ../paradox/ did when v4.33.0 shipped #14609."
  exit 1
}
