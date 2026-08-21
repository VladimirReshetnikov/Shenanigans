# What does `rocqchk` actually validate, and does it depend on how you ask?
#
#   pwsh Audits/Coq/CheckerCoverage/verify.ps1
#
# Category (see ../../../README.md): **audit**.  No proof of False is produced
# here.  The question is narrower and is the one CATALOG.md §4.7 exists to ask:
# a CI script that runs `rocqchk` and checks the exit code -- what has it
# actually established?
#
# Three measurements, all asserted, all on the installed toolchain.
#
#   1. ORDER DEPENDENCE (rocq#22362, and #22360 as the observable).  Two
#      `rocqchk` invocations differing ONLY in the order of two `-norec`
#      arguments give opposite verdicts on the same files.  A `-norec` root that
#      is interned first pulls its dependencies in as `Dep`, which reads them
#      through `System.marshal_in` with no `Validate.validate`; a later explicit
#      `-norec` for such a dependency finds it already in `needed` and does
#      nothing.  So naming a library on the command line does not mean it was
#      validated, and the passing order still PRINTS it in the "Checking
#      library:" list.
#
#   2. THE SEGMENT DIGEST IS NOT COMPARED, in any mode (negative result).  A .vo
#      whose recorded per-segment MD5 does not match its contents is accepted by
#      `rocqchk` in both `-norec` orders and in full-closure mode.  This is NOT
#      unsoundness -- the contents spliced in is another honest compilation, so
#      what the checker type-checks is well typed and it correctly says so.  It
#      is recorded because it says where the line actually is: the digest is an
#      accident detector, and the only thing standing between a hand-edited .vo
#      and a bogus theorem is that `rocqchk` re-typechecks the bodies.
#
#   3. ...WHICH IS EXACTLY WHAT rocq#22352 GETS AROUND, by lying in the one
#      segment the re-typechecking does not derive its answers from.  The
#      artifact for that is ../../../KernelDefects/Coq/Checker/, and this script
#      asserts the pointer rather than repeating the exhibit.
#
# Needs `rocq`, `rocqchk` and `python` on PATH.

$ErrorActionPreference = 'Stop'
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("rocqchk-coverage-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $work -Force | Out-Null

$version = (& coqc --version 2>&1 | Select-Object -First 1)
Write-Host "Toolchain: $version"
Write-Host ""

$failures = 0
function Check([string] $label, [bool] $ok, [string] $detail) {
  if ($ok) { Write-Host ("  [ok]   {0}" -f $label) }
  else { Write-Host ("  [FAIL] {0}" -f $label) -ForegroundColor Red; if ($detail) { Write-Host ("         {0}" -f $detail) }; $script:failures++ }
}

try {
  # ======================================================================
  # 1.  Order dependence.
  # ======================================================================
  Write-Host "1. Does the set of validated files depend on argument order? (rocq#22362)"
  $ord = Join-Path $work 'ord'
  New-Item -ItemType Directory -Path $ord -Force | Out-Null
  $coqlib = (& rocq c -where).Trim()
  Set-Content (Join-Path $ord 'A.v') "Require Import Corelib.Strings.PrimString.`nDefinition foo := 1.`n"

  Push-Location $ord
  & rocq c -R . "" A.v 2>&1 | Out-Null
  Check "A.v compiles" ($LASTEXITCODE -eq 0) ""

  $theories = Join-Path $coqlib 'theories'
  $first  = & rocqchk -bytecode-compiler yes -Q $theories Corelib -R . "" -norec A -norec Corelib.Strings.PrimString 2>&1 | Out-String
  $firstCode = $LASTEXITCODE
  $second = & rocqchk -bytecode-compiler yes -Q $theories Corelib -R . "" -norec Corelib.Strings.PrimString -norec A 2>&1 | Out-String
  $secondCode = $LASTEXITCODE
  Pop-Location

  Check "the two orders give DIFFERENT exit codes on the same files" `
    ($firstCode -ne $secondCode) "both were $firstCode"
  Check "PrimString-validated-first FAILS validation (rocq#22360)" `
    (($firstCode -ne 0) -and ($first -match 'Validation failed')) ($first | Select-Object -Last 1)
  Check "PrimString-as-a-dependency is ACCEPTED, unvalidated" `
    (($secondCode -eq 0) -and ($second -match 'Modules were successfully checked')) ($second | Select-Object -Last 1)
  Check "...and the accepting run still lists it as 'Checking library'" `
    ($second -match 'Checking library: Corelib\.Strings\.PrimString') "not listed"

  # ======================================================================
  # 2.  Is the recorded segment digest compared?
  # ======================================================================
  Write-Host ""
  Write-Host "2. Is a .vo whose segment digest does not match its contents rejected?"
  $dig = Join-Path $work 'digest'
  New-Item -ItemType Directory -Path (Join-Path $dig 'v1') -Force | Out-Null
  New-Item -ItemType Directory -Path (Join-Path $dig 'v2') -Force | Out-Null
  $bsrc = "Unset Elimination Schemes.`nInductive bool : Set := true | false.`nDefinition b : bool := true.`n"
  Set-Content (Join-Path $dig 'v1/B.v') $bsrc
  Set-Content (Join-Path $dig 'v2/B.v') ($bsrc.Replace(':= true.', ':= false.'))
  foreach ($d in 'v1', 'v2') {
    Push-Location (Join-Path $dig $d)
    & rocq c -boot -R . "" -noinit B.v 2>&1 | Out-Null
    $ok = ($LASTEXITCODE -eq 0)
    Pop-Location
    Check "honest compilation $d" $ok ""
  }

  Push-Location $dig
  # Contents from v2, digest recorded from v1: the file's own checksum is wrong.
  $py = @'
import hashlib, struct, sys
M = 0x436F7121
def parse(p):
    b = open(p, "rb").read()
    ver = struct.unpack_from(">I", b, 4)[0]
    o = struct.unpack_from(">Q", b, 8)[0]
    n = struct.unpack_from(">I", b, o)[0]; o += 4; s = {}
    for _ in range(n):
        nl = struct.unpack_from(">I", b, o)[0]; o += 4
        nm = b[o:o+nl].decode(); o += nl
        pos, ln = struct.unpack_from(">QQ", b, o); o += 16
        dig = b[o:o+16]; o += 16
        s[nm] = (b[pos:pos+ln], dig)
    return ver, s
def write(p, ver, by):
    out = bytearray(struct.pack(">IIQ", M, ver, 0)); su = []
    for nm in sorted(by):
        data, dg = by[nm]; pos = len(out); out += data; out += dg
        su.append((nm, pos, len(data), dg))
    sp = len(out); out += struct.pack(">I", len(su))
    for nm, pos, ln, dg in su:
        nb = nm.encode()
        out += struct.pack(">I", len(nb)) + nb + struct.pack(">QQ", pos, ln) + dg
    struct.pack_into(">Q", out, 8, sp); open(p, "wb").write(out)
v, s1 = parse("v1/B.vo"); _, s2 = parse("v2/B.vo")
seg = dict(s1)
seg["library"] = (s2["library"][0], s1["library"][1])
assert hashlib.md5(seg["library"][0]).digest() != seg["library"][1], "digest unexpectedly matches"
write("B.vo", v, seg)
print("ok")
'@
  Set-Content -Path (Join-Path $dig 'mismatch.py') -Value $py -NoNewline
  $mk = & python mismatch.py 2>&1 | Out-String
  Check "built a .vo whose recorded digest does not match its contents" ($mk -match 'ok') $mk.Trim()

  Set-Content (Join-Path $dig 'A.v') "Require Import B.`nDefinition foo := b.`n"
  & rocq c -boot -R . "" -noinit A.v 2>&1 | Out-Null
  Check "rocq c accepts a Require of it" ($LASTEXITCODE -eq 0) ""

  $o1 = & rocqchk -boot -R . "" -norec A -norec B 2>&1 | Out-String; $c1 = $LASTEXITCODE
  $o2 = & rocqchk -boot -R . "" -norec B -norec A 2>&1 | Out-String; $c2 = $LASTEXITCODE
  $o3 = & rocqchk -boot -R . "" A 2>&1 | Out-String;                 $c3 = $LASTEXITCODE
  Pop-Location

  Check "NEGATIVE RESULT: accepted in both -norec orders AND in full-closure mode" `
    (($c1 -eq 0) -and ($c2 -eq 0) -and ($c3 -eq 0)) "exits: $c1 / $c2 / $c3"
  Check "...so the digest is not what catches a hand-edited .vo; re-typechecking is" `
    ($o3 -match 'Modules were successfully checked') ($o3 | Select-Object -Last 1)

  # ======================================================================
  # 3.  The pointer.
  # ======================================================================
  Write-Host ""
  Write-Host "3. And re-typechecking is what rocq#22352 escapes."
  $exhibit = Join-Path (Split-Path (Split-Path (Split-Path $PSScriptRoot -Parent) -Parent) -Parent) 'KernelDefects/Coq/Checker/verify.ps1'
  Check "the exhibit for that is present" (Test-Path $exhibit) "expected $exhibit"
} finally {
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Host ""
if ($failures -eq 0) { Write-Host "All checker-coverage measurements behaved as documented." }
else { Write-Host ("{0} measurement(s) deviated from the documented behaviour." -f $failures) -ForegroundColor Red }
exit ([int]($failures -ne 0))
