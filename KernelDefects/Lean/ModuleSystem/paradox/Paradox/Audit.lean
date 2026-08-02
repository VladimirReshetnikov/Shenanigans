import Paradox.Consumer
import Lean

/-!
The audit, and the escape.  Deliberately NOT a `module`: `#print axioms` is
refused inside one on toolchains before `v4.30`, and this file has to run on all
of them.

Two things are established here.

**The audit is blind.**  `partialFalse` is, in this environment, literally an
`axiomInfo` — and `#print axioms` reports nothing.  Module stubs are excluded
from the axiom audit by design, because for an honest definition the stub stands
for a body that *was* checked; here it stands for a `partial` body that was not.
[`CATALOG.md`](../../../../../CATALOG.md) §1.2 records `debug.skipKernelTC` plus a
hand-built `addDecl` as "the only Lean route invisible to `#print axioms`".  This
is a second one, and unlike that one it needs no debug option.

**The `False` does not stay inside the module system.**  This file is ordinary
Lean that merely imports the package.  It gets `False` too, and its audit is
clean as well — so nothing downstream has to opt in to anything.
-/

/-- info: 'partialBoom' does not depend on any axioms -/
#guard_msgs in
#print axioms partialBoom

/-- info: 'oneEqTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms oneEqTwo

/-- info: 'Paradox' does not depend on any axioms -/
#guard_msgs in
#print axioms Paradox

/-! ### The escape into plain Lean

Nothing below is a `module`, uses `public`, or mentions the module system at all. -/

theorem downstream : (2 : Nat) = 3 := Paradox.elim

/-- info: 'downstream' does not depend on any axioms -/
#guard_msgs in
#print axioms downstream

open Lean in
run_cmd do
  match (← Lean.getEnv).find? `partialFalse with
  | none                 => Lean.logError "partialFalse: ABSENT — the reproducer is broken"
  | some (.axiomInfo v)  =>
      Lean.logInfo m!"partialFalse is an AXIOM, isUnsafe = {v.isUnsafe}"
      if v.isUnsafe then
        Lean.logError "*** the stub is marked unsafe — this toolchain has the fix, update the matrix ***"
  | some (.defnInfo v)   => Lean.logInfo m!"partialFalse is a DEFINITION, safety = {repr v.safety}"
  | some _               => Lean.logInfo "partialFalse: other constant kind"
