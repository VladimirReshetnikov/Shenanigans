import Paradox.Consumer
import Lean

/-!
The audit.  Deliberately NOT a `module`: `#print axioms` is refused inside one on
toolchains before `v4.30`, and this file has to run on all of them.

The point of this file is the second half of the defect.  `partialFalse` is, in
this environment, literally an `axiomInfo` — and `#print axioms` reports
**nothing**.  Module stubs are excluded from the axiom audit by design, because
for an honest definition the stub stands for a body that was checked; here it
stands for a `partial` body that was not.

CATALOG.md §1.2 records `debug.skipKernelTC` + a hand-built `addDecl` as "the only
Lean route invisible to `#print axioms`".  This is a second one, and unlike that
one it needs no debug option.
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
