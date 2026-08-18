/-
Category (see ../../README.md): **audit**, and specifically an audit of this
repository's own method rather than of Lean.

`Environment.addDeclCore`'s `maxHeartbeats` argument is **not a per-call
allowance**.  It is a *threshold* compared against a counter that accumulates
across the whole task, so a sweep that submits many declarations inside one
command crosses it partway through, and every later submission comes back as
`(kernel) deterministic timeout` — the very declaration the kernel accepted a
moment earlier.

A harness that classifies `Except.error` as "the kernel refused this on its
merits" then silently truncates its own corpus and reports the truncation as a
completed sweep.  README ground rule 5 used to recommend a finite budget; it now
says to pass `0`, and this file is the measurement behind that change.

Lean core does it correctly in both places it replays declarations in bulk:
`src/Lean/Replay.lean` and `src/Lean/Environment.lean` each call
`addDeclCore 0 0`.

NOT A DEFECT IN LEAN, and it should not be filed upstream.  Through
`Lean.addDecl` the same option bounds the elaborator too, the allocation counter
grows far faster, and `Core`'s own check fires first.  It is a hazard only for
harnesses that call the kernel entry point directly in a loop — which is exactly
what this repository does.

WHAT IT DID NOT DO.  No result recorded in this repository is invalidated by it.
The largest `addDecl`-looping sweep here is
[`../Lean/Fuzz/IsNotZeroFuzzer.lean`](../Lean/Fuzz/IsNotZeroFuzzer.lean), whose
recorded line is "360 level spellings, 91 large-eliminating: 0 unsound"; re-run
on v4.33.0 it reports `levels=360 declared=360 largeElim=91 UNSOUND=0`, so
nothing was dropped.  That sweep passes `{}` for the options, which resolves to
the default `maxHeartbeats` scaled by 1000 — a threshold far above what 360
small inductives consume.  The hazard is real; it happens not to have bitten.

Run: elan run leanprover/lean4:v4.33.0 lean <this file>
-/
import Lean

open Lean

set_option Elab.async false

namespace HeartbeatBudget

/-- A declaration whose kernel cost is small, fixed, and identical for every `i`. -/
def triv (i : Nat) : Declaration :=
  .defnDecl { name := Name.mkSimple s!"hbTriv{i}", levelParams := [],
              type := mkConst ``Nat, value := mkNatLit i,
              hints := .abbrev, safety := .safe }

/-- Submit `n` identical declarations in ONE command at threshold `b`, against
    the same starting environment each time, and count how many the kernel
    takes.  Under a per-call reading this is all-or-nothing; under a cumulative
    reading it scales with `b`. -/
def sweep (env : Environment) (b : USize) (n : Nat) : Nat := Id.run do
  let mut ok := 0
  for i in [0:n] do
    match env.addDeclCore b 8000 (triv i) none with
    | .ok _ => ok := ok + 1
    | .error _ => pure ()
  return ok

end HeartbeatBudget

open HeartbeatBudget

/--
info: 3000 IDENTICAL declarations, submitted in one command:
at a finite budget, some are accepted and the rest are refused
at budget 0, all 3000 are accepted
A per-call cost would give the same verdict for every one of them, so the
refusals are a property of the SWEEP's position, not of the declaration.
-/
#guard_msgs in
run_meta do
  let env ← getEnv
  -- Finite first: a later sweep would start from an already-raised counter.
  let f := sweep env 16000 3000
  let u := sweep env 0 3000

  -- The 3000 declarations are identical in content and cost.  Under a per-call
  -- reading the verdict is the same for all of them; a split is only possible
  -- if the budget is compared against something that accumulates.
  unless 0 < f && f < 3000 do
    throwError "expected a split at the finite budget, got {f} accepted of 3000"
  unless u == 3000 do
    throwError "unlimited budget did not accept everything: {u}"

  logInfo "3000 IDENTICAL declarations, submitted in one command:\n\
             at a finite budget, some are accepted and the rest are refused\n\
             at budget 0, all 3000 are accepted\n\
           A per-call cost would give the same verdict for every one of them, so the\n\
           refusals are a property of the SWEEP's position, not of the declaration."
