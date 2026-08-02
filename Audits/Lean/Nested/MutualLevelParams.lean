import Lean
/-!
LEDGER CORRECTION (no `False`).  [`CATALOG.md`](../../../CATALOG.md) §5.1 asserted,
of `Declaration.mutualDefnDecl`, that "#14608's same-`lparams` requirement is
enforced".  **It is not, on any released toolchain.**

[lean4#14608](https://github.com/leanprover/lean4/pull/14608) added

    names const & lparams = head(vs).get_lparams();
    ...
    if (v.get_lparams() != lparams)
        throw kernel_exception(*this, "invalid mutual definition, declarations must have the same universe level parameters");

to `environment::add_mutual` (`kernel/environment.cpp`) on 2026-07-30 — after
`v4.32.2` was tagged and after `v4.33.0-rc1` was cut.  So it joins #14607, #14609,
#14613 and #14616 in the set of July-wave fixes that no release carries.

Why this matters beyond the ledger: it is the fourth such fix, and the third
*different* method this repository has used to enumerate them has missed one.
Diffing `src/kernel/` missed #14609 because that fix is in `src/Lean/`.  Searching
commit messages for "soundness" missed #14608 because its message does not use the
word.  The only method that does not miss anything is to take the PR numbers the
postmortem itself names — #14607–#14616, #14621, #14631, #14632, #14633 — and
check each one against the release tags directly.

This is not by itself a route to `False`: `add_mutual` refuses a block tagged
`safe`, so the safety gate still stands between a mismatched block and any safe
declaration.  The composite worth trying is #14608 together with #14609, since the
latter is exactly a way to get a `partial` block's members past that gate.

Run with plain `lean --trust=0 MutualLevelParams.lean`.
-/
open Lean Elab Command Meta

private def probe (tag : String) (d : Declaration) (names : List Name) : MetaM Unit := do
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .error e => logInfo m!"rejected  {tag}\n          {← (e.toMessageData {}).toString}"
  | .ok kenv =>
    let mut s := ""
    for n in names do
      if let some ci := kenv.find? n then
        s := s ++ s!"\n            {n} : levelParams = {ci.levelParams}, type = {← ppExpr ci.type}"
    logInfo m!"ACCEPTED  {tag}{s}"

run_cmd liftTermElabM do
  let u : Level := .param `u
  let v : Level := .param `v
  -- Two members of one `partial` mutual block, declared at DIFFERENT universe
  -- parameters.  On `master` this is "invalid mutual definition, declarations
  -- must have the same universe level parameters".
  probe "mutual `partial` block, members at different universe parameters"
    (.mutualDefnDecl [
      { name := `MA, levelParams := [`u], hints := .opaque, safety := .partial,
        type := .sort (.succ u), value := .sort u },
      { name := `MB, levelParams := [`v], hints := .opaque, safety := .partial,
        type := .sort (.succ v), value := .sort v }])
    [`MA, `MB]
  -- Control: the same block with matching parameters, which is legal everywhere.
  probe "control — matching universe parameters"
    (.mutualDefnDecl [
      { name := `NA, levelParams := [`u], hints := .opaque, safety := .partial,
        type := .sort (.succ u), value := .sort u },
      { name := `NB, levelParams := [`u], hints := .opaque, safety := .partial,
        type := .sort (.succ u), value := .sort u }])
    [`NA, `NB]

/-
Expected on every released toolchain through v4.33.0-rc1:

  ACCEPTED  mutual `partial` block, members at different universe parameters
              MA : levelParams = [u], type = Type u
              MB : levelParams = [v], type = Type v
  ACCEPTED  control — matching universe parameters

On `master`, the first is rejected with
  "invalid mutual definition, declarations must have the same universe level parameters".
-/
