# Independent checkers, measured rather than cited

Every other verdict in this repository about an independent checker is a
citation. [`CATALOG.md`](../../../CATALOG.md) §2.5 says `nanoda` *"decides all
three semantically"*; lean4#14613's commit message says *"`nanoda` rejects it"*.
This directory runs it.

Category ([`../../README.md`](../../README.md)): no `False` is produced here.
The result is a measurement, and it is a **positive** one — the cross-checking
safeguard works on the exact construction this repository ships an exhibit for.

## The question

[`KernelDefects/Lean/Universes/`](../../../KernelDefects/Lean/Universes/) is an
axiom-free `False` on every released Lean toolchain, and it turns on a *spelling*:
the released kernel reads `Sort (imax 1 0)` as "not a proposition" even though
that level denotes `0`. Upstream says `nanoda` rejects the construction — but
`nanoda`'s own regression resource, `test_resources/ProjFromProp`, uses the
**honest** `Sort 0`. Whether it also catches the laundered spelling is a
different question, and it is the one that matters, because the laundering is
what gets the term past a released Lean kernel in the first place.

## What was measured

`nanoda_lib` 0.4.10-beta, built from [`Upstream/nanoda_lib`](../../../Upstream/).

| Case | Verdict |
| --- | --- |
| control — a well-formed export | **accept**, exit 0, `Checked 0 declarations with no typechecker errors` |
| honest — `nanoda`'s own `ProjFromProp`, `Sort 0` | **reject**, exit 101, `panicked at src/tc.rs:474: infer_proj prop` |
| laundered — the same with `Sort (imax 1 0)` | **reject**, exit 101, same message, same site |

So `nanoda` normalises the level before deciding `Prop`-hood, and the
cross-checking argument of *Who Watches the Provers?* holds on this construction:
**the released Lean kernel accepts it and the independent checker does not.**

The laundered export is *derived* by `verify.ps1` from `nanoda`'s own resource
with a three-line edit — `{"ie":14,"sort":0}` becomes `Sort (imax 1 0)` via two
new level entries — rather than vendored, so the provenance stays visible and
their file (Apache-2.0) stays theirs.

## Two things worth recording about the failure mode

**`nanoda` rejects by panicking.** Exit 101 with `panicked at src/tc.rs:474` is
a safe failure for a judge — it cannot be mistaken for acceptance by anything
that reads the exit code. But it is not a verdict, and a harness that decided by
parsing output for the word `error` would misread it: the string `error` does not
appear. That is [ground rule 5](../../../README.md) meeting a real case, and it
is why `verify.ps1` here checks both the exit code **and** that the rejection
carries `infer_proj prop` — a rejection for a missing file would otherwise pass
as evidence. It did, on the first run of this script.

**The control is load-bearing.** "`nanoda` rejects it" says nothing without a
case `nanoda` accepts; the empty export supplies one.

## Reproducing

```bash
pwsh Audits/Lean/Checkers/verify.ps1
```

Requires `cargo` and the `Upstream/nanoda_lib` submodule; the script builds
`nanoda` itself, and exits 0 with a note if the submodule is absent — which it
is in a `git worktree` unless you initialise it there. Pass `-SkipBuild` to reuse
an existing `target/release/nanoda_bin`.
