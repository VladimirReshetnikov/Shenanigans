# The module boundary that loses `partial`

> **Warning.** [`paradox/`](paradox/) is a Lake package containing a
> machine-checked proof of `False`. It is deliberately unsound, it is not part of
> this repository's own build, and it must never be imported.

Category: [`KernelDefects/`](../../README.md) — closed `False`, **clean audit**,
no flag, no `prelude`. Full write-up:
[`Reports/2026-08-01-module-boundary-partial-stub.md`](../../../Reports/2026-08-01-module-boundary-partial-stub.md).

## The hole in one paragraph

Lean's 2026 module system publishes a definition whose body stays private as an
*axiom stub*. `Lean.addDeclCore` (`src/Lean/AddDecl.lean:118`) built the stub with

```lean
exportedInfo? := some <| .axiomInfo { defn with isUnsafe := defn.safety == .unsafe }
```

and that test is **false for `DefinitionSafety.partial`**. So a `partial`
definition crosses the boundary as an ordinary *safe* axiom. Feed the kernel a
`partial` definition whose type is `False` — which it accepts, because a mutual
block tagged `partial` carries no inhabitance obligation at the kernel level —
and the module boundary launders it into a safe axiom of type `False`.

Both of the kernel's safety gates then miss, for two different reasons:
`type_checker::infer_constant` tests `info.is_unsafe()`, which the stub answers
`false`; and its `partial` test only inspects *definitions*, while a stub is an
*axiom*. The kernel is doing exactly what it was told; it was told wrong.

## What makes it worth a directory

**`#print axioms` reports nothing.** Module stubs are excluded from the axiom
audit by design — for an honest definition the stub stands for a body that *was*
checked. Here it stands for a `partial` body that was not.
[`CATALOG.md`](../../../CATALOG.md) §1.2 records `debug.skipKernelTC` plus a
hand-built `addDecl` as *"the only Lean route invisible to `#print axioms`"*.
This is a second one, and unlike that one it needs no debug option.

**The `False` does not stay inside the module system.** `Audit.lean` is ordinary
Lean — no `module`, no `public` — that merely imports the package, and it proves
`downstream : (2 : Nat) = 3` with a clean audit of its own. Nothing downstream
has to opt in to anything.

**`leanchecker` catches it**, because it replays declarations against the real
environment rather than the exported view:

```
uncaught exception: while replaying declaration 'partialBoom':
(kernel) invalid declaration, safe declaration must not contain partial declaration 'partialFalse'
```

That is the cross-checking argument of *Who Watches the Provers?* doing real work
— and, unusually for this directory, the shipped in-tree judge is enough, because
the defect is in the frontend rather than in the kernel it shares.

## Contents

| File | What it is |
| --- | --- |
| [`paradox/Paradox/Producer.lean`](paradox/Paradox/Producer.lean) | `module`. A `partial` definition of type `False`, handed to the kernel with `addDecl`. Legitimate on its own. |
| [`paradox/Paradox/Consumer.lean`](paradox/Paradox/Consumer.lean) | `module`. `public theorem Paradox : False := partialFalse`, from a **safe** declaration. Also `oneEqTwo : (1 : Nat) = 2`, so there is no doubt the `False` is real. |
| [`paradox/Paradox/Audit.lean`](paradox/Paradox/Audit.lean) | Not a `module`, so `#print axioms` is available on every toolchain. Asserts the clean audit with `#guard_msgs`, and asserts that the imported `partialFalse` really is an `axiomInfo` with `isUnsafe = false`. |
| [`paradox/Paradox/Control.lean`](paradox/Paradox/Control.lean) | Control. The identical `partial` definition used from a safe theorem in the **same** module, so no stub is created: `(kernel) invalid declaration, safe declaration must not contain partial declaration`. |
| [`paradox/Paradox/ProducerUnsafe.lean`](paradox/Paradox/ProducerUnsafe.lean), [`ConsumerUnsafe.lean`](paradox/Paradox/ConsumerUnsafe.lean) | **Differential control, and the sharpest one.** The identical construction across the identical boundary with `safety := .unsafe` instead of `.partial`. It is *blocked*: `(kernel) invalid declaration, it uses unsafe declaration 'unsafeFalse'`, because `.unsafe` satisfies `defn.safety == .unsafe` and the stub keeps its marking. The whole difference between accepted and rejected is that one token. |

## Status

| | |
| --- | --- |
| Upstream | [lean4#14609](https://github.com/leanprover/lean4/pull/14609), merged `master` 2026-07-30 (`d53dcb222f`), one character of substance: `defn.safety == .unsafe` → `defn.safety != .safe` |
| Released toolchains carrying the fix | **none** |
| On `releases/v4.33.0`? | **no** — that branch is still at `f839b65ba4` (#14577) |
| `#print axioms` | **reports nothing** |
| `leanchecker` | **rejects** (and did not exist before `v4.28.0`) |
| Where the defect lives | `src/Lean/AddDecl.lean`, **not** `src/kernel/` |
| Coverage before this directory | none. CATALOG filed #14609 under §2.2 "fixed", and §5.1's module-boundary sweep covered `sorry`, private-in-public and section variables — not `partial`. That row's `sorry` claim does hold: a `sorry`-backed definition crosses the boundary still reporting `sorryAx` |

## The methodology lesson

This one was missed here for a structural reason worth recording. The 2026-08-01
pass that found [`Universes/`](../Universes/) worked by diffing
`git diff v4.32.2..master -- src/kernel/`. **#14609 is a `src/Lean/` fix**, so
that diff could not see it, and CATALOG went on saying two of the July wave's
`False`s were unreleased when the answer is three. The corrected sweep is to
search *every* commit in the range by message —

```bash
git log v4.32.2..HEAD --format="%h %s" --grep=soundness --grep=unsound -i
```

— which turns up ten commits, of which #14609, #14613 and #14616 are the three
unreleased proofs of `False`; #14615 and #14621 are widening and hardening, and
#14618, #13587, #14524, #14404 are tactic bugs the kernel itself caught.

## Reproducing

```bash
pwsh KernelDefects/Lean/ModuleSystem/verify.ps1
```

The package is copied to a scratch directory outside this repository before
building, so nothing here joins any Lake workspace.
