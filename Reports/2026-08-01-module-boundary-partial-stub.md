# A module boundary that turns a `partial` definition into a safe axiom of type `False`

**Date:** 2026-08-01
**Toolchains measured:** `v4.27.0-rc1`, `v4.30.0-rc2`, `v4.31.0`, `v4.32.0`, `v4.32.1`,
`v4.32.2`, `v4.33.0-rc1`, against `leanprover/lean4` at `5fa71c9141`.
**Artifact:** [`KernelDefects/Lean/ModuleSystem/paradox/`](../KernelDefects/Lean/ModuleSystem/paradox/).
**Provenance:** found by mining Stephen Dolan's
[*Counterexamples in Type Systems*](https://counterexamples.org)
([`Reports/Counterexamples/`](Counterexamples/)) for mechanisms with a Lean
analogue. This is the entry *Privacy violation*: a property is checked against a
declaration's local view, while consumers see a lossy summary across a boundary,
and the summary drops the property the check relied on.

---

## Claim

On **every released Lean toolchain**, a safe declaration can prove `False`:

```lean
-- Producer.lean
module
public import Lean
open Lean
public section
run_meta do
  addDecl (.mutualDefnDecl [{ name := `partialFalse, levelParams := [],
                              type := mkConst ``False, value := mkConst `partialFalse,
                              hints := .opaque, safety := .partial }])
end
```
```lean
-- Consumer.lean
module
public import Paradox.Producer
public theorem Paradox : _root_.False := partialFalse
```

No flag, no `sorry`, no `axiom`, no `unsafe` in the consumer, no
`debug.skipKernelTC`. **`#print axioms Paradox` reports nothing.**

This is [lean4#14609](https://github.com/leanprover/lean4/pull/14609), fixed on
`master` on 2026-07-30 by `d53dcb222f`. No released toolchain carries the fix,
and it is not on `releases/v4.33.0`.

---

## Mechanism

Two things have to be true, and each is reasonable on its own.

**The kernel accepts a `partial` definition of type `False`.**
`environment::add_mutual` requires a mutual block to be tagged `unsafe` or
`partial` — it rejects `safe` outright — and a `partial` block carries no
inhabitance obligation at the kernel level. The `Inhabited`/`Nonempty` obligation
people associate with `partial def` belongs to the *elaborator*'s `partial def`,
not to `Declaration.mutualDefnDecl`. What keeps this sound is the safety gate in
`type_checker::infer_constant`, which refuses to let a safe declaration mention
such a constant. Inside the defining module that gate works, and the artifact's
control shows it:

```
(kernel) invalid declaration, safe declaration must not contain partial declaration 'sameModuleFalse'
```

**The module boundary republishes it as a safe axiom.** When a `module` exports a
definition whose body stays private, `Lean.addDeclCore`
(`src/Lean/AddDecl.lean:118`) publishes an axiom stub in its place:

```lean
exportedInfo? := some <| .axiomInfo { defn with isUnsafe := defn.safety == .unsafe }
```

`defn.safety == .unsafe` is **false for `DefinitionSafety.partial`**. So
downstream sees `partialFalse` as an ordinary safe axiom of type `False`.

Both kernel gates then miss, for two different reasons. `infer_constant`'s first
test is `info.is_unsafe()`, which the stub answers `false`. Its second test only
inspects *definitions* — and a stub is an *axiom*, so it is skipped entirely. The
kernel is doing exactly what it was told. It was told wrong.

The fix is one character of substance: `defn.safety != .safe`.

---

## Measured behaviour

Each row builds the package and runs four modules plus `leanchecker`. Exit 0 is
the assertion in every column: `Audit.lean`'s `#guard_msgs` demands *"does not
depend on any axioms"* and raises an error if the imported `partialFalse` is not
an axiom stub with `isUnsafe = false`; `Control.lean`'s and
`ConsumerUnsafe.lean`'s each demand a specific kernel rejection.

| Toolchain | build | Consumer | Audit | Control | axiom-free theorems | `leanchecker` |
| --- | --- | --- | --- | --- | --- | --- |
| `v4.27.0-rc1` | 0 | 0 | 0 | 0 | 3 | did not run — it ships only from `v4.28.0` |
| `v4.30.0-rc2` | 0 | 0 | 0 | 0 | 3 | **reject** |
| `v4.31.0` | 0 | 0 | 0 | 0 | 3 | **reject** |
| `v4.32.0` | 0 | 0 | 0 | 0 | 3 | **reject** |
| `v4.32.1` | 0 | 0 | 0 | 0 | 3 | **reject** |
| `v4.32.2` | 0 | 0 | 0 | 0 | 3 | **reject** |
| `v4.33.0-rc1` | 0 | 0 | 0 | 0 | 3 | **reject** |

The three theorems are `partialBoom : False`, `oneEqTwo : (1 : Nat) = 2` — so
there is no doubt the `False` is real — and `Paradox : False`.

Two further controls sharpen the result.

**The `.unsafe` twin is blocked.** The identical construction across the identical
boundary with `safety := .unsafe` gets
`(kernel) invalid declaration, it uses unsafe declaration 'unsafeFalse'`, because
`.unsafe` satisfies `defn.safety == .unsafe` and the stub keeps its marking. The
entire difference between accepted and rejected is that one token — which is
exactly the token #14609 changed.

**`sorry` is not affected.** A `sorry`-backed definition crossing the same
boundary still reports `sorryAx` downstream, so CATALOG §5.1's "Module boundary:
`sorry` … correctly guarded" row holds as written. It is `partial` alone that the
summary drops.

**And the `False` escapes the module system.** `Audit.lean` is ordinary Lean —
no `module`, no `public` — that merely imports the package, and it proves
`downstream : (2 : Nat) = 3` with a clean audit of its own. Nothing downstream
has to opt in to anything, which is what makes this an exposure rather than a
curiosity.

`v4.32.1` and `v4.32.2` are the only two releases Lean has ever cut specifically
for kernel soundness. Both ship this.

---

## The two audit results, and why they differ

**`#print axioms` reports nothing.** Module stubs are excluded from the axiom
audit, and that is right for honest code: the stub stands for a body that *was*
checked, and reporting every private definition as an axiom would make the audit
useless. Here it stands for a `partial` body that was not checked, and the
exclusion becomes a blind spot.

[`CATALOG.md`](../CATALOG.md) §1.2 records `set_option debug.skipKernelTC true`
plus a hand-built `addDecl` as *"the only Lean route invisible to
`#print axioms`"*. **This is a second one**, and unlike that one it needs no
debug option and no `set_option` at all.

**`leanchecker` rejects it:**

```
uncaught exception: while replaying declaration 'partialBoom':
(kernel) invalid declaration, safe declaration must not contain partial declaration 'partialFalse'
```

It replays declarations against the real environment rather than the exported
view, so it sees the `partial` definition and refuses. Note the contrast with the
rest of [`KernelDefects/Lean/`](../KernelDefects/Lean/): the accelerator family
and the universe-spelling exhibit are both *accepted* by `leanchecker`, because
they are defects in the kernel it shares. This one is a defect in the frontend,
so the in-tree judge is enough — which is a nice demonstration that the two
tools cover genuinely different ground rather than one subsuming the other.

For the same reason `comparator` is unaffected, and #14607's commit message says
why in the neighbouring case: `lean4export` refuses declarations that are not
well-formed for export.

---

## A correction to this repository's own method

The 2026-08-01 pass that produced [`Universes/`](../KernelDefects/Lean/Universes/)
worked by diffing

```bash
git diff v4.32.2..master -- src/kernel/
```

on the theory that this gives *the exact set of checks the shipped kernels lack*.
It does — and that is the flaw. **#14609 is a `src/Lean/` fix**, so the diff could
not see it, and CATALOG went on saying two of the July wave's proofs of `False`
were unreleased when the answer is three.

The corrected sweep searches the whole range by message rather than by path:

```bash
git log v4.32.2..HEAD --format="%h %s" --grep=soundness --grep=unsound \
    --grep="proof of false" --grep="kernel bug" --grep=inconsisten -i
```

Ten commits, which classify as:

| | |
| --- | --- |
| **Unreleased proofs of `False`** | **#14609** (this report), **#14613** ([`Universes/`](../KernelDefects/Lean/Universes/)), **#14616** (still a gap) |
| Already released | #14498/#14484 (`v4.32.1`), #14577/#14576 (`v4.32.2`) |
| Widening / hardening, not soundness | #14615, #14621 |
| Tactic bugs the kernel itself caught | #14618 (`grind` closed a goal with an ill-typed term — and the kernel rejected it), #13587 (`lia`/`grind` `eq_def` kernel type mismatch), #14524, #14404 |

The general lesson is the one #14609 itself illustrates: **soundness is not a
property of `src/kernel/`.** The kernel's gates were correct throughout; what
failed was the frontend's summary of a declaration, and a search scoped to the
kernel is structurally unable to find that class.

---

## Scope and honesty

* **Reachable only through metaprogramming**, since the `partial` definition of
  `False` has to be handed to the kernel with `addDecl` — the `partial def`
  elaborator would demand `Inhabited False`. Upstream's own commit message says
  as much. That is not a mitigation, for the reason the #14576 postmortem gives.
* **Not a kernel defect.** It is a frontend defect that defeats a kernel gate, in
  the same family as the Lean Kernel Arena's *trusted-metadata* tests
  (`ctor-num-fields`, `rec-k-lie`), where the checker is lied to about a
  declaration rather than reasoning wrongly about one.
* **Not novel as a defect** — #14609 is upstream's, found and fixed in the July
  wave. What is new here is the artifact, the observation that `#print axioms` is
  blind to it, the full version matrix, the `leanchecker` verdict, and the
  correction to this repository's sweep method.
* **The `v4.33` backport gap now has three members**, not two: `releases/v4.33.0`
  is still at `f839b65ba4` and carries none of #14609, #14613, #14616. See
  [`2026-07-29-lean-4.33-backport-gap.md`](2026-07-29-lean-4.33-backport-gap.md).
