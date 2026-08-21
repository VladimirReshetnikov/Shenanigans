# An axiom-free `False` on every released Lean toolchain, and the inheritance step upstream did not name

**Date:** 2026-08-01
**Source line numbers** are `v4.32.2`'s unless stated otherwise.
**Toolchains measured:** `v4.27.0-rc1`, `v4.30.0-rc2`, `v4.31.0`, `v4.32.0`, `v4.32.1`,
`v4.32.2`, `v4.33.0-rc1` (all `x86_64-w64-windows-gnu`), against
`leanprover/lean4` at `5fa71c9141` (`master` after #14633) for the source
citations.
**Artifacts:** [`KernelDefects/Lean/Universes/ImaxPropSpelling.lean`](../KernelDefects/Lean/Universes/ImaxPropSpelling.lean),
[`KernelDefects/Lean/Universes/MutualResultLevel.lean`](../KernelDefects/Lean/Universes/MutualResultLevel.lean),
control [`KernelDefects/Lean/Controls/ImaxPropControl.lean`](../KernelDefects/Lean/Controls/ImaxPropControl.lean).

---

## Summary

`theorem Paradox : False` is accepted by the released Lean kernel under
`--trust=0`, with `#print axioms` reporting nothing, on every toolchain from
`v4.27.0-rc1` through `v4.33.0-rc1`. The underlying defect is
[lean4#14613](https://github.com/leanprover/lean4/pull/14613), fixed on `master`
on 2026-07-31 by commit `17dbc815cf` and named in de Moura's
[postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)
as one of the follow-ups to #14576. **No released toolchain carries the fix.**

Two things here are not upstream's.

1. **The reproducer needs two independent kernel weaknesses, and upstream's
   commit message and regression test name only one.** The second — the
   *inheritance step* — is that a mutual inductive block takes `m_result_level`
   from its **first** type and lets every other type in the block inherit the
   permissions that spelling earns. It is *not* fixed on `master`.
2. **The defect class is wider than the one level it is documented against.**
   Upstream's test uses `Sort (imax 1 0)`. `Sort (max 0 0)` works identically,
   and for the same reason: `is_zero` asks `kind() == Zero`, so *every* spelling
   of zero that is not literally `Level.zero` is in scope.

Neither changes upstream's fix — `normalizes_to_zero` closes both spellings at
once, because it is a semantic test. Both change what the *catalog* should say
about the shape of the hole, and (1) leaves a live primitive behind.

---

## The construction

### Step 1 — inheritance: borrow a `Sort 0`'s permissions

`add_inductive_fn::check_inductive_types` (`kernel/inductive.cpp:248`) does:

```cpp
if (first) {
    m_result_level = sort_level(type);
    m_is_not_zero  = is_not_zero(m_result_level);
} else if (!is_equivalent(sort_level(type), m_result_level)) {
    throw kernel_exception(m_env, "mutually inductive types must live in the same universe");
}
```

`m_result_level` is the **first** type's level *as written*. Every later type is
only required to be `is_equivalent` to it — and `is_equivalent`
(`kernel/level.cpp:503`) normalizes. Every downstream gate then reads that one
spelling. The gate that matters is `check_constructors`
(`kernel/inductive.cpp:439`):

```cpp
if (!(is_geq(m_result_level, sort_level(s)) || is_zero(m_result_level)))
    throw kernel_exception(..., "universe level of type_of(arg #N) ... is too big ...");
```

`is_geq` normalizes (`level.cpp:527`); `is_zero` is `kind() == Zero`
(`level.h:106`) and does not. A proposition carrying a data field is legal — it
is the squashed/`exProp` type, and its recursor is correspondingly restricted —
but the permission is granted only to the syntactic `Level.zero`.

So `Sort (imax 1 0)`, which *denotes* `Prop`, cannot carry a `Bool` field on its
own. Put a `Sort 0` type first in the same mutual block and it can.
`MutualResultLevel.lean` measures exactly this, and the reversal is the control:

| Block | `v4.27.0-rc1` … `v4.33.0-rc1` |
| --- | --- |
| `W : Sort (imax 1 0)` alone, `Bool` field | **rejected** |
| `W : Sort (max 0 0)` alone, `Bool` field | **rejected** |
| `W : Sort 0` alone, `Bool` field | accepted (legitimately) |
| `D : Sort 0`, then `W : Sort (imax 1 0)` | **accepted** |
| `D : Sort 0`, then `W : Sort (max 0 0)` | **accepted** |
| `D : Sort (imax 1 0)`, then `W : Sort 0` | **rejected** |
| `D : Sort (max 0 0)`, then `W : Sort 0` | **rejected** |

The last two rows are the point. Swapping the order rejects the same pair of
types, which pins the behaviour on *first type* rather than on *some type in the
block*.

### Step 2 — the same type through two spellings of its own sort

```lean
def AsProp : Prop := Weird          -- accepted: level equality normalizes
```

Now one inductive is reachable through two sorts:

* `Weird`, whose `infer_type` is the raw `Sort (imax 1 0)`;
* `AsProp`, whose `infer_type` is the syntactic `Sort 0`.

`type_checker::is_prop` at `v4.32.2` was

```cpp
bool type_checker::is_prop(expr const & e) { return whnf(infer_type(e)) == mk_Prop(); }
```

(`type_checker.cpp:328`) — a syntactic comparison. Consulted through `AsProp` it
says **yes**; through `Weird` it says **no**. Both consumers behave correctly given their answer:

* `is_def_eq_proof_irrel` (`type_checker.cpp:836`) sees `AsProp`, applies proof
  irrelevance, and equates `Weird.mk false` with `Weird.mk true`. This step is
  *right* — they really are two proofs of a proposition.
* `infer_proj` (`type_checker.cpp:248`, guards at `:253` and `:263`) sees `Weird`, concludes it is not
  a proposition, and therefore does not require the projected field to be a
  proof. This step is wrong.

Neither spelling is incorrect. The kernel simply never compares them, and the
type is a proposition for one purpose and not for the other in the same session.

### Step 3

```lean
theorem boom : False :=
  Bool.noConfusion (show false = true from congrArg extract irrel)
```

`#print axioms boom` reports nothing.

---

## Measured behaviour

Each row is `lean --trust=0 <file>`, exit code plus the `#guard_msgs`-asserted
audit output. `MutualResultLevel.lean` is a measurement and produces no `False`.

| Toolchain | `ImaxPropSpelling.lean` | `ImaxPropControl.lean` |
| --- | --- | --- |
| `v4.27.0-rc1` | exit 0 — `False` accepted, `'Paradox' does not depend on any axioms` | exit 0 — `(kernel) invalid projection` |
| `v4.30.0-rc2` | exit 0 | exit 0 |
| `v4.31.0` | exit 0 | exit 0 |
| `v4.32.0` | exit 0 | exit 0 |
| `v4.32.1` | exit 0 | exit 0 |
| `v4.32.2` | exit 0 | exit 0 |
| `v4.33.0-rc1` | exit 0 | exit 0 |

Exit 0 *is* the assertion in both columns: the exhibit's `#guard_msgs` demands
`'Paradox' does not depend on any axioms` (and the same for `boom`, `boom2` and
`irrel`), and the control's demands `(kernel) invalid projection`. A toolchain
that fixed the defect would fail the exhibit's build; a toolchain that broke the
guard would fail the control's.

`v4.32.1` and `v4.32.2` are the two releases Lean has ever cut specifically for
kernel soundness. Both ship this.

All seven rows of `MutualResultLevel.lean`'s table — including both REVERSED
controls — reproduce identically on all seven toolchains.

**`leanchecker` accepts it**, in both modes: `leanchecker ImaxPropSpelling`
and `leanchecker --fresh ImaxPropSpelling` on `v4.33.0-rc1` both exit 0, the
second having re-checked the whole `Lean.CoreM` closure from an empty
environment. That is expected rather than surprising, and it is the point of §3 of
[`CATALOG.md`](../CATALOG.md): the `leanchecker` binary shipped in the toolchain
since `v4.28.0` **shares Lean's own kernel** and is not an independent verifier,
so it inherits the defect exactly. `nanoda`, which is independent, rejects the
construction — #14613's commit message says so. This is the cross-checking
argument of *Who Watches the Provers?* working as designed, and also a reminder
that running the in-tree checker is not an instance of it.

The control is the same construction with the sort spelled `Sort 0`. Everything
up to and including proof irrelevance is accepted there — a data-carrying
proposition is legal, and that was never the defect — and only the projection is
refused, with `(kernel) invalid projection`. Acceptance of the exhibit means
something only because the control is rejected by the same procedure on the same
toolchain.

---

## What the fix does, and what it leaves

[#14613](https://github.com/leanprover/lean4/pull/14613) adds
`normalizes_to_zero` (`kernel/level.cpp`) and routes `is_prop` and
`to_cnstr_when_structure` through it;
[#14615](https://github.com/leanprover/lean4/pull/14615) routes the three
`inductive.cpp` sites — `check_constructors`, the field test inside
`elim_only_at_universe_zero`, and `init_K_target` — through it as well. After
both, every kernel decision that asks "is this sort `Prop`?" asks it
semantically. Grepping `master` at `5fa71c9141` for the syntactic forms
(`is_zero(`, `mk_Prop()`) over `src/kernel/` leaves no site that decides
`Prop`-hood: the surviving `mk_Prop()` uses build the type of `Quot`'s relation
argument (`quot.cpp:32,64,74,93`) and the placeholder type of `local_ctx`'s dummy
declaration (`local_ctx.cpp:132`), and the surviving `is_zero` uses are on `Nat`
literals (`type_checker.cpp:974,980`, `expr.h:61`).

That closes both spellings at once, and it closes them for `max 0 0` as well as
for `imax 1 0` without anybody having to enumerate the spellings. It is the right
fix.

**The inheritance step is untouched.** `m_result_level` is still the first type's
spelling on `master`, and the reversal still fails there. It is harmless *today*
only because every gate that reads it became semantic in the same wave: since all
types in a block must be `is_equivalent`, they have equal normal forms, so
`normalizes_to_zero` and `is_geq` — both of which normalize — give the same
answer for every type in the block regardless of which spelling is stored.

That is a global invariant standing in for a local one, which is precisely the
pattern [#14631](https://github.com/leanprover/lean4/pull/14631) and
[#14632](https://github.com/leanprover/lean4/pull/14632) spent the same week
converting in the other direction — `#14631`'s own justification is that
`proj_sname` equality "is not [reachable], because `infer_proj` had already
rejected mismatched names on the paths that reach it", and it was made local
anyway. The same argument applies here: `check_constructors` should gate on the
type it is checking, not on the block's first type.

One consequence is concrete rather than stylistic. A future change that makes any
`m_result_level` consumer spelling-sensitive again — or that relaxes the
same-universe requirement on mutual blocks from `is_equivalent` to something
weaker — reintroduces this construction, and the regression test for #14613 will not
catch it, because that test's subject is `is_prop` rather than the block
structure. `MutualResultLevel.lean` is the missing test.

---

## Why it is still shipped: the backport gap, second instance

`releases/v4.33.0` is at `f839b65ba4` (#14577, merged 2026-07-28). `git log
--grep` over that branch finds no cherry-pick of #14613, #14615 or #14616 — all
three merged to `master` on 2026-07-31, three days later. So the release line
that will become stable `v4.33.0` currently carries neither this fix nor
#14616's, and the published `v4.33.0-rc1` artifact (tagged 2026-07-15) predates
both by a fortnight.

That is the same gap [`2026-07-29-lean-4.33-backport-gap.md`](2026-07-29-lean-4.33-backport-gap.md)
documented for #14484 and #14576 — recurring with a different pair of fixes,
four days after it was recorded as resolved. The recurrence matters more than
either instance: a kernel soundness fix landing on `master` shortly after a
release branch's HEAD, with nothing tying the two together automatically, is a
process shape that will keep producing this, and the tracker reads `closed`
either way.

---

## Scope and honesty

* **Reachable only through metaprogramming.** The elaborator normalizes levels
  eagerly, so `Sort (imax 1 0)` is not writable in surface syntax. This is not a
  remedy, and the postmortem is explicit about why: the elaborator is
  untrusted by design, and "soundness cannot depend on an untrusted component
  refusing to build a bad term."
* **Not a `prelude` module.** Unlike the accelerator family in
  [`../KernelDefects/Lean/Accelerators/`](../KernelDefects/Lean/Accelerators/),
  this uses only genuine core constants — `Bool`, `Eq`, `congrArg`,
  `Bool.noConfusion` — so [lean4#13626](https://github.com/leanprover/lean4/issues/13626)'s
  "the kernel assumes the official prelude is used" ruling does not apply to it.
* **Not novel as a defect.** #14613 is upstream's, found and fixed within the
  #14576 response. What this report adds is the artifact — this catalog had none,
  and the Lean Kernel Arena's `proj-of-imax-prop` is an export test rather than a
  Lean module — plus the inheritance analysis, the `max 0 0` member of the class,
  and the version matrix for the released toolchains.
* **The arena already records that the released kernel fails this test.**
  `official` `4.32.2` scores 56/57 there, and `proj-of-imax-prop` is the one it
  fails. This report is the same fact reached from the other side, with a running
  `theorem Paradox : False` attached.
