# Universe-spelling defects

> **Warning.** [`ImaxPropLaundering.lean`](ImaxPropLaundering.lean) contains a
> machine-checked proof of `False`. It is deliberately unsound, belongs to no
> Lake package, is imported by nothing, and must never be.

Category: [`KernelDefects/`](../../README.md) — closed `False`, clean audit, no
flag, no `prelude`. Full write-up:
[`Reports/2026-08-01-imax-prop-laundering.md`](../../../Reports/2026-08-01-imax-prop-laundering.md).

## The hole in one paragraph

Lean's kernel decides several things by asking whether a universe level *is
zero*. Until the July 2026 wave it asked that question two different ways: `is_geq`
and `is_equivalent` **normalize**, while `is_zero` (`kernel/level.h:106`, unchanged since) is
`kind() == Zero` and does not. So `Sort (imax 1 0)` and `Sort (max 0 0)` — both
of which denote `Prop` — are propositions to one half of the kernel and not to
the other. Feed the two halves the same inductive type through two different
spellings of its own sort and they disagree: proof irrelevance identifies two of
its inhabitants while `infer_proj` hands you a `Bool` out of them.

## Contents

| File | What it is |
| --- | --- |
| [`ImaxPropLaundering.lean`](ImaxPropLaundering.lean) | The exhibit. `theorem Paradox : False`, `#print axioms` reports nothing, `lean --trust=0` exits 0. Both spellings of zero, each giving its own `False`. |
| [`MutualResultLevel.lean`](MutualResultLevel.lean) | The laundering step measured on its own, with the order reversal as its control. No `False`. |
| [`../Controls/ImaxPropControl.lean`](../Controls/ImaxPropControl.lean) | Control. The same construction with the sort spelled `Sort 0`; the kernel refuses the projection with `(kernel) invalid projection`, asserted by `#guard_msgs`. |

## The two steps, and which one upstream fixed

The reproducer needs **two** independent weaknesses.

**Laundering.** `check_inductive_types` (`kernel/inductive.cpp:248`) sets
`m_result_level` from the **first** type of a mutual block and requires the rest
only to be `is_equivalent` to it. `check_constructors` then admits a data field
in an inductive predicate when `is_zero(m_result_level)` — syntactically. So a
type whose own sort is spelled `Sort (imax 1 0)` inherits the data-field
permission that only a syntactic `Sort 0` earns, by being declared *second*.
Reverse the two types and the same block is rejected.

**Spelling.** `type_checker::is_prop` compared `whnf(infer_type(e))` against
`Prop` syntactically, so it answered `false` for `Sort (imax 1 0)`, and
`infer_proj` therefore skipped its "a field of a proof must be a proof"
restriction.

[lean4#14613](https://github.com/leanprover/lean4/pull/14613) and
[#14615](https://github.com/leanprover/lean4/pull/14615) fix the *spelling* half,
by routing every `Prop`-hood decision through the new semantic
`normalizes_to_zero`. That closes both spellings at once and is the right fix.

**The laundering half is untouched on `master`,** and `MutualResultLevel.lean`
still reads the same there apart from the two "alone" rows, which #14615 turns
from rejections into acceptances. It is harmless today only because every
consumer of `m_result_level` became semantic in the same wave — a global
invariant standing in for a local one, which is exactly what
[#14631](https://github.com/leanprover/lean4/pull/14631) and
[#14632](https://github.com/leanprover/lean4/pull/14632) spent the same week
converting in the other direction.

## Status

| | |
| --- | --- |
| Upstream issue | [lean4#14613](https://github.com/leanprover/lean4/pull/14613), merged `master` 2026-07-31 (`17dbc815cf`) |
| Released toolchains carrying the fix | **none**, through `v4.33.0-rc1` |
| Arena test | [`proj-of-imax-prop`](https://arena.lean-lang.org/) — the one reject-test the released official kernel fails (56/57) |
| `leanchecker` | **accepts** — exit 0 on `v4.33.0-rc1` both plain and with `--fresh`. Not a surprise and not a counter-example to the cross-checking argument: `leanchecker` shares Lean's own kernel, so it inherits the defect. It is the reason the exhibit's control matters more than its `leanchecker` verdict. |
| Independent checkers | `nanoda` rejects it, per #14613's own commit message |
| Coverage before this directory | none here; the arena's version is an export test, not a Lean module |

## Reproducing

```bash
pwsh KernelDefects/Lean/Universes/verify.ps1
```

The script builds each module in a scratch directory outside the Lake workspace
and asserts the documented verdict — exit code, the exact `#guard_msgs` output,
and all seven rows of the measurement table — for the exhibit, the measurement,
and the control. It takes `-Toolchains v4.32.2,v4.33.0-rc1` and
`-SkipLeanChecker`.

These modules have their own script rather than joining
[`../verify.ps1`](../verify.ps1) because they are not `prelude`: they import
`Lean.CoreM`, so `leanchecker --fresh` would re-check the whole Lean library once
per module. The `leanchecker` step is run once, at the end.
