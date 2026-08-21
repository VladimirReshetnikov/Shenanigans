# A recursor keeps a dependency its module's exported view drops

**Category (see [`../../../../README.md`](../../../../README.md)): kernel
defect.** Closed `False`, no flag, no `sorry`, and `#print axioms` reports
nothing.

> **Warning.** This directory contains a machine-checked proof of `False` that
> **every released Lean toolchain accepts**, including `v4.34.0-rc1`.

    pwsh KernelDefects/Lean/ModuleSystem/classrec/verify.ps1
    pwsh KernelDefects/Lean/ModuleSystem/classrec/verify.ps1 -Toolchains v4.32.2,v4.33.0,v4.34.0-rc1

[lean4#14875](https://github.com/leanprover/lean4/issues/14875), reported
2026-08-21 by [@nielstron](https://github.com/nielstron) and **open**. The issue
body credits the discovery to **GPT 5.6 Sol**, which makes this the fourth
model-driven wave this catalog records — after Lean's July and August waves and
the [2026-08-20 Rocq wave](../../../../Reports/2026-08-20-rocq-august-wave.md),
all of which came from the same kind of effort.

## The mechanism

Three modules, and the whole defect is in what the middle one *exports*.

| Module | What it does |
| --- | --- |
| [`IS/ClassHidden.lean`](IS/ClassHidden.lean) | `public def ClassHidden : Prop := False` |
| [`IS/ClassProducer.lean`](IS/ClassProducer.lean) | `import all` the above, then declare `public class inductive ClassVictim` whose constructor takes `ClassWrap ClassVictim = ClassHidden → ClassVictim`, and an instance `classValue` |
| [`IS/ClassConsumer.lean`](IS/ClassConsumer.lean) | plain `import` of the producer, declare *its own* `inductive ClassHidden`, apply `ClassVictim.rec` — `False` |

`import all` is what lets the producer see through `ClassHidden` to its body, so
that `fun h => False.elim h` typechecks. But because `ClassHidden` arrived that
way, it is **omitted from the producer's exported view** — while the generated
recursor `ClassVictim.rec` still refers to it.

The consumer therefore receives a recursor with a dependency it cannot see, and
is free to use that global name for something else. `ClassVictim.rec` was
*checked* against `ClassHidden := False` and is *interpreted* against the
consumer's one-constructor `ClassHidden`. The minor premise's induction
hypothesis wants a proof of the local `ClassHidden`, `ClassHidden.intro` supplies
it, and out comes the `False` the original type promised.

## What was measured

On `v4.32.2`, `v4.33.0` **and** `v4.34.0-rc1` — all three identical:

| | |
| --- | --- |
| `lake build` | **exit 0** |
| `#print axioms boom` | *'boom' does not depend on any axioms* — asserted in-file by `#guard_msgs` |
| `leanchecker IS.ClassConsumer` | **rejects**: `while replaying declaration 'ClassHidden': (kernel) constant has already been declared 'ClassHidden'` |
| control — `import all` → `import` | producer stops building: `Application type mismatch` at the `False.elim` |
| control — withdraw the redefinition | consumer stops building: `Unknown constant ClassHidden` |

The second control is the finding stated as a measurement. With the redefinition
gone the name is **not visible to the consumer at all** — which is exactly the
claim that the producer's exported view omits a dependency its exported recursor
still has. The consumer is not overriding anything it can see; it is filling a
hole nothing told it was there.

The first control isolates the trigger to a single token: without `import all`
the producer cannot see that a `ClassHidden` is a `False`, so `classValue` does
not typecheck and there is nothing to export.

## Where it sits

**`leanchecker` catches this one**, which distinguishes it from the two live
`DefEq/` defects and puts it in the same position as
[`../paradox/`](../paradox/) (#14609): a defect in `src/Lean/`, not
`src/kernel/`, that the independent replay refuses. The catalog's §4.7 table
cares about exactly that column.

It is also the **second** proof of `False` to come out of Lean's module system,
which was introduced in `v4.31`. That has forced a correction to
[`../../../README.md`](../../../README.md)'s standing claim that Rocq's module
system has "no Lean counterpart at all": the functors, applicative module
equality and delta-resolver still have none, but Lean grew an **export view**,
and a view that omits something the exported term depends on is the same class of
defect by another route.

## Upstream's suggested fixes

The issue lists three, and they are worth recording because they bracket the
design question: export the dependency too, hide the recursor, or reject the
producer. Nothing here takes a position on which is right.
