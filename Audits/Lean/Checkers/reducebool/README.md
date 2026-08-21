# `leanchecker` accepts an axiom-free `False`

**Category (see [`../../../../README.md`](../../../../README.md)): audit.** The
`False` here is not new and its mechanism is
[out of scope by upstream policy](../../../../CATALOG.md) (§2.3). What is new,
and what this directory exists for, is the **checker's verdict on it**.

    pwsh Audits/Lean/Checkers/reducebool/verify.ps1

## The measurement

Four modules, one construction, on `leanprover/lean4:v4.33.0`. The only
difference between the accepted `False` and the rejected one is which module the
evaluated constant lives in.

| Module | Contains | `#print axioms` | `leanchecker` |
| --- | --- | --- | --- |
| [`P/Base.lean`](P/Base.lean) | `probe`, in its own module | — | exit 0 |
| [`P/Boom.lean`](P/Boom.lean) | `boom : False`, `probe` **imported** | *does not depend on any axioms* | **exit 0 — ACCEPTED** |
| [`P/Downstream.lean`](P/Downstream.lean) | `downstream : False` across a plain `import` | *does not depend on any axioms* | **exit 0 — ACCEPTED** |
| [`P/LocalControl.lean`](P/LocalControl.lean) | the same `False`, `probe` **module-local** | *does not depend on any axioms* | exit 1 — REJECTED |

## What it corrects

[`CATALOG.md`](../../../../CATALOG.md) §4.7 said the Lean column of its checker
table was empty *"for a structural reason rather than a lucky one"*, because the
kernel's only compiled-code hook is `Lean.reduceBool` and `leanchecker`
*"cannot replay it at all — which is why
[`ReduceBoolFreeName.lean`](../../../../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean)
is the one exhibit in that directory `leanchecker` rejects."*

Both halves are false, and the control is what shows it. `leanchecker` refuses
`P.LocalControl` with:

    uncaught exception: while replaying declaration 'rb_nativeL':
    (kernel) (interpreter) unknown declaration 'probeL'

It **names the declaration it was replaying**. So it does not decline the hook —
it runs it, and the interpreter behind `reduce_native` fails to resolve a
constant that is local to the module under replay. Imported constants it
resolves fine. Move one definition into an imported module and the same `False`
is accepted.

So `ReduceBoolFreeName.lean` is rejected because of **where it happens to put
`probe`**, not because of anything structural about `leanchecker`. The reason
§4.7's Lean column was empty was luck, and this is what it looks like when the
luck runs out.

## What it does not claim

**The `False` is not new and the kernel defect is not new.** It is the
free-name hook of
[`ReduceBoolFreeName.lean`](../../../../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean),
unchanged — `Init.Prelude` leaves the name `Lean.reduceBool` free, the kernel's
`reduce_native` is keyed on that name and tried first in `whnf`, so defining it
gives the kernel two disagreeing rules for one constant. Upstream closed exactly
this as **working-as-intended**
([lean4#13626](https://github.com/leanprover/lean4/issues/13626)), and this
repository files it under §2.3 for that reason. `Lean.reduceBool` is also
deprecated on v4.33.0 in favour of asserting native evaluations with axioms.

**It needs `prelude`**, so it is not reachable from ordinary Lean source, and
that is the same containment §2.3 already records.

The finding is therefore narrow and specific: *the property "`leanchecker`
rejects it" was doing work in §4.7's argument, and it does not hold.* An
independent checker's value is that it catches what the kernel missed; here it
catches the same thing the kernel missed only when the construction is arranged
one way, and a one-line rearrangement that changes nothing about the kernel's
verdict changes the checker's.

## Why the axiom accounting does not cover this

The obvious rebuttal is that Lean tracks native evaluation with axioms: the
honest route through `native_decide` puts `Lean.ofReduceBool` and
`Lean.trustCompiler` into `#print axioms`, so a reader auditing the proof would
see that compiled code was trusted — which is exactly the half
[rocq#22352](https://github.com/rocq-prover/rocq/issues/22352) is dangerous for
lacking, since `Print Assumptions` reports nothing there.

**That rebuttal does not apply to this construction, and the difference is the
point.** The free-name route uses no axiom at all — the kernel runs compiled code
because a constant is *named* `Lean.reduceBool`, not because anything invoked the
sanctioned hook. So all three properties hold at once, which is #22352's
signature exactly:

* the module contains a proof of `False`,
* `#print axioms` reports **"does not depend on any axioms"**,
* the independent checker exits **0**.

The axiom accounting is the mitigation for the *sanctioned* channel. This is the
unsanctioned one, and it is audited by nothing.

## Provenance

Found on 2026-08-20 while adapting the 2026-08-20 Rocq wave to Lean — the Lean
counterpart question to
[rocq#22352](https://github.com/rocq-prover/rocq/issues/22352), where
`rocqchk -bytecode-compiler yes` reports success over a `False` because it runs
VM bytecode it read from the file instead of deriving it from the bodies. The
shape is the same one §4.7 draws: **a checker trusting something it did not
derive.** Rocq's checker trusts a spliced segment; Lean's checker trusts an
interpreter whose constant resolution depends on module placement.

See [`../../../../Reports/2026-08-20-rocq-wave-to-lean.md`](../../../../Reports/2026-08-20-rocq-wave-to-lean.md)
for the full transfer table this came out of.
