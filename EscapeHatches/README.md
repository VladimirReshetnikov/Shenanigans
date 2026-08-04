# Escape hatches: the sanctioned routes to `False`

Every proof assistant ships with ways to assert things the kernel has not
verified. They exist because the alternative — a system in which nothing can be
stubbed, no compiled code can be trusted, and no experimental extension can be
tried — would not be usable. This directory catalogs them, in both systems, with
the audit output for each machine-checked.

Category (see [`../README.md`](../README.md)): a route belongs here when the
`False` is **closed** (no hypothesis in the statement) but *something* discloses
the cost — an entry in `#print axioms` / `Print Assumptions`, or a non-default
compiler flag, or, in the last two files, only a careful reading of the
statement.

Contrast with [`../KernelDefects/`](../KernelDefects/), where the `False` is
closed and the audit reports **nothing**. That is the whole distinction this
directory exists to draw.

## Contents

### Lean

| File | Route | What `#print axioms` reports |
| --- | --- | --- |
| [`Lean/Sorry.lean`](Lean/Sorry.lean) | `sorry` — and the `sorry` you did not write: a failed tactic or a type error patches the declaration and it still enters the environment | `sorryAx` |
| [`Lean/Axioms.lean`](Lean/Axioms.lean) | `axiom`, including the innocuous-looking kind; plus the realistic failure — an over-general statement under `autoImplicit` | the axiom, by name |
| [`Lean/Unsafe.lean`](Lean/Unsafe.lean) | **Negative result.** `unsafe` and `partial` do *not* get you there: the kernel refuses to let a safe declaration depend on an unsafe one, and `partial` needs `Inhabited` | n/a |
| [`Lean/NativeDecide.lean`](Lean/NativeDecide.lean) | `@[implemented_by]` + `native_decide`. The one route that yields a closed, `sorry`-free, `unsafe`-free `theorem Paradox : False` from two core attributes | a fresh per-use axiom, `<thm>._native.native_decide.ax_N_M` |
| [`Lean/Metaprogramming.lean`](Lean/Metaprogramming.lean) | `set_option debug.skipKernelTC true` + hand-built `addDecl`. The only Lean route the audit cannot see | **nothing** — but `leanchecker` rejects it |
| [`Lean/Spoofing.lean`](Lean/Spoofing.lean) | Shadowed names, claimed glyphs, homoglyph identifiers: the statement is not what it reads as | nothing, correctly |
| [`Lean/ArenaTrustedMetadata.lean`](Lean/ArenaTrustedMetadata.lean) | Overwrites a derived `ConstantInfo` in `Environment.checked.constants`, past the kernel. Three closed `theorem … : False`; the kernel runs on every declaration and is correct on the input it was given | needs `module` + `import all Lean.Environment` — a disclosure in the *source*, with none in the audit | **nothing at all**; `leanchecker` rejects |
| [`Lean/Spoofing.BareCyrillic.lean`](Lean/Spoofing.BareCyrillic.lean) | Companion control: a bare Cyrillic homoglyph is a **parse error** in Lean, unlike in Rocq | n/a — must be rejected |

### Rocq

| File | Route | Flag needed | What `Print Assumptions` reports |
| --- | --- | --- | --- |
| [`Coq/Assumptions.v`](Coq/Assumptions.v) | `Admitted`, `Axiom`, `Program` obligations | — | the assumption, by name |
| [`Coq/TypingFlags.v`](Coq/TypingFlags.v) | `Unset Guard Checking` (non-terminating fixpoint), `Unset Positivity Checking` (Curry), `Unset Universe Checking` (Hurkens), `#[bypass_check(...)]` | — | `loop is assumed to be guarded.` / `Curry is assumed to be positive.` / `… relies on an unsafe hierarchy.` |
| [`Coq/RewriteRules.v`](Coq/RewriteRules.v) | `Symbol` + `Rewrite Rule` — unchecked definitional equalities injected straight into kernel conversion | `-allow-rewrite-rules` | the symbols, plus `Theory: Rewrite rules are allowed` |
| [`Coq/ImpredicativeSet.v`](Coq/ImpredicativeSet.v) | Chicli–Pottier–Simpson: impredicative `Set` is safe alone, fatal with decidability in `Set` | `-impredicative-set` | `Theory: Set is impredicative` |
| [`Coq/ComputeMachines.v`](Coq/ComputeMachines.v) | `vm_compute` / `native_compute` — kernel-level conversion machines, not tactics: the kernel re-runs them at `Qed`, so the trusted base becomes `coq_interp.c` or the OCaml native compiler invoked at proof-checking time | — | **nothing.** `Print Assumptions` clean, `Print Typing Flags` unchanged, `coqchk` says `Axioms: <none>`. Carries a **correction** to `CATALOG.md` §1.2: `Opaque` was never load-bearing against conversion, and is the only one of Rocq's three hiding mechanisms these defeat |
| [`Coq/Spoofing.v`](Coq/Spoofing.v) | Redefined names, redefined notations, redefined `=`, homoglyphs | — | `Closed under the global context`, correctly |
| [`Coq/ExtractConstant.v`](Coq/ExtractConstant.v) | `Extract Constant` splices arbitrary OCaml over a *verified* function. The refman's own words: the replacement text "is not checked at all by extraction, even for syntax errors" | — | **nothing** — and it is right to report nothing, because nothing happened *inside* Rocq | 
| [`Coq/DeclareMLModule.v`](Coq/DeclareMLModule.v) | Loads native code into `coqc`'s address space, sharing the kernel's mutable environment — how `lia`, `firstorder`, `Derive` and extraction itself all arrive | — | **nothing**; `coqchk` does not read the plugin's name |

## Reproducing

```bash
pwsh EscapeHatches/verify.ps1
```

Expected final line: `All 32 escape-hatch exhibits behaved as documented.`

`ComputeMachines.v`, `ExtractConstant.v` and `DeclareMLModule.v` are the exhibits
whose cost is invisible to **both** audit channels — they are `CATALOG.md` §1.2's
three untracked Rocq hatches — so the last two are checked differently: not by
what Rocq *reports* but by what Rocq *writes out*. `verify.ps1` compiles the emitted OCaml,
runs it, and asserts three specific disagreements between the extracted program
and the theorems proved about the Coq functions — `secret = false` in Rocq,
`true` in the binary. That is the honest form of the claim, and it means a future
Rocq that started checking `Extract Constant` would fail this harness loudly
instead of passing it silently.

Neither is a defect: both are documented, and the cost is paid entirely outside
the system by whoever runs the binary. `Declare ML Module` has no Lean row in
[`../CATALOG.md`](../CATALOG.md) §1.2 at all — Lean has no supported way to load
native code into `lean`'s process and let it edit the environment, which makes it
the single largest structural difference between the two trusted computing bases.
`DeclareMLModule.plugin.ml` ships as source and is **not** loaded by the harness;
its header records exactly what was measured, what was not, and why (the `.cmxs`
builds but is ABI-incompatible with this opam switch's prebuilt binaries).

Every Lean file carries its own `#guard_msgs` assertions — including the exact
`#print axioms` output and every expected error message — so `lean` exiting 0
already means all of that matched. The script adds the Rocq substring assertions
and, for the two flag-gated Rocq files, the **controls**: each must be *rejected*
without its flag, with the exact refusal recorded
(`requires passing the flag "-allow-rewrite-rules"`, and
`universe inconsistency: Cannot enforce Set+1 <= Set`).

Verified on Lean `4.32.0` and The Rocq Prover `9.2`.

## Three things this collection settles

**1. The two systems draw the line in different places, and neither is
uniformly safer.**

Rocq lets you switch off each kernel check individually and then *tells you* —
`Print Assumptions` names the disabled flag, and the report is per-declaration.
Lean has no such flag, and no such report: its only comparable route,
`debug.skipKernelTC`, bypasses the kernel wholesale and is invisible to
`#print axioms`. Against that, Lean's `unsafe`/`partial` quarantine is enforced
*by the kernel* — `(kernel) invalid declaration, it uses unsafe declaration` —
where Rocq's `Unset Guard Checking` is a real, documented route to `False`.

**2. `native_decide` no longer means what most write-ups say it means.**

`Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool` and `Lean.ofReduceNat`
are all deprecated since 2026-02-01, with the message *"in-kernel native
reduction is deprecated; assert native evaluations with axioms instead"*. Under
[RFC #12216](https://github.com/leanprover/lean4/issues/12216), shipped in
`v4.29.0`, `native_decide` runs the computation in the tactic and emits **one
fresh axiom per use**, named after the theorem that used it. `Lean/NativeDecide.lean`
asserts the current name. This is strictly better for auditing, and it is why
the `Lean.reduceBool` exhibit in
[`../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean`](../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean)
documents a mechanism on its way out.

**3. The audit is not the last line of defence — reading the statement is.**

`Spoofing.lean` and `Spoofing.v` produce theorems that are entirely honest, fully
closed, and accepted by every checker, whose displayed statements are lies. No
assumption-tracking machinery in either system can catch this, and none is
supposed to. The lexical half of the question — *which* confusable identifiers a
system will actually accept — is studied systematically for Lean in
[`../Audits/Lean/StringIdentity/`](../Audits/Lean/StringIdentity/), whose answer
is mildly reassuring: every confusable Lean admits requires French quotes `«…»`,
which are conspicuous in source. Rocq accepts bare Cyrillic homoglyphs, which
are not.
