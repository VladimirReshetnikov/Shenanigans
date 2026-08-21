# Nine Rocq inconsistencies, mapped onto Lean 4

**2026-08-20.** On 2026-08-20 Rocq took nine `kind: inconsistency` issues in
under an hour, reported by OpenAI and credited in the issue bodies to "an LLM and
@dselsam" — the same effort behind Lean's July and August waves. Exhibits for all
nine are in [`../KernelDefects/Coq/`](../KernelDefects/Coq/) and
[`../Paradoxes/Coq/`](../Paradoxes/Coq/); the wave write-up is
[`2026-08-20-rocq-august-wave.md`](2026-08-20-rocq-august-wave.md).

This report asks the next question: **does any of it transfer to Lean 4?**

Toolchain for everything below: `elan run leanprover/lean4:v4.33.0 lean
--trust=0`, `set_option Elab.async false`, synchronous
`Kernel.Environment.addDeclCore env 0 <n> d none` matched on the `Except`,
`maxHeartbeats` passed as `0` (see
[`../Audits/Method/HeartbeatBudget.lean`](../Audits/Method/HeartbeatBudget.lean)),
judged by exit code and `#print axioms`. Kernel sources read from the **installed
toolchain**, not from a source mirror — a distinction that turned out to matter,
see the #22366 row.

## The answer

**No Rocq kernel mechanism in this wave transferred to Lean as a kernel defect.**
Eleven Rocq issue numbers in six mechanism families produced zero novel `False`
and zero novel ill-typed stored declaration.

**One row did not come back clean, and it is not a kernel row.** The Lean
counterpart question to [rocq#22352](https://github.com/rocq-prover/rocq/issues/22352)
— *what does the independent checker trust that it did not derive?* — produced a
module on which `leanchecker` **exits 0 over an axiom-free `False`**. That
falsifies a structural claim this catalog was making, and it is the one result of
this pass that became an artifact:
[`../Audits/Lean/Checkers/reducebool/`](../Audits/Lean/Checkers/reducebool/).

## The transfer table

| Rocq issue | Rocq mechanism | The Lean mechanism that would play the role | Verdict | Why |
| --- | --- | --- | --- | --- |
| [#22378](https://github.com/rocq-prover/rocq/issues/22378) | A `LetIn` in a constructor's telescope: conversion pushes a relevance annotation for *every* binder while only the surviving ones are substituted, so the relevance array shifts | No relevance array (no SProp). The transferable question is `numFields`: `declare_constructors` (`inductive.cpp:463`) counts with a bare `while (is_pi(it))` that **stops** at a `letE`; `infer_proj` (`type_checker.cpp`) walks the same telescope as `r = whnf(r)`, which zeta-reduces and **steps past** one. The two counters genuinely disagree | **no analogue** — but see the artifact | Closed by an *unrelated* check. `check_constructors` ends its walk at `is_valid_ind_app`, which needs a literal application of the inductive; a `letE` residue never is one. All four `let` placements refused as `invalid return type`, a message about something else. Measured, with the no-`let` control accepted at `numFields=2`: [`../Audits/Lean/Constructors/LetInTelescope.lean`](../Audits/Lean/Constructors/LetInTelescope.lean) |
| [#22383](https://github.com/rocq-prover/rocq/issues/22383) | Same telescope, second consumer: **cumulativity inference** miscounts the surviving binders | No cumulative inductives and no subtyping to infer. Universe comparison is an *equality* (`is_equivalent`, `level.cpp`), with no `≤` path a variance annotation could feed | **no analogue** | Two independent closures: the consumer does not exist, and the trigger term is refused as above |
| [#22387](https://github.com/rocq-prover/rocq/issues/22387) | Same telescope, third consumer: **module subtyping** disagrees about how many binders survive | No ML-module layer at all — no functor elaborator, no signature ascription, no constant-body substitution at import. The nearest surface, `section`/`variable`, is abstracted into each declaration's own telescope and kernel-checked as part of it | **no analogue** | No instantiated copy exists to be left unchecked; `import` copies `ConstantInfo`s verbatim. Plus the same refusal |
| [#22386](https://github.com/rocq-prover/rocq/issues/22386) / [#22389](https://github.com/rocq-prover/rocq/issues/22389) | `check_one_cofix` resolves the cofix component's **declared type** against the environment `push_rec_types` built — already holding the block's own recursive binders — so a `let`-bound alias means one thing to the type checker and another to the guard checker | Nothing to carry a declared type. `Lean.Declaration` (`Declaration.lean:185`, and `declaration.h:192`) has **exactly seven** constructors — `axiomDecl`, `defnDecl`, `thmDecl`, `opaqueDecl`, `quotDecl`, `mutualDefnDecl`, `inductDecl` — none a fixpoint or cofixpoint | **no analogue** | Termination is decided in the untrusted frontend and reaches the kernel as recursor applications, so the kernel never reads a declared type to license a recursion. **Two readers is the precondition; Lean has one.** And the one former that could carry mutual recursion is not on the trusted path at all: `declaration.cpp:168` makes `is_unsafe()` return **unconditionally `true`** for `MutualDefinition` |
| [#21839](https://github.com/rocq-prover/rocq/issues/21839) | The fixpoint twin — the catalog's strongest live Rocq route (`coqchk` misses it, and it escapes a plain `Require`) | Same as above | **no analogue** | Same |
| [#22382](https://github.com/rocq-prover/rocq/issues/22382) | `find_uniform_parameters` — the fifth soundness defect out of one guard-checker function: a `let` in a fixpoint's binder prefix shifts the de Bruijn baseline a recursive call's principal argument is tested against | Lean has **no guard checker**: no termination check, no subterm relation, no fixpoint former in the kernel. What it trusts instead is recursor *generation* | **no analogue** | Rocq's defect is two walks over one telescope disagreeing. Over a constructor type Lean has **one walk, used four times** (`inductive.cpp:413`, `:456`, `:630`, `:705` — the identical bare `is_pi` loop), so they cannot disagree about where the telescope ends; and the single reducing walker is fenced off by `is_valid_ind_app`. The trigger cannot be delivered either: **0 of 704** spine-`let` single specs and **0 of 292** mutual pairs accepted |
| [#22380](https://github.com/rocq-prover/rocq/issues/22380) | `cClosure.ml`: a lazy machine with its own term representation, carrying a **pending** universe substitution, and a reification step that forgets to apply it | Level substitution during reduction happens at exactly **two eager sites**, `unfold_definition_core` and `inductive_reduce_rec`, both a full one-pass `replace` | **analogue exists, sound** | None of the three ingredients is present: no second representation (no closure node, no `Case` node), no pending substitution, nothing to reify. Probed anyway: 37,026 cases over a 34-redex × 33×33 level grid, type preservation and substitution/reduction commutation both 0 failures. The 610 rejections are all the catalogued #12747 incompleteness, unreachable from the elaborator |
| [#22391](https://github.com/rocq-prover/rocq/issues/22391) | The same shape one layer up: stuck-`case` conversion rebuilds a branch's `let` context with an instance never **composed** with an outer one | The two sites that read an instance off one term and write it onto another: `mk_nullary_cnstr` and `expand_eta_struct` (`inductive.cpp:88-111`) | **analogue exists, sound** | Because nothing is deferred, "composition" is ordinary substitution into an already-substituted body, so the uncomposed-instance shape has nowhere to arise. 14,400 transplant cases, 0 anomalies, 14,400 mangled controls all rejected |
| [#22366](https://github.com/rocq-prover/rocq/issues/22366) | A functor applied under `Unset Guard Checking` substitutes an `Inline` parameter body into the instantiated constant without re-checking it **and without recording the flag use** | `src/Lean/AddDecl.lean`'s `exportedInfo?` stub — the [lean4#14609](https://github.com/leanprover/lean4/pull/14609) site | **no analogue; and the positive control now rejects** | The attribute half is dead by construction: every attribute lives in `Kernel.Environment.extensions`, and the C++ `class environment` exposes only `find` / `add` / `is_quot_initialized` / `get_diag` — `type_checker.cpp` never reads an extension. The functor half has no layer to live in. **And #14609 is fixed in shipped v4.33.0**, which three files in this repo denied; see below |
| [#22352](https://github.com/rocq-prover/rocq/issues/22352) | `rocqchk` typechecks the bodies and then **runs VM bytecode it read from the file** instead of deriving it: exit 0, `Modules were successfully checked`, over a `False` with a clean `Print Assumptions` | `leanchecker` → `Lean.Environment.replay`; the compiled-code hook is `reduce_native`, tried **first** in `whnf`, dispatching to the IR interpreter | **ANALOGUE EXISTS AND IS REACHABLE** | See below. `leanchecker` exits 0 over an axiom-free `False` |
| [#22362](https://github.com/rocq-prover/rocq/issues/22362) | `rocqchk -norec` gives different verdicts on the same files in the two argument orders | `leanchecker` builds its target list and spawns one independent replay per module, each against that module's own imports | **no analogue for order**; a heuristic sibling exists | No shared interning table, so no module can be pulled in as a dependency and thereby skipped. Both orders measured on the same two files: identical verdict, identical message. The sibling: bare `leanchecker` picks its targets from the Lake manifest by `manifest.name.capitalize`, with an in-source TODO conceding the assumption, and silently skips libraries it did not guess |

## The row that did not come back clean

`leanchecker` **does** replay `Lean.reduceBool`. The catalog said it "cannot
replay it at all", and that was the basis for calling §4.7's empty Lean column
structural. The evidence is the checker's own refusal message on the
module-local case, which **names the declaration it was replaying**:

    uncaught exception: while replaying declaration 'rb_nativeL':
    (kernel) (interpreter) unknown declaration 'probeL'

It runs the hook; the interpreter behind it resolves *imported* constants and not
constants local to the module under replay. So take the free-name construction of
[`ReduceBoolFreeName.lean`](../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean)
and move `probe` into an imported module — a change that leaves the kernel's
verdict, the proof term and `#print axioms` untouched:

| Module | `#print axioms` | `leanchecker` |
| --- | --- | --- |
| `P.Boom` — `boom : False`, `probe` **imported** | *does not depend on any axioms* | **exit 0 — ACCEPTED** |
| `P.Downstream` — the same `False` across a plain `import` | *does not depend on any axioms* | **exit 0 — ACCEPTED** |
| `P.LocalControl` — the same `False`, `probe` **module-local** | *does not depend on any axioms* | exit 1 — REJECTED |

All three properties of #22352's signature hold at once: a proof of `False`, a
clean audit, and an independent checker reporting success.

**The axiom accounting does not cover it.** The natural rebuttal is that Lean
tracks native evaluation with `Lean.ofReduceBool` and `Lean.trustCompiler`, so an
auditor would see it — and that is true of the *sanctioned* channel through
`native_decide`. The free-name route uses no axiom at all: the kernel runs
compiled code because a constant is *named* `Lean.reduceBool`. That channel is
audited by nothing.

**What this does not claim.** The `False` is not new and the kernel behaviour is
not a new defect — upstream closed exactly this as working-as-intended
([lean4#13626](https://github.com/leanprover/lean4/issues/13626)) and this
catalog files it under §2.3. It needs `prelude`, so it is not reachable from
ordinary source. The finding is about the **checker's verdict**, which is what
§4.7 is a table of.

## Corrections this pass forced

1. **§4.7 and §4 were wrong about `leanchecker` and `Lean.reduceBool`.** Both
   said it "cannot replay it at all". It replays it. Corrected in
   [`../CATALOG.md`](../CATALOG.md), with the artifact above.
2. **lean4#14609 is fixed in shipped v4.33.0**, and three places said otherwise.
   [`../KernelDefects/Lean/ModuleSystem/README.md`](../KernelDefects/Lean/ModuleSystem/README.md)
   said "Released toolchains carrying the fix: **none**" and "On
   `releases/v4.33.0`? **no** — that branch is still at `f839b65ba4`";
   [`../KernelDefects/README.md`](../KernelDefects/README.md) said "**four**
   defects live on every released toolchain". Measured both ways: the exhibit
   builds on its pinned `v4.32.2` and is refused by `v4.33.0` with
   `(kernel) invalid declaration, it uses unsafe declaration 'partialFalse'`,
   exit 1. It is now a regression witness, and the count is three.

   **The methodology lesson is worth more than the correction.** The stale
   reading came from a source mirror checked out on `master`; the installed
   toolchain's own `src/lean/Lean/AddDecl.lean:121` reads
   `isUnsafe := defn.safety != .safe`. *A source mirror is not evidence about a
   release branch.* Read the toolchain elan actually runs.

## Verification status

The repository's ground rules ask that a claim entering the catalog be measured
rather than reported. Split accordingly.

**Verified directly for this report** — re-run from source or re-measured on the
installed toolchain: the two-walk asymmetry and all four `let` placements
(#22378); the seven `Declaration` constructors and `MutualDefinition`'s
unconditional `is_unsafe()` (#22386); #14609's status on both toolchains; every
`leanchecker` verdict in the table above, including the control; and the
`quotInit := !imports.isEmpty` heuristic noted below.

**Not independently re-measured** — the large sweep counts (37,026 universe
cases, 14,400 transplants, 5,640 recursor computation rules, the 704/292
spine-`let` figures). They come from the six probe agents, are reported here as
theirs, and none of them is load-bearing for a "no analogue" verdict: each such
verdict rests on a source fact stated in the same row.

## Loose ends worth someone's time

* **`Kernel.Environment.quotInit` is not serialised.** It is re-derived by
  heuristic: `Lean/Environment.lean:2365` reads
  `quotInit := !imports.isEmpty -- We assume `Init.Prelude` initializes quotient
  module` (verified verbatim). That makes it a third entry on §1.2's list of
  kernel-affecting flags whose use is not recorded, beside `debug.skipKernelTC`
  and `trustLevel` — and the only *derived* one.
* **`addDeclWithoutChecking` cannot bypass inductive checking**, so for inductives
  it is not the escape hatch §1.2 lists it as: `environment::add(d, check)`
  dispatches `declaration_kind::Inductive` to `add_inductive(d)` and **drops the
  flag** (`environment.cpp:279`, verified).
* **An upstream comment worth filing.** `is_valid_ind_app`'s refusal to reduce is
  load-bearing for `numFields`, and nothing in the code says so. Teaching
  `check_constructors` to zeta-reduce before it — a natural-looking
  generalisation — would open the #22378 disagreement immediately. That is the
  whole point of
  [`../Audits/Lean/Constructors/LetInTelescope.lean`](../Audits/Lean/Constructors/LetInTelescope.lean).

## What the wave says about the catalog's structural claim

[`../KernelDefects/README.md`](../KernelDefects/README.md) argues that the two
systems' defects cluster in different places, and this wave is a real test of it.
The claim survives — nothing here moves Lean's cluster — but it is stated at the
wrong altitude in one respect worth recording.

**The operative variable is not "which subsystem" but "how many independent walks
over one binder telescope, and whether they agree what a binder is."** Seven of
the eleven rows turn on a `let` appearing where a walker counts binders. Rocq
admits `let` in constructor telescopes, fixpoint binder prefixes, match-branch
contexts and module component types, and then lets six different consumers walk
them with their own notion of "next binder". Lean is safe here not because it
thought about `let`s but because of a structural accident worth naming: over a
constructor type there is **one walk, used four times**, and the one reducing
walker is fenced off from disagreeing with it by a syntactic check that never
reduces.

So "Lean has no guard checker" is true but weak. The sentence that earns its keep
is: *Rocq's #22378, #22382, #22383 and #22387 are one telescope read by
disagreeing walkers; Lean has one walk, used four times, behind an invariant that
makes the fifth agree with it.*

**And the checker column should stop being described as structurally empty.** It
was empty by luck. The luck was that the one exhibit put its evaluated constant
in the same module as its proof.
