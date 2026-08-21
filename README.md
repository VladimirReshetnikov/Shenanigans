# Shenanigans

This is a catalog of the ways one can write

```lean
theorem Paradox : False
```

in Lean 4 and in Rocq/Coq, and get it accepted — organised by *what it costs you
to do so*.

## The organising question: what does the audit report?

Every route to `False` gives something up, and the four top-level directories
are exactly the four answers to *what*.

| Route | The `False` is | `#print axioms` / `Print Assumptions` says | Directory |
| --- | --- | --- | --- |
| **Assume what the theory withholds** | conditional — the hypothesis is in the statement | nothing; the cost is visible in the *type* | [`Paradoxes/`](Paradoxes/) |
| **Use a sanctioned escape hatch** | closed | names the hatch — or a non-default flag was needed, or the statement is not what it looks like | [`EscapeHatches/`](EscapeHatches/) |
| **Rely on an implementation defect** | closed | **nothing at all** — and that is the bug | [`KernelDefects/`](KernelDefects/) |
| **Look for a route and fail** | there is none | — | [`Audits/`](Audits/) |

The third row is the only one that is anybody's fault. The first is a permanent
fact about type theory; the second is a documented feature being used as
designed; the fourth is a negative result.

## Contents

| Path | Contents |
| --- | --- |
| [`Paradoxes/`](Paradoxes/) | Girard/Hurkens, Coquand–Paulin, Cantor, the subsingleton-elimination barrier, and univalence, each stated as an implication from an ingredient the system withholds, each axiom-free. The univalence pair records the sharpest Lean/Rocq difference here: Lean needs one hypothesis where Rocq needs two, because proof irrelevance makes UIP definitional. Plus `Blockers.lean`, which machine-checks the exact judgment Lean refuses in every case. Lean and Rocq. |
| [`EscapeHatches/`](EscapeHatches/) | The sanctioned routes: `sorry`, `axiom`, `Admitted`, `native_decide` + `@[implemented_by]`, `Unset Guard/Positivity/Universe Checking`, rewrite rules, `-impredicative-set`, unchecked `addDecl` — and the two routes that escape the audit rather than the kernel, `Misreading.lean`/`Misreading.v`. Lean and Rocq. |
| [`KernelDefects/`](KernelDefects/) | Genuine implementation defects. Lean: the name-keyed `Nat`/`String`/`reduceBool` accelerator family, `Expr.proj` index truncation, and the **four** defects that are live on every released toolchain — a universe spelling the kernel reads two ways, a module boundary that loses `partial`, a definitional-equality *cache* whose transitive closure lets a recursor's type disagree with its computation rule ([#14806](https://github.com/leanprover/lean4/pull/14806)), and an `is_prop` that answers "no" for a term it should reject, skipping the proof-irrelevance guard on projections ([#14807](https://github.com/leanprover/lean4/pull/14807)) — with controls and a `leanchecker` verdict for each. Rocq: four fixed guard-checker and module-system defects kept as regression witnesses, plus **three live routes** — [rocq#22287](https://github.com/rocq-prover/rocq/issues/22287), a `False` with a clean `Print Assumptions` that `coqchk` still catches; [rocq#21839](https://github.com/rocq-prover/rocq/issues/21839) and **six more from the 2026-08-20 wave**, each a closed flag-free `False` that **`Print Assumptions` and `coqchk` both miss** and that escapes through a plain `Require` — `AuditBlindSextet.v` is the one file that `Require`s six of them at once and reports six clean audits; and [rocq#22352](https://github.com/rocq-prover/rocq/issues/22352), the first defect in this catalog that is in a **checker** rather than a kernel — `rocqchk -bytecode-compiler yes` reports `Modules were successfully checked` over a `False`, while plain `rocqchk` rejects the same bytes. |
| [`Audits/`](Audits/) | Searches that came up empty, which is the useful part of their output. Level/def-eq/compiler fuzzers, the `Acc` and `Expr.proj` metatheory probes, the string- and name-identity study, and — the first two Rocq entries — what a green `rocqchk` has actually established, and what `Print Assumptions` leaves out. |
| [`Reports/`](Reports/) | Write-ups suitable for upstream bug reports, each pinned to specific toolchain versions. Plus [`Counterexamples/`](Reports/Counterexamples/), a typeset edition of Stephen Dolan's *Counterexamples in Type Systems*, which is source material rather than a result — mining it for Lean analogues is what produced [`KernelDefects/Lean/ModuleSystem/`](KernelDefects/Lean/ModuleSystem/). |
| [`Upstream/`](Upstream/) | Submodules pinning the three sources this catalog cites line by line: `leanprover/lean4`, `leanprover/comparator`, `ammkrn/nanoda_lib`. **Reference material, not dependencies** — nothing here builds or imports them, and every exhibit verifies with the directory absent. |
| [`CATALOG.md`](CATALOG.md) | **The completeness ledger.** Every known route in both systems, whether or not this directory represents it, with upstream issue numbers, affected version ranges, and a coverage mark. |

## Reproducing

Each category verifies itself. Every script builds in a scratch directory
outside the repository and **asserts** the documented verdict — exit code plus
the exact audit output — rather than printing something for a human to read.
Each locates its own sources from `$PSScriptRoot`, so the working directory does
not matter.

```bash
pwsh Paradoxes/verify.ps1                  # All 11 paradox exhibits behaved as documented.
pwsh EscapeHatches/verify.ps1              # All 32 escape-hatch exhibits behaved as documented.
pwsh KernelDefects/Lean/verify.ps1         # All 6 modules behaved as documented.
pwsh KernelDefects/Lean/DefEq/verify.ps1   # All non-transitive-def-eq artifacts behaved as documented.
pwsh KernelDefects/Coq/verify.ps1          # All 41 Coq exhibits behaved as documented.
pwsh KernelDefects/Coq/Checker/verify.ps1  # The rocqchk VM-bytecode artifact behaved as documented.
pwsh Audits/Coq/CheckerCoverage/verify.ps1 # All checker-coverage measurements behaved as documented.
pwsh Audits/Coq/PrintAssumptions/verify.ps1 # All Print Assumptions blind spots behaved as documented.
```

Verified on Lean `4.32.0` (`x86_64-w64-windows-gnu`, commit `8c9756b28d64`) and
The Rocq Prover `9.2` (OCaml 4.14.2). The `DefEq/` artifacts need `4.33.0` or
later to elaborate — `Environment.addDeclCore` gained a parameter there — and
were verified on `4.33.0` and `4.34.0-rc1`.

## Ground rules for anything added here

1. **Know which category you are in, and say so in the file header.** The three
   that produce a `False` are distinguished by what the audit reports, not by
   how clever the construction is. A `False` that needs a flag is an escape
   hatch even if the flag is obscure; a `False` that needs an assumption is a
   paradox even if the assumption looks plausible.
2. **No `sorry` and no new `axiom` in `Paradoxes/`, `KernelDefects/`, or
   `Audits/`.** A `False` obtained by assuming one is worthless as evidence of a
   defect. `EscapeHatches/` is the exception and exists precisely to exhibit
   them — with the exact `#print axioms` output asserted.
3. **Every claim carries its audit, machine-checked.** In Lean that means
   `#guard_msgs in #print axioms foo`, so a toolchain change that alters the
   answer fails the build instead of silently invalidating the prose. In Rocq it
   means `Print Assumptions` with the expected substring asserted by
   `verify.ps1`.
4. **State the toolchain.** `lean` resolves its toolchain from the current
   directory, so results are meaningless without a pin. Prefer
   `elan run leanprover/lean4:<version> lean --trust=0 <file>`, and give a
   version matrix rather than a single verdict.
5. **Judge by exit code and the audit, never by grepping output for `error`.** A
   stack-overflow abort prints no `error` line and returns 127; a linter warning
   is not an error. `Lean.addDecl` is asynchronous in 4.32.x, so a `try`/`catch`
   around it silently reports kernel rejections as acceptances — use
   `set_option Elab.async false`, or the synchronous
   `(← getEnv).toKernelEnv.addDecl {}` and `Lean.Kernel.isDefEq`.
   **And in any sweep, pass `0` as `addDeclCore`'s `maxHeartbeats`.** That
   argument is not a per-call allowance: it is a *threshold* compared against a
   cumulative per-task counter, so a loop that submits many declarations in one
   command crosses it partway through and every later submission comes back
   `(kernel) deterministic timeout` — the same declaration the kernel accepted a
   moment earlier. A harness that classifies `Except.error` as "the kernel
   refused this" then reports a truncated corpus as a completed sweep.
   **Measured on v4.33.0**: 3,000 identical trivial declarations in one command
   give 133 accepted at budget 2000, 333 at 16000, 888 at 32000, 1992 at 64000,
   and 3000 at either 800000 or 0. Lean core does this correctly — `Replay.lean`
   and `Environment.lean` both call `addDeclCore 0 0`. See
   [`Audits/Method/HeartbeatBudget.lean`](Audits/Method/HeartbeatBudget.lean),
   which asserts the scaling, and note that this rule's own earlier wording
   recommended a finite budget.
6. **Give every defect a control.** Acceptance of an exhibit means something only
   if a deliberately-broken twin is rejected by the same procedure. See
   [`KernelDefects/Lean/Controls/`](KernelDefects/Lean/Controls/).
7. **Write about consistency, not about security.** The subject here is whether
   a formal system proves things that are false, and the vocabulary should say
   so. Prefer *construction*, *derivation*, *witness*, *probe*, *reachable*,
   *deliberately constructed*, *hand-edited*, *misstate*, *safeguard*. Avoid
   *exploit*, *attack*, *spoof*, *adversarial*, *malicious*, *payload*,
   *poison*, *victim*, *threat*, *tamper*, *defeat*. Nothing here is an intrusion
   into anyone's system: a kernel that accepts `False` is a mathematical defect,
   and a file that produces one is a counterexample, not a weapon.

   Two exceptions, both about fidelity to sources. Upstream's own identifiers
   stay verbatim — Rocq's `#[bypass_check(...)]` attribute, proper nouns, URLs.
   And a **quotation is never silently reworded**: where a quoted source uses the
   older vocabulary the substitution is marked with square brackets, the way an
   editorial alteration is marked in a quoted legal or scholarly text, as in
   *"an OpenAI agent then produced two [distinct constructions]"*. The reader can
   always see that the words were changed and by whom.

## Context

For the perspective the `KernelDefects/` category should be read in, see Leonardo
de Moura's [*Who Watches the Provers?*](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/).
Its argument is that a kernel bug is not a crisis but the expected cost of a
kernel fast enough to be usable, and that the safeguard is having several
independent implementations disagree: a term one kernel accepts and another
rejects is the design working. That is the standard applied here — every defect
is pinned to exact versions, given a control, and checked against an independent
judge where one exists. The
[Lean Kernel Arena](https://arena.lean-lang.org/) has since made that argument
operational, running a standard rejection corpus against sixteen registered
checkers.

De Moura's [*Postmortem for Kernel Soundness Bug
#14576*](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)
is the follow-up, and it sharpens that claim rather than repeating it. The AI-assisted
"disproof" of the Collatz conjecture that triggered the bug passed the official
kernel **and** a week-old build of `nanoda`, the main external checker — for two
entirely unrelated reasons, one bug in each. Cross-checking held, in the sense
that getting past it took two implementations failing at once; but it held only for
people running current versions of both, and the two failures turn out to be the
same omission wearing different clothes. Independence of implementations is not
independence of blind spots. [`CATALOG.md`](CATALOG.md) §3.0 works through it.

The postmortem is also worth reading for what it refuses. The suggested
remedy — restrict metaprogramming so the probe is not expressible — is
rejected outright, because the elaborator is untrusted by design and *"soundness
cannot depend on an untrusted component refusing to build a bad term."* That is
the same premise this directory is organised around: what the audit reports is
the thing that matters, and the kernel is the only component whose verdict counts.

**2026-08-18 brought two more, from the same reporter, and they sharpen the
postmortem's argument rather than settling it.**
[#14806](https://github.com/leanprover/lean4/pull/14806) — the definitional-
equality *cache* was a union-find, so its transitive closure made `is_def_eq`'s
answer depend on query order, and a recursor's type could disagree with its
computation rule — and
[#14807](https://github.com/leanprover/lean4/pull/14807) — `is_prop` answered
"not a proposition" for a term whose type does not reduce to a sort, instead of
rejecting it, so a data field could be projected out of a proof. Three axiom-free
`False`s between them, all live on `v4.33.0` and `v4.34.0-rc1`, all reproduced
here in [`KernelDefects/Lean/DefEq/`](KernelDefects/Lean/DefEq/). On two of the
three, cross-checking worked as designed. On the third, **`nanoda` accepted the
bogus proof too** — and unlike July's near-miss, which needed two unrelated bugs
in two implementations, this is one omission present in both.
[`Reports/2026-08-18-defeq-cache-and-stuck-sort.md`](Reports/2026-08-18-defeq-cache-and-stuck-sort.md)
works through it, including the correction it forces on this repository's own
2026-07-29 finding, which classified exactly the #14806 mechanism as *"not
unsoundness"*.

Lawrence Paulson's [*Broken proofs and broken
provers*](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html)
supplies the longer view from outside both systems, running back through
Isabelle/HOL, HOL88, LCF and PVS: soundness bugs recur in every prover, and their
practical consequences have been consistently small, because nobody's real
theorem turned out to depend on one. His sharper point is that the inadequacy of
a *model* of the world is a far likelier source of a wrong conclusion than the
unsoundness of a kernel.

Both cautions apply to everything below — and so does a third, which this
directory's own [`EscapeHatches/Lean/Misreading.lean`](EscapeHatches/Lean/Misreading.lean)
makes concrete: the likeliest way to end up believing something false is not a
broken kernel or a bad axiom, but a correct proof of a statement that does not
say what its reader thought it said.
