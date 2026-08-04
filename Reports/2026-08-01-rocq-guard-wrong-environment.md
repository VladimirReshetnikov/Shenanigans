# rocq#21839 on Rocq 9.2: the first route both `Print Assumptions` and `coqchk` miss

**Date:** 2026-08-01
**Toolchain:** The Rocq Prover 9.2 (`coq-core` 9.2.**0**, OCaml 4.14.2).
**Artifacts:** [`KernelDefects/Coq/GuardChecker/WrongEnvReduction.v`](../KernelDefects/Coq/GuardChecker/WrongEnvReduction.v)
and [`WrongEnvReductionEscape.v`](../KernelDefects/Coq/GuardChecker/WrongEnvReductionEscape.v).
**Upstream:** [rocq-prover/rocq#21839](https://github.com/rocq-prover/rocq/issues/21839),
"Incorrect environment passed to reduction during guard checking", fixed by
[#21845](https://github.com/rocq-prover/rocq/pull/21845), milestone 9.2.1.

---

## Claim

`Definition oops : False` — no flag, no axiom, no tactic, no paradox encoding —
accepted by the installed Rocq, with **both** of this catalog's audit channels
reporting nothing:

```
$ coqc WrongEnvReduction.v ; echo EXIT=$?
Closed under the global context      (oops)
Closed under the global context      (oops_const)
Closed under the global context      (one_eq_two : 1 = 2)
EXIT=0

$ coqchk -o WrongEnvReduction ; echo EXIT=$?
Modules were successfully checked
* Axioms: <none>
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
EXIT=0
```

That last line is `coqchk` *positively certifying* the one thing that is false:
the fixpoint **is** unsafe.

CATALOG §4.1 lists #21839 as affecting 8.16–9.2.0 and fixed in 9.2.1/9.3, marked
**gap**. The installed toolchain is 9.2.**0**, inside the affected range, so this
is not a regression witness — it is a proof of `False` the machine running
`verify.ps1` accepts today.

---

## Why this is the strongest route in the repository

The catalog's organising question is *what does the audit report*. Every route
catalogued until now fails at least one of these two tests. This one fails
neither, and it propagates.

| | `Print Assumptions` | `coqchk` | escapes to a consumer |
| --- | --- | --- | --- |
| Rocq flag hatches ([`EscapeHatches/Coq/TypingFlags.v`](../EscapeHatches/Coq/TypingFlags.v)) | names the flag | rejects | — |
| [rocq#22287](2026-08-01-rocq-universe-flag-desync.md), found earlier today | **silent** | rejects | **no** — `Require` fails at the `Require` line |
| Lean [`ModuleSystem/`](../KernelDefects/Lean/ModuleSystem/) (#14609) | **silent** | `leanchecker` rejects | yes |
| Lean [`Universes/`](../KernelDefects/Lean/Universes/) (#14613) | **silent** | `leanchecker` accepts; `nanoda` rejects | yes |
| **rocq#21839, here** | **silent** | **accepts** | **yes** |

The escape is the second artifact, and it is ordinary Rocq:

```coq
Require Import WrongEnvReduction.
Definition escaped : False := oops.
Definition anything : 2 + 2 = 5 := match escaped return 2 + 2 = 5 with end.
```

`coqc` exit 0, both `Print Assumptions` lines clean, and `coqchk` on the
*downstream* `.vo` also clean.

---

## Why `coqchk` misses it, and why that is not a surprise

The contrast with [rocq#22287](2026-08-01-rocq-universe-flag-desync.md) is exact
and instructive, because the two were found on the same day on the same machine.

* #22287 collapses the universe hierarchy. The inconsistency is written into the
  `.vo`'s **universe graph**, which `coqchk` recomputes and any `Require`
  re-checks — so both catch it, and the `False` is confined to one file.
* #21839 produces a term that is **well typed**. Nothing about it is wrong except
  that a *guardedness* decision was made with the wrong environment. `coqchk` is
  not an independent implementation of the guard checker — at 9.2.0
  `checker/mod_checking.ml` type-checks bodies with `Typeops.infer`, i.e. the
  kernel's own — so it re-runs the same code and reaches the same wrong answer.

This is the sharp form of the point *Who Watches the Provers?* makes: independent
implementations catch what they implement independently. `coqchk` shares Rocq's
guard checker the way `leanchecker` shares Lean's kernel, and the July 2026
postmortem's own lesson — that #14576 passed the official kernel *and* `nanoda`
for two unrelated reasons — is the same lesson from the other side. A second
checker is only a second opinion where it is a second implementation.

---

## Scope and honesty

* **Not a new defect.** #21839 is upstream's, reported and fixed. What is new is
  the artifact — CATALOG marked it a **gap** — the measurement on 9.2.0, and the
  two-channel-silent + escapes characterisation, which the issue does not state.
* **Fixed upstream.** Anyone on 9.2.1 or later is unaffected. The exhibit will
  flip from `accept` to `reject` on such a toolchain, and `verify.ps1` will fail
  loudly when it does — which is exactly what a regression witness should do once
  it stops being live.
* **Reachable from ordinary source.** No metaprogramming; the issue text is a
  direct `Definition oops : False`.
* **The controls are in the file**, and each was run standalone to capture its
  verbatim rejection: deleting the ltac-built inner fixpoint, and a one-character
  change to the recursive argument, each turn acceptance into
  `Recursive definition of ... is ill-formed`.
