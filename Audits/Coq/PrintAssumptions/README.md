# Three things `Print Assumptions` does not tell you, on the toolchain you have

Category (see [`../../../README.md`](../../../README.md)): **audit**. No proof of
`False` is produced here. What is measured is that Rocq's own audit command
answers `Closed under the global context` about a constant whose honest answer
names an axiom, or a kernel check that was switched off.

Each is paired with a control that the *same* procedure on the *same* toolchain
reports correctly, so "the audit is silent" is a measurement rather than an
absence.

```bash
pwsh Audits/Coq/PrintAssumptions/verify.ps1
```

Expected final line: `All Print Assumptions blind spots behaved as documented.`
Needs `rocq` and `rocqchk` on `PATH`.

## Why this exists

[`CATALOG.md`](../../../CATALOG.md) §1.4 used to say, of `Print Assumptions`:
*"Mostly false, and better than its reputation: it reports every `bypass_check`
flag by name."* The first half is still fair. The second half is false on Rocq
9.2, and this directory is why that row now says so.

## 1. rocq#21825 — the *type* of a definition is not traversed

Merged 2026-03-26 (Jason Gross) from a branch point past the `V9.2.0` tag, so
the fix is carried only by the `V9.3+rc1` prerelease: **live on every released
Coq/Rocq**.

| File | What it asks | Answer on 9.2.0 |
| --- | --- | --- |
| [`ViaType.v`](ViaType.v) | axiom reachable only through the **type** | `Closed under the global context` |
| [`ViaType.v`](ViaType.v) | same axiom in the **body** (control) | `Axioms: ax3 : nat` |

**The escalation is the part that matters**, because `Print Assumptions` walks
the same reachable set to report `bypass_check` flags:

| File | What it asks | Answer on 9.2.0 |
| --- | --- | --- |
| [`GuardViaType.v`](GuardViaType.v) | guard flag reachable only through the **type** | `Closed under the global context` |
| [`GuardViaBody.v`](GuardViaBody.v) | the same flag through the **body** (control) | `Axioms: loop is assumed to be guarded.` |

Same flag, same `Unset Guard Checking` fixpoint, two answers, decided by whether
the taint sits in a type or a body.

Two precision points. The gap is constants that **have a body** — bodiless ones
were always traversed, which is how `Axiom ax : nat` was ever reported at all.
And the fix's added `match obj with` handles `GlobRef.ConstRef` only;
`VarRef`/`IndRef`/`ConstructRef` fall through unchanged. In the other direction,
honesty about severity: the concealed occurrences here are convertibility-
erasable, so no *essential* dependency is being hidden. **This is not a proof of
`False` and the harness does not claim one.**

## 2. rocq#20550 — `abstract` loses the declaration's typing flags

Labelled `kind: inconsistency` upstream, closed 2026-04-24 with the fix on
`master`/`v9.3` only — **live on 9.2.0**. Absent from upstream's
`dev/doc/critical-bugs.md`, and absent from this repository's catalog until now.

[`Abstract.v`](Abstract.v):

| | Answer on 9.2.0 |
| --- | --- |
| `#[bypass_check(universes=no)] Lemma bar … Proof. abstract the_tac. Qed.` | `Closed under the global context` |
| the same lemma, same tactic, **without** `abstract` (control) | `foo relies on an unsafe hierarchy.` |

`abstract` generates its side-effect constant with the *global* typing flags
rather than the declaration's local ones, so the taint never lands on the
constant that holds the proof.

**Contained, and the harness measures the containment:** `rocqchk` rejects the
`.vo`. That is the [`ModuleSystem/UniverseFlagDesync.v`](../../../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v)
shape — the *local* audit is lost, the independent checker is not.

One open question the file states rather than answers: `exists T:Set, Set = T` is
refutable, so `bar` is an inconsistent statement carrying a clean audit, one
Set-level Hurkens instance away from a closed `False` with a clean audit. Rocq's
`TypeNeqSmallType.paradox` is monomorphic at fixed universes and does not
instantiate to `Set`, so that step is not built here and nothing claims it.

## 3. rocq#22164 — cross-file `-impredicative-set` is invisible

[`impred/`](impred/). `prereq.v` is compiled **with** the flag; `consumer.v`
`Require`s it and is compiled twice, against the same `.vo`:

| Reading session | `Print Assumptions impred_def` and `uses_it` |
| --- | --- |
| predicative (no flag) | `Closed under the global context`, twice |
| impredicative (`-impredicative-set`) | `Theory: Set is impredicative`, twice |

**The audit's answer is a function of how the reader was invoked, not of the
artifact being audited.** The in-file `Fail` is the control and is not vacuous:
with the flag on, the definition it guards succeeds and `Fail` reports
`The command has not failed!`.

Upstream classifies this `kind: enhancement` + `part: printer` rather than
`kind: inconsistency`, and this repository adopts that classification: a missing
feature, not a soundness bug. Worth knowing anyway, because the fix (merged
2026-07-15) is **a flag that is off by default**, so even 9.3+rc1's default
`Print Assumptions` still has the blind spot.

## The shape all three share

It is the same shape as [`../../../KernelDefects/Coq/Checker/`](../../../KernelDefects/Coq/Checker/),
where `rocqchk` in one mode certifies a `False` that the same tool in its default
mode rejects. In every case the audit's verdict depends on something other than
the thing being audited — where the taint sits, which tactic produced the
constant, which flags the reader passed, which mode the checker ran in. A
verdict that varies with the asker is not a property of the artifact, and a CI
script that records the verdict has recorded the asker.

## Verified on

* The Rocq Prover 9.2 (OCaml 4.14.2) — the current stable release.
