# `Print Assumptions` reports a property of the asker, not of the artifact

**Status: three audit holes, all live on Rocq 9.2 — the current stable release —
all measured here.** No new proof of `False`. The finding is that Rocq's own
audit command answers `Closed under the global context` about constants whose
honest answer names an axiom or a kernel check that was switched off, and that
this repository's [`CATALOG.md`](../CATALOG.md) §1.4 was too generous about it.

| Issue | What is dropped | State |
| --- | --- | --- |
| [rocq#21825](https://github.com/rocq-prover/rocq/pull/21825) | Anything reachable only through a definition's **type** — axioms *and* `bypass_check` flags | Merged 2026-03-26 from a branch point past `V9.2.0`. **Live on every released Coq/Rocq**; carried only by the 9.3+rc1 prerelease |
| [rocq#20550](https://github.com/rocq-prover/rocq/issues/20550) | The declaration's typing flags, when the proof went through `abstract` | `kind: inconsistency`, closed 2026-04-24, fix on `master`/`v9.3` only. **Live on 9.2.0** |
| [rocq#22164](https://github.com/rocq-prover/rocq/issues/22164) | Cross-file `-impredicative-set` | Fixed 2026-07-15 **behind a flag that is off by default**, so 9.3+rc1's default still has it |

Artifact: [`Audits/Coq/PrintAssumptions/`](../Audits/Coq/PrintAssumptions/), each
finding paired with a control the same procedure on the same toolchain reports
correctly. `pwsh Audits/Coq/PrintAssumptions/verify.ps1` — thirteen assertions.

## The correction this forces

§1.4's row read:

> `Print Assumptions` is unreliable — *Mostly false, and better than its
> reputation: it reports every `bypass_check` flag by name.*

The first clause survives. The second is false, and the cleanest demonstration is
a pair of files differing in one thing:

```coq
(* both files: Unset Guard Checking. Fixpoint loop (n : nat) : False := loop n. *)

Definition tyG := (fun _ : False => nat) (loop 0).
Definition viaType : tyG := 0.
Print Assumptions viaType.     (* -> Closed under the global context *)

Definition viaBody : nat := match loop 0 return nat with end.
Print Assumptions viaBody.     (* -> Axioms: loop is assumed to be guarded. *)
```

Same flag, same fixpoint, same file pair. Reported when the taint sits in a body,
silent when it sits in a type.

Two precision points, because the severity is easy to overstate. The gap is
constants that **have a body** — bodiless ones were always traversed, which is
how `Axiom ax : nat` was ever reported. And the concealed occurrences in these
witnesses are convertibility-erasable, so no *essential* dependency is being
hidden. It is an audit hole, not a route to `False`, and the artifact says so.

## `abstract`, and a statement that is false with a clean audit

```coq
Ltac the_tac := unshelve eexists;[exact_no_check Set | reflexivity].
Unset Universe Checking.
#[bypass_check(universes=no)] Lemma bar : exists T:Set, Set = T.
Proof. abstract the_tac. Qed.
Set Universe Checking.
Print Assumptions bar.          (* -> Closed under the global context *)
```

The control is the same lemma proved by the same tactic without `abstract`, and
it reports `foo relies on an unsafe hierarchy.` correctly. `abstract` builds its
side-effect constant with the *global* typing flags rather than the
declaration's, so the taint never reaches the constant that holds the proof.
Restoring `Set Universe Checking` afterwards does not change the answer.

**Contained, and the harness measures it:** `rocqchk` rejects the `.vo`. That is
the [`UniverseFlagDesync.v`](../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v)
shape — the *local* audit is lost, the independent checker is not.

Worth stating and worth not overclaiming: `exists T:Set, Set = T` is refutable,
so `bar` is an inconsistent statement with a clean audit — one Set-level Hurkens
instance away from a closed `False` with a clean audit. Rocq's
`TypeNeqSmallType.paradox` is monomorphic at fixed universes and does not
instantiate to `Set`, so that step was not built and nothing here claims it.

## The audit answers a question about the reader

The third finding is the one that generalises. `prereq.v` is compiled with
`-impredicative-set`; `consumer.v` `Require`s it and is compiled twice against
the *same* `.vo`:

| Reading session | `Print Assumptions` |
| --- | --- |
| predicative | `Closed under the global context` |
| `-impredicative-set` | `Theory: Set is impredicative` |

Nothing about the artifact changed between those two rows.

Upstream files this `kind: enhancement` + `part: printer`, not
`kind: inconsistency`, and this repository adopts that classification — it is a
missing feature rather than a soundness bug, and unlike #12155/#16646 it is not
in `dev/doc/critical-bugs.md`. It earns its place because of the shape, which is
the same shape as [`KernelDefects/Coq/Checker/`](../KernelDefects/Coq/Checker/)
and its companion measurement: **the verdict depends on the asker.** Where the
taint sits; which tactic produced the constant; which flags the reader passed;
which mode the checker ran in. A verdict that varies with the asker is not a
property of the artifact, and a CI script that records the verdict has recorded
the asker.

One narrowing the verification pass insisted on, and it is right: of the four
"theory assumptions", only impredicative `Set` is actually silent. Rewrite rules
name their `Symbol`; type-in-type's per-definition entry is environment-
independent and only its banner is gated, which §1.2's `TypingFlags.v` row
already states correctly; and *indices not mattering does not exist in 9.2.0*.
The indices case also runs the opposite way — suppressed when the reader's
environment already makes the assumption, which is conservative. Only #22164 is
suppressed when the reader's environment does **not**.

## A version correction that strengthens an existing claim

The same sweep turned up that **there is no `V9.2.1`**, and never will be. The
tag list runs `V9.2.0` (2026-03-27), `V9.3+alpha`, `V9.3+rc1` (2026-07-22),
`V9.4+alpha`; the `v9.2` branch is one commit ahead of `V9.2.0` and that commit
is `eae147572 "Unset is_a_released_version"`. Upstream's own ledger has said
`fixed in: V9.3` since 2026-03-31 — only the GitHub milestone ever said 9.2.1.

[`CATALOG.md`](../CATALOG.md) §4.1 recorded rocq#21839 as *"fixed in 9.2.1 / 9.3"*
and its artifact as live on 9.2.0 "because the installed toolchain is 9.2.**0**".
The corrected statement is stronger: **#21839 is live on every released stable
Rocq since 8.16 (bar 8.18), including the latest.** The same correction applies
to #22021 and to the #21970 cell.

## What was ruled out

The sweep behind this report covered six angles — the tracker exhaustively since
2026-06-01, upstream's `critical-bugs.md`, the 2026-08-18 checker cluster,
releases and changelogs, community channels, and the catalog's own open gaps.
Its headline is a negative: **no new route to `False` reachable from ordinary
Rocq source on any released toolchain.** One genuinely new closed axiom-free
`False` exists — [rocq#22125](https://github.com/rocq-prover/rocq/issues/22125),
a de Bruijn misalignment introduced by a commit titled *"Reorder and cleanup"* —
and **no tagged build of any kind ever carried it**; it lived on `master` for
eleven weeks. §4.1 records it with a version-boundary control measured on 9.2.0
rather than an artifact.

Two standing blind spots the next survey should know about:

* **Rocq Zulip is not publicly readable.** `rocq-prover.zulipchat.com` returns
  `UNAUTHORIZED` anonymously on every API route tried; the GitLab archive mirror
  ends at 2024-10-12. No 2026 Zulip content is reachable by any route found, and
  Zulip is demonstrably where Rocq soundness discussion happens.
* **Two 2026 events are unpublished**: Rocq'n'Share (EPFL, June–July) included a
  Yann Leray lightning talk *"Everything you never wanted to know about the guard
  condition"* with no slides or notes anywhere, and Rocqshop (Lisbon, 2026-07-25)
  produced an abstract whose "few bugs" sentence names none of them.

Outside those, the community sweep was empty: Tristan Stérin's *In search of
falsehood* has no follow-up and no second round, and nobody has run a
Selsam-style AI audit against Rocq the way one was run against Lean in July and
August 2026.
