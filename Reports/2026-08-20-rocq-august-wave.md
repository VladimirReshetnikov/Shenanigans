# Three auditing efforts hit Rocq in seventy-two hours

**Status: a wave, not a bug report.** Between 2026-08-18 and 2026-08-20,
`rocq-prover/rocq` received **nine new `kind: inconsistency` issues** plus a
separate cluster of audit and checker defects, from **three independent
sources**. This report records the provenance, pins what reproduces on Rocq 9.2
— the current stable release — and says what the catalog should carry.

## The provenance, and a correction to the obvious reading

Carlo Angiuli's post of 2026-08-20 18:48 UTC, verbatim:

> Looks like OpenAI (Daniel Selsam?) found nine soundness "[deliberately constructed counterexamples]"
> in Rocq, which were reported privately and already have potential fixes in PRs.
> https://github.com/rocq-prover/rocq/issues h/t @constantine

Two things in that are worth separating, because the naive reading is wrong in a
way that matters.

**The attribution is Angiuli's inference and is marked as such** — "Daniel
Selsam?" carries a question mark. Nothing in the issues names OpenAI or Selsam.
What *is* checkable is the filing pattern, and it corroborates the "reported
privately" half exactly: the nine `kind: inconsistency` issues of 2026-08-20 were
filed not by an outside reporter but by **Rocq's own maintainers** — six by
`SkySkimmer` (Gaëtan Gilbert) and three by `yannl35133` (Yann Leray) — each with
a fix PR opened the same day. That is what a coordinated private disclosure looks
like when it lands publicly. It is not what an outside bug report looks like.

So: nine defects, found privately, landed as maintainer-filed issues with fixes
attached. Whether OpenAI found them is **unconfirmed** and this catalog should
say so until someone upstream states it.

**And it was not one effort but three, concurrently:**

| Filed | By | What |
| --- | --- | --- |
| 2026-08-18 | `JasonGross` | the `rocqchk` cluster — #22352 (a `False` the checker certifies), #22360, #22362, #22363, and on 08-19 #22373/#22374 |
| 2026-08-19 | `christos-spearbit` | #22364, #22365, #22366, #22367 — two of them axiom-free `False` with clean `Print Assumptions` |
| 2026-08-20 | `SkySkimmer`, `yannl35133` | the nine, privately reported, each with a same-day fix PR |

Three unrelated auditing efforts converging on the same kernel inside seventy-two
hours is the headline, and it is a stronger version of what
[`CATALOG.md`](../CATALOG.md) §6 already says about 2026: *the rate of discovery
changed, in both systems, for the same reason.*

**One sentence in §4 now needs revisiting.** It reads: *"Rocq 9.2.0 fixed ten
`kind: inconsistency` issues in a single release — an unprecedented count."*
Nine more arrived in one day. Whether that count is still unprecedented depends
on how many of the nine survive triage, but the sentence can no longer be left
standing unqualified.

## rocq#22366 — measured, reproduced, and now an artifact

The finding worth having from the 08-19 group, because it reproduces on the
current stable release and because it isolates further than the report does.

A functor applied while `Unset Guard Checking` is active substitutes an `Inline`
module parameter's body into the instantiated constant **without re-checking
guardedness and without recording the flag use**. Measured on Rocq 9.2:

| Channel | Verdict |
| --- | --- |
| `rocq c` on the exhibit | **exit 0** |
| `Print Assumptions boom` | **`Closed under the global context`** |
| `rocqchk` on the `.vo` | `Fatal Error: Type error: IllFormedRecBody` — caught |

Upstream reports it against Coq 8.18.0 and master and leaves the version field
blank; **9.2 is pinned here**.

**The isolation is this repository's contribution.** Upstream's report does not
narrow the trigger. Two controls do, and they run on the same toolchain in the
same harness:

| Arrangement | `Print Assumptions` |
| --- | --- |
| the flag used directly, no functor | `loopD is assumed to be guarded.` |
| the same functor **without** `Parameter Inline` | `X2.T is assumed to be guarded.` |
| the same functor **with** `Parameter Inline` | *silence* |

So the audit is working on both sides of it, and `Parameter Inline` — one token —
is the whole difference.

**Where it belongs, and why not `EscapeHatches/`.** The route to `False` needs
`Unset Guard Checking`, and ground rule 2 says a `False` behind a flag is an
escape hatch. That rule decides the *route*, and the route is not the finding:
[`EscapeHatches/Coq/TypingFlags.v`](../EscapeHatches/Coq/TypingFlags.v) §1
already exhibits it honestly, reporting `loop is assumed to be guarded.` The
finding is that the cost stops being reported — which is precisely why
[`UniverseFlagDesync.v`](../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v)
(rocq#22287) sits in `KernelDefects/` too. Both are the module system losing a
typing flag's bookkeeping; in both the casualty is the local audit and the
residual safeguard is `rocqchk`.

It is the **fourth** member of a family this catalog already tracks: §4.2's
#12155 and #16646 are the universe instances, §1.4's #20550 is the `abstract`
one, and this is guard. Upstream's own summary says as much — *"The known
`Print Assumptions` audit-bypass class was documented for universe checking. The
same one exists for guard checking."*

Artifact:
[`KernelDefects/Coq/ModuleSystem/GuardFlagThroughFunctor.v`](../KernelDefects/Coq/ModuleSystem/GuardFlagThroughFunctor.v)
with
[`GuardFlagThroughFunctorControls.v`](../KernelDefects/Coq/ModuleSystem/GuardFlagThroughFunctorControls.v).
`pwsh KernelDefects/Coq/verify.ps1` now runs 13 exhibits.

## rocq#22364 — not testable on this machine, and the reason is a containment fact

`kernel/nativecode.ml`'s `string_of_kn` joins module-path components with `_`
without escaping, so `A.B.x` and `A_B.x` both mangle to `A_B_x`; the second
shadows the first in the generated OCaml, and the kernel trusts the native
verdict via `NATIVEcast` with no re-check by kernel conversion. Upstream reports
an axiom-free `False` with `Print Assumptions` clean, on every native-enabled
build since commit `6b908b5185` (January 2013) through V9.2.0 and master, with
`rocqchk` rejecting the `.vo`.

**It does not reproduce here, and not because the bug is absent.** The installed
switch was configured without the native compiler:

```
Warning: native_compute disabled at configure time; falling back to vm_compute.
```

With the fallback in force the proof-of-concept computes *correctly* — `Eval
native_compute in (Nat.add A.B.x A_B.x)` gives `3`, and `via_native_neq` fails
with `Not a discriminable equality`. So the exhibit cannot be built on this
machine, and that is worth recording in both directions: it is an honest reason
for the gap, **and it is a containment fact**. A distribution built without the
native compiler is not exposed to this bug at all, and the fallback is to the VM
lane, which gets the answer right.

Coverage: **noted**, with the obstacle named so the next attempt does not
rediscover it. Building it needs a switch configured with
`--enable-native-compiler`.

## Scope of this report

The nine of 2026-08-20 are characterised separately; this document covers the
provenance, the two 08-19 `False` reports, and the catalog placement. What is
measured here was measured on:

* The Rocq Prover 9.2 (OCaml 4.14.2), `vo_version 90299`, native compiler
  **disabled** — the current stable release.

The version note matters for every row: `rocq#21839` and the rest of §4.1 are
recorded against a 9.2 whose native lane is unavailable, so any future exhibit in
the `native_compute` family will need a second switch.
