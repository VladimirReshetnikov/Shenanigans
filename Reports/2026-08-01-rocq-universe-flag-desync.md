# Rocq 9.2: universe checking stays off after the module that turned it off closes

**Date:** 2026-08-01
**Toolchain:** The Rocq Prover 9.2 (`coqc`, `coqchk` both 9.2).
**Artifacts:** [`KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v`](../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v)
and its companion [`UniverseFlagDesyncImport.v`](../KernelDefects/Coq/ModuleSystem/UniverseFlagDesyncImport.v).
**Upstream:** [rocq-prover/rocq#22287](https://github.com/rocq-prover/rocq/issues/22287),
reported 2026-07-16, **OPEN**.

---

## Claim

```coq
From Stdlib Require Import Hurkens.

Module M.
  Local Unset Universe Checking.
  Definition inside : Type := Type.
End M.

Definition Small2 : Type := Type.
Definition desync_false : False := TypeNeqSmallType.paradox Small2 eq_refl.
Print Assumptions desync_false.
```

`coqc` accepts this, exit 0, and prints

```
Closed under the global context
```

The flag is `Local` to `M`, and `M` is closed before the paradox is stated. No
flag is in scope on the line that proves `False`.

This is #22287: `ugraph` keeps a *copy* of the universe-checking flag, so closing
the module restores the syntactic setting without restoring the graph's. CATALOG
§4.2 and §4.6 record it as a **gap** with no artifact, and give the affected
version as `master`. **Rocq 9.2 is affected too**, which is what this report
adds.

It is also this repository's first *live* Coq exhibit. The other three in
[`KernelDefects/Coq/`](../KernelDefects/Coq/) are fixed upstream and are kept as
regression witnesses that must be **rejected**; this one is open, so acceptance
is the finding, and [`verify.ps1`](../KernelDefects/Coq/verify.ps1) now
distinguishes the two.

---

## Controls

The same declaration is refused twice in the same file before the module appears.

| | |
| --- | --- |
| `Fail Definition control_false : False := TypeNeqSmallType.paradox Small0 eq_refl.` | passes — i.e. the paradox **is** refused with the flag genuinely on |
| the same after a `Module Plain` that does **not** touch the flag | still refused |
| the same after `Module M` with `Local Unset Universe Checking` | **accepted** |

So the closed module is the whole difference, and it is not merely "a module was
opened".

---

## What catches it, and what does not

| Check | Verdict |
| --- | --- |
| `coqc UniverseFlagDesync.v` | exit 0 — **not caught** |
| `Print Assumptions desync_false` | `Closed under the global context` — **not caught** |
| `Print Assumptions one_eq_two` (a `1 = 2` derived from it) | `Closed under the global context` — **not caught** |
| `coqchk UniverseFlagDesync` | `Fatal Error: Error: Universe inconsistency.` (exit 129) |
| `Require Import UniverseFlagDesync.` from any other file | **rejected at the `Require` line** |

The `Require` verdict is the one that decides how bad this is, and it is worth
quoting in full:

```
Error: Universe inconsistency. Cannot enforce
Hurkens.TypeNeqSmallType.Paradox.u0 = UniverseFlagDesync.32 because
UniverseFlagDesync.32 < UniverseFlagDesync.31
<= Hurkens.TypeNeqSmallType.Paradox.u0.
```

The inconsistency really is written into the `.vo`'s universe graph. Both the
independent checker and any consumer re-check it and refuse. **The `False` is
confined to the file that produced it.**

---

## So what is actually lost

The *local* audit. Inside that file the signature is exactly the one a correct
development produces, and `1 = 2` carries it too. A CI that compiles the file and
greps `Print Assumptions` for a cost passes.

The contrast that makes this precise is in this repository already.
[`EscapeHatches/Coq/TypingFlags.v`](../EscapeHatches/Coq/TypingFlags.v) §3
obtains the *same* Hurkens paradox honestly, with the flag in scope, and
`Print Assumptions` says

```
universe_false relies on an unsafe hierarchy.
```

That file also records the near-miss already: restoring `Set Universe Checking`
afterwards keeps the per-constant line but suppresses the `Theory: Type hierarchy
is collapsed` banner, so *"auditing by grepping for the banner alone therefore
misses a file that switches the flag off and back on again."* #22287 is the same
observation one step further on — here even the per-constant line is gone,
because as far as `Print Assumptions` can tell no flag was ever used.

The second contrast is with this repository's Lean exhibit of the same *shape*.
[`KernelDefects/Lean/ModuleSystem/`](../KernelDefects/Lean/ModuleSystem/) is also
a module boundary that drops a soundness-relevant property, also with a clean
`#print axioms` — but there the `False` **does** escape into ordinary downstream
code, and `Audit.lean` proves `(2 : Nat) = 3` in a plain non-module file. Rocq
records enough in the `.vo` to stop that; Lean's stub does not. Two systems, one
mechanism, opposite containment.

---

## Scope and honesty

* **Not a new defect.** #22287 is upstream's, open since 2026-07-16. What is new
  is the artifact — CATALOG marked it a gap — the measurement that 9.2 is
  affected rather than only `master`, and the containment result, which the issue
  does not state.
* **Contained.** This cannot misstate a library. Anyone who `Require`s the file
  gets an error, and `coqchk` refuses the `.vo`. The exposure is to whoever reads
  `Print Assumptions` in the file itself and believes it.
* **Reachable from ordinary source.** Unlike every Lean route in this catalog, no
  metaprogramming is involved: nine lines of plain Coq, one of them a flag inside
  a module.
* **CATALOG §5 listed #22287 and #22024 as the two highest-priority Rocq gaps.**
  This closes the first. #22024 (guard rtree mutation, relative inconsistency
  with univalence) is still a gap.
