# Definitional equality is not transitive, and three things depended on it being so

> **Warning.** Three of the modules here contain a machine-checked, axiom-free
> proof of `False` that **every released Lean toolchain accepts**, including
> `v4.33.0` and `v4.34.0-rc1`. They are not `prelude` modules and have no fuse:
> importing one really does put `False` in scope. Do not.

Lean's `is_def_eq` implements a relation that *is* an equivalence — reflexive,
symmetric, transitive — but implements it **soundly and incompletely**. A fixed
reduction strategy can get stuck on a valid equality, so the implemented test is
not itself transitive. Every exhibit in this directory is built on one triple
where that is visible:

```lean
def run (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => step x m) h

opaque seed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def a := run false 1 seed                                   -- stuck
def b := run false 1 (Acc.intro 1 fun _ => Acc.inv seed)
def c := run false 0 (Acc.inv seed (Nat.lt_succ_self 0))
```

`a ≡ b` by definitional proof irrelevance, `b ≡ c` by iota, and `a ≢ c` asked on
its own — because there the two `Acc` proofs have different types, so proof
irrelevance does not apply and `a` never reduces.

> **Correction, 2026-08-18.** Everything below, and every upstream account of
> lean4#14806, presents an engineered `Expr.hash` collision as what makes the
> transitive closure reachable. That is wrong: `quick_is_def_eq` is declared
> `bool use_hash = false` (`type_checker.h:83`) and two of its three call sites
> take the default, so the closure is consulted for any pair. The order
> dependence reproduces with plain, unpadded terms whose hashes differ —
> measured in [`../../../Audits/Lean/DefEq/HashGateBypass.lean`](../../../Audits/Lean/DefEq/HashGateBypass.lean).
> The three exhibits here keep upstream's salts because they are ports of
> upstream's regression tests, not because the salts are load-bearing.

That much has been documented here since 2026-07-29, under the heading **"not
unsoundness"**. On 2026-08-17 and 08-18 upstream fixed two soundness bugs that
are exactly it, both reported by Daniel Selsam (OpenAI) using their internal
models. The correction, and what was wrong with the original argument, is
[`Reports/2026-08-18-defeq-cache-and-stuck-sort.md`](../../../Reports/2026-08-18-defeq-cache-and-stuck-sort.md).

## Contents

| File | What it is | Needs |
| --- | --- | --- |
| [`EquivManagerMissingIH.lean`](EquivManagerMissingIH.lean) | `theorem inconsistent : False`, `#print axioms` clean. The def-eq cache was a **union-find**, so it answered from the transitive closure — but only for hash-colliding terms. A constructed `Expr.hash` collision makes a K-like reduction fire while the recursor's *minor premises* are built and not while its *rules* are built, so `Owner.rec`'s `step` premise takes four arguments and its rule supplies three. A `Prop`-valued application then reduces to `Bool`. | [lean4#14806](https://github.com/leanprover/lean4/pull/14806) |
| [`EquivManagerStuckSort.lean`](EquivManagerStuckSort.lean) | The same cache, a different consequence: the order-dependent comparison decides an inductive family's **result sort**, so `Owner x h` is a `Prop` under `_kernel_fresh.0` and a stuck sort for the closed instantiation. `infer_proj` reads the stuck sort as "not a proposition" and hands out the hidden `Bool`. | #14806 **and** [#14807](https://github.com/leanprover/lean4/pull/14807) |
| [`SubstStuckSort.lean`](SubstStuckSort.lean) | **The sharpest one: no cache at all.** `P := a = b` and `Q := a = c` are definitionally equal *types* whose proofs behave differently under `Eq.rec`'s K-like reduction, so a family declared over `P` is a family of propositions while its instance at a proof of `Q` has a sort that does not reduce. Every comparison comes out the same way in a fresh type-checker session, so #14806 alone does not close it. | #14807 |
| [`DefEqHistoryDependence.lean`](DefEqHistoryDependence.lean) | The 2026-07-29 measurement of the union-find itself: the same non-transitivity, the engineered 32-bit hash collision, and the six-row table showing that acceptance depends on query order and on the collision. **Its header's "not unsoundness" claim is now marked as refuted.** No `False`; kept because the measurement is what the three above are built on. | — |
| [`LevelNormalizeIncomplete.lean`](LevelNormalizeIncomplete.lean) | [lean4#12747](https://github.com/leanprover/lean4/issues/12747), `Level.normalize` does not canonicalize an `imax` that collapses to a `max`. Incompleteness, not unsoundness — and unlike the row above, that classification still stands, because nothing downstream makes a structural decision from the answer. | — |
| [`../Controls/DefEqCollisionControl.lean`](../Controls/DefEqCollisionControl.lean) | Control for the three exhibits. One pad salt changed in each of the first two, breaking the hash collision; the third gives its substituted proof type `P` instead of `Q`. All three must be **rejected**, `#guard_msgs`-asserted. | — |

## Why this directory is worth reading as a unit

The three `False`s differ in what they need, and the difference is the point.

* #14806 is a **cache** bug: a component whose only job was to avoid repeated
  work changed the answer. It is invisible to any reading of the type theory,
  and it is why `DefEqHistoryDependence.lean` was filed under "not unsoundness"
  — nothing the cache stores is false.
* #14807 is an **error-handling** bug: `is_prop` returned `false` for a term it
  should have rejected, and `false` was read downstream as permission.
* `SubstStuckSort.lean` needs only the second. So the two fixes are independent,
  and shipping #14806 without #14807 would close two of these three.

#14807 is the **second** way `type_checker::is_prop` has been found wrong in
three weeks. The first is
[`../Universes/ImaxPropSpelling.lean`](../Universes/ImaxPropSpelling.lean)
([#14613](https://github.com/leanprover/lean4/pull/14613)), which compared the
sort *spelling* against `Prop` syntactically, and which is *also* live on every
release. Six lines of C++, one `False` each.

## Reproducing

```bash
pwsh KernelDefects/Lean/DefEq/verify.ps1
```

Expected final line: `All non-transitive-def-eq artifacts behaved as documented.`
It takes `-Toolchains` and `-SkipLeanChecker`.

`v4.33.0` is the floor, for an uninteresting reason:
`Environment.addDeclCore` gained a `maxRecDepth` parameter there, so on
`v4.31.0`/`v4.32.2` these files fail to *elaborate*, in the metaprogram, before
the kernel is reached. The version-independent evidence is upstream's — the
arena's export-based tests `rec-missing-ih`, `proj-of-stuck-prop` and
`proj-of-subst-prop` are accepted by the official kernel at `v4.28.0`, `v4.29.1`,
`v4.33.0` and `nightly-2026-08-01`, and it re-derives the malformed recursor when
replaying the export.

## Verified on

* Lean `4.33.0` — the current stable release (2026-08-10)
* Lean `4.34.0-rc1` (2026-08-10)

Controls rejected on both.
