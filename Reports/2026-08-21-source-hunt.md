# Source hunt for a novel `False`, 2026-08-21: no route found, four things found instead

A deliberate attempt to find a **new** way to prove `False` in Lean by reading
kernel source, run against `v4.33.1` on the day it was released. The headline
result is negative and is stated first, because the rest of this file is only
worth reading if that is clear.

**No novel route to `False` was found.** What the hunt produced is one bug
located and generalised, one behavioural confirmation that a fixed family is
really closed, one new trust-base entry, and two artifacts whose status changed
underneath the catalog.

## Where the hunt looked, and why

Two surfaces were picked deliberately over a broad sweep:

1. **`v4.33.1`'s brand-new kernel code.** Released 2026-08-21T12:02Z. New
   verification code is the least-audited code there is, and the repository's own
   best previous finding came from reading a *just-patched* check for the copies
   it missed. `check_recursors` and `check_uniform_ind_occs` did not exist in
   `v4.33.0`.
2. **The mechanism of [lean4#14875](https://github.com/leanprover/lean4/issues/14875)**,
   which had been proven live hours earlier. Generalising a demonstrated
   mechanism beats hunting a fresh one.

## 1. An asymmetry in the new `check_recursors`, examined and not exploitable

`v4.33.1` added, per [#14808](https://github.com/leanprover/lean4/pull/14808), a
**type-preservation** check on generated recursors: reduce `rec … (ctor …)` one
step and compare the reduct's type against the un-reduced application's. Its own
comment explains why the weaker check will not do — *"checking only that a
rule's right-hand side has some type is insufficient, because an under-applied
minor premise is still a well-typed (function) term."*

The nested-inductive path does not get that check. `check_recursors()` runs
inside `add_inductive_fn::operator()()` on the **auxiliary** declaration;
`restore_nested` then rewrites the recursor types and rule right-hand sides, and
the post-rewrite re-check (`environment::add_inductive`, the block #14621 added)
does only:

```cpp
tc.check(rec_info.get_type(), rec_info.get_lparams());
for (recursor_rule const & rule : rec_info.to_recursor_val().get_rules())
    tc.check(rule.get_rhs(), rec_info.get_lparams());     // "has SOME type"
```

So the exact weakness #14808 was written to close is, on the nested path, left to
the weaker check. **This was not turned into anything.** Reaching it needs
`restore_nested` to produce a rule that is well-typed but not type-preserving,
and the obvious lever — naming a `_nested` auxiliary — is closed: see §4 below.
Recorded because the asymmetry is real and someone with a better lever may want
it.

## 2. lean4#14875 located in kernel source, and a wider surface measured

Full detail in
[`KernelDefects/Lean/ModuleSystem/classrec/README.md`](../KernelDefects/Lean/ModuleSystem/classrec/README.md).
In brief: `mk_minor_premises` builds each induction hypothesis from the
**`whnf`-unfolded** type of the recursive field, and `mk_local_decl_for` takes
its binder type from that unfolded form — so the kernel writes a constant into
the recursor that no source mentions and no visibility check ever saw.

Measured consequence: the leak needs an **indirect** reference *and* a **class**.
Plain `inductive`, plain `structure`, and an `inductive` with a `| public`
constructor are all correctly refused; a directly written `(Hidden → Victim)` is
refused too. **A plain `class` is affected as well as `class inductive`**, which
the issue does not say.

The limit is also measured: every member of the family is caught by
`leanchecker`, structurally, because the route needs two declarations bearing one
global name in one environment and the producer's `.olean` records its
`import all` so the replay follows it.

## 3. `LEAN_NAT_MAX_SIZE`: an environment variable that changes kernel verdicts

`v4.33.1` bounds the numerals `reduce_nat` will compute, via `check_nat_size`,
configured by the **`LEAN_NAT_MAX_SIZE` environment variable** (default 128 MB).

Measured, same file and same toolchain, submitting
`Nat.pow 2 20000 % 7 = 4` through `addDeclCore`:

| | verdict |
| --- | --- |
| default | `KERNEL ACCEPTED` |
| `LEAN_NAT_MAX_SIZE=1024` | `KERNEL REJECTED — the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size` |

**This is not unsoundness, and the direction is what makes it safe.**
`check_nat_size` *throws* rather than returning "no reduction", so a tighter
limit only rejects more; nothing a small limit accepts is refused by a large one.
It fails closed.

What it is: the first kernel-affecting knob in §1.2's table that is not even a
`set_option` — it is in no source file, no recorded options, and no `.olean`.
"The same proof checks on my machine" becomes, in part, a claim about an
environment variable. Added to §1.2 beside `debug.skipKernelTC`, `trustLevel` and
the derived `quotInit`.

## 4. Two of this repository's own artifacts changed status under it

Both found by re-running rather than re-reading, and both now regression
witnesses.

* **[`Audits/Lean/DefEq/HashGateBypass.lean`](../Audits/Lean/DefEq/HashGateBypass.lean)** —
  exit 0 on `v4.33.0`, and on `v4.33.1` the primed exhibit *"did not reach the
  parameter check"*: it now dies at `inductive.cpp:426` with `application type
  mismatch`, exactly like its control. **The order dependence is gone**, measured
  behaviourally. `v4.33.1` removed `equiv_manager.cpp` outright and replaced it
  with plain positive/negative pair caches whose header comment names the reason:
  *"`is_def_eq` is … not transitive, so taking a transitive closure of successful
  pairs would make its result depend on evaluation order."* The #14806 family is
  closed, and this file is now the witness for that.
* **[`Audits/Lean/Nested/IllTypedStoredConstructor.lean`](../Audits/Lean/Nested/IllTypedStoredConstructor.lean)** —
  its README claims `v4.27.0-rc1` through `v4.33.0-rc1`. It is refused on **both**
  `v4.33.0` and `v4.33.1` with `(kernel) invalid declaration 'B.node', it uses
  the reserved prefix '_nested'`, so #14616's `check_no_nested_aux` closed it and
  the claim had already lapsed before this hunt started.

## What was ruled out

* The new `m_success`/`m_failure` def-eq caches are **not** a repeat of #14806:
  they are deliberately plain pair sets, and the order-dependence probe confirms
  it behaviourally.
* `check_uniform_ind_occs` handles the over-applied case by descending, and the
  partial application is revisited as a subterm, so the `args.size() > nparams`
  early return is not a hole. Its own comment shows the nested case — where a
  nested occurrence's parametric arguments are dropped from the auxiliary — was
  considered, which is why it runs on the original declaration first.
* `is_rec_argument` opens with `whnf`, but reduction cannot *create* an
  occurrence of a datatype being declared, since those are not yet in the
  environment. The erasure direction is sound: an erased field carries no data.
* Escaping `leanchecker` with the #14875 mechanism — see §2.

## Honest summary

The two richest-looking leads both terminated in a check that already exists: the
nested type-preservation gap has no lever to reach it, and the #14875 family
cannot get past the replay. The value of the day is a sharper account of a live
bug, a wider surface for it than upstream has recorded, one new trust-base entry,
and two status corrections the catalog would otherwise still be wrong about.
