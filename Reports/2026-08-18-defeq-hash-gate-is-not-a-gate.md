# The `Expr.hash` collision was never the gate

**Status: a reachability correction, not a new defect.** lean4#14806's
order-dependent `is_def_eq` needs **no engineered `Expr.hash` collision**.
Measured on Lean v4.33.0 with plain, unpadded terms.

This corrects a claim that is stated as fact in four places, one of which is a
report written in this repository earlier the same day:

| Source | What it says |
| --- | --- |
| lean4#14806's PR body | describes the union-find as consulted per hash |
| the arena's `rec-missing-ih`, `proj-of-stuck-prop`, `proj-of-subst-prop` | each quotes `if (m_use_hash && hash(a) != hash(b)) return false; // skips the union-find` and builds its exploit around an engineered collision |
| [`2026-07-29-defeq-history-dependence.md`](2026-07-29-defeq-history-dependence.md) | *"same three, no hash collision → rejected (**collision essential**)"* — a measured row in its own table |
| [`2026-08-18-defeq-cache-and-stuck-sort.md`](2026-08-18-defeq-cache-and-stuck-sort.md) | *"The union-find lookup is gated on `hash(a) == hash(b)`"* |

Artifact: [`Audits/Lean/DefEq/HashGateBypass.lean`](../Audits/Lean/DefEq/HashGateBypass.lean).
Exit 0 under `lean --trust=0` on v4.33.0, with both measurements
`#guard_msgs`-asserted.

## The source facts

```
kernel/type_checker.h:83
  lbool quick_is_def_eq(expr const & t, expr const & s, bool use_hash = false);

kernel/type_checker.cpp:1090   quick_is_def_eq(t, s, use_hash);   // use_hash = true
kernel/type_checker.cpp:1114   quick_is_def_eq(t_n, s_n);         // DEFAULT: false
kernel/type_checker.cpp:965    quick_is_def_eq(t_n, s_n);         // DEFAULT: false
```

`equiv_manager::is_equiv(e1, e2, use_hash = false)` assigns `m_use_hash` from its
third argument, and `is_equiv_core`'s early return reads
`if (m_use_hash && hash(a) != hash(b))`. So at two of the three call sites the
hash comparison is **not performed at all** and the union-find is consulted for
any pair whatsoever. Only :1090 — the site everyone quotes — passes `true`.

:1114 is reached whenever `whnf_core` changed either side; :965 comes from
`lazy_delta_reduction_step`, i.e. after both sides have been unfolded. Between
them they cover the ordinary case.

## The measurement

Take lean4#14806's own triple and lift it from `Bool` to closed *types* with
`def Vec : Bool → Type := fun b => cond b Nat Bool`:

```
A := Vec (rcA false)     B := Vec (rcB false)     C := Vec (rcC false)
```

No padding, no salt, no search. Then, on v4.33.0:

| | Result |
| --- | --- |
| `hash A` vs `hash C` | **differ** (asserted, so the file measures nothing if they ever collide) |
| isolated `A ≡ B` | true |
| isolated `B ≡ C` | true |
| isolated `A ≡ C` | **false** |
| `A~B`, then `B~C`, then `A` ascribed at `C`, in **one** `Kernel.check` | **ACCEPTED** |
| the third ascription alone, in its own `Kernel.check` | rejected |
| the same chain padded with deliberately **non-colliding** salts | **ACCEPTED** |

The last row is the one that kills the received account: upstream's exploits pad
their terms, the padding is described everywhere as the collision-engineering
step, and padding with salts chosen so the hashes *differ* changes nothing.

**Scope.** What is measured is the behaviour plus the two source facts. Which of
the two ungated sites fires for a given query is not measured — that needs an
instrumented build — and the behavioural claim does not depend on knowing.

**The bound, also measured.** `equiv_manager` lives in the type_checker state
and a separate `addDecl` gets a fresh one, so priming in one declaration does
**not** carry into the next: the same third ascription, submitted as its own
declaration against the environment the priming declaration produced, is
correctly rejected. The order dependence is confined to a single declaration
check. That is what #14806's analysis says, and the artifact asserts it rather
than assuming it — if a future toolchain ever let the closure persist across
declarations, that assertion is what would catch it.

## Why it matters

The bar for lean4#14806 drops from *"engineer a 32-bit collision, then place the
comparisons where the kernel's fresh variables make it hold"* to *"write three
ordinary definitional-equality comparisons inside one declaration"*. The
upstream exploits' constants are named `Native64TwoHashA` and their salts were
found by a birthday search over 200k candidates; none of that apparatus is
required for the mechanism.

**One thing this does not claim.** Upstream's exploits use the collision for a
second purpose beyond reaching the closure: *selectivity*. `rec-missing-ih`
needs a K-like reduction to fire while the recursor's minor premises are built
and **not** while its rules are, and the collision is what makes the closure
visible in one pass and invisible in the other. Removing the hash gate makes the
closure reachable everywhere, which is the opposite of selective — so this
finding lowers the bar for the *order-dependence*, not automatically for
*those particular exploits*. Rebuilding them without a collision needs some other
source of asymmetry between the two passes, and none is offered here.

That is worth having on the record for three reasons. It makes the bug easier to
trip over **by accident** in ordinary code, which changes how one reads
"non-reproducible checking" in the 2026-07-29 report. It means a regression test
built around a specific collision is testing a narrower thing than its
description claims. And it removes the main reason to think lean4#14616 —
whose exploit "depends on transient `equiv_manager` state" and which this catalog
still lists as its largest Lean-side gap — is hard to reconstruct.

## How close this gets to a `False`, and why it stops

`check_constructors` type-checks the whole constructor type
(`tc().check(t, m_lparams)`, inductive.cpp:426) and then walks its telescope,
comparing each of the first `nparams` binder types against the inductive's
parameters (inductive.cpp:430) — and, whatever that comparison says, substitutes
the inductive's parameter fvar into the body. `declare_constructors` then stores
the **original, unsubstituted** type. So an accepted-but-wrong parameter check
would leave a stored constructor a fresh kernel must reject.

With the priming lets placed in the constructor's later binder types, that is
half-reached, and the halves are worth stating separately:

* the **control** — parameter declared at `C`, inductive at `A`, no priming —
  dies at **:426**, `application type mismatch`;
* the **primed exhibit** dies at **:430**, `arg #1 of 'PE.mk' does not match
  inductive datatypes parameters'`.

The exhibit got *further*. The kernel type-checked a constructor whose result
applies `PE : Vec (rcA false) → Type` to a `p : Vec (rcC false)` — a term a fresh
kernel rejects — and what stopped the declaration was the second, redundant
comparison at :430, which asks the same question again outside the primed
context and gets the honest answer.

Both directions of that are worth recording. The kernel does type-check a
constructor type it should refuse; and the parameter check, which reads like a
well-formedness formality, is **load-bearing as a backstop** against the def-eq
order dependence. It is not obvious that every consumer of a defeq verdict in
`inductive.cpp` has such a backstop — that is the next thing to look at, and it
is the reason this stops at an anomaly rather than a `False`.

## Reproduction notes

* `elan run leanprover/lean4:v4.33.0 lean --trust=0 Audits/Lean/DefEq/HashGateBypass.lean`
* The file asserts its own preconditions: it fails loudly if the unpadded pair
  ever collides, if the triple stops being non-transitive, or if the bare
  ascription starts being accepted. A future toolchain that fixes #14806 will
  make it fail at the primed chain, which is the intended regression signal.
* `Elab.async` is disabled and every verdict comes from `Kernel.check` /
  `Kernel.isDefEq` directly, not from `addDecl`.
