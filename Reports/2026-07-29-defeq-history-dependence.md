# Kernel definitional equality is history-dependent, gated by a 32-bit `Expr.hash` collision

> ## Status corrected 2026-08-18: this **is** unsoundness
>
> This report was headed **"Status: not unsoundness"**. On 2026-08-17
> [lean4#14806](https://github.com/leanprover/lean4/pull/14806) fixed exactly the
> mechanism described below, as a soundness bug, with two axiom-free proofs of
> `False` attached. The reasoning that follows in this report is right about the
> cache and wrong about the consequence: nothing unsound is ever *stored* in the
> union-find, but the closure changes the **verdict** `is_def_eq` returns, and
> recursor construction reads that verdict to decide which constructor fields are
> recursive — asking more than once and assuming a stable answer. Two calls, two
> answers, and the recursor's type disagrees with its computation rule.
>
> The section *"Not usable to derive `False` as-is"* below searched for a `False`
> **among the terms the cache relates**, and correctly found none. The exploits
> export no equation at all; they let the cache change a decision *about a
> declaration* and take the `False` from the malformed declaration. The search
> was aimed one level below where the defect was.
>
> Everything else here — the mechanism, the hash gate, the witness, the six-row
> order table — is unchanged and is what those exploits are built on. See
> [`2026-08-18-defeq-cache-and-stuck-sort.md`](2026-08-18-defeq-cache-and-stuck-sort.md).

**Original status, retained for the record: not unsoundness.** Every equivalence
the kernel derives this way is semantically valid. The defect is that the
kernel's *accept/reject verdict* for a definitional-equality query depends on
which **unrelated** queries were performed earlier while checking the same
declaration, plus a 32-bit hash coincidence an adversary can engineer cheaply.

Reproduces identically on **v4.32.0 and v4.32.2** (the kernel patched for #14576),
so this is independent of the recent nested-inductive and `opaqueDecl` defects.

Witness: [`../KernelDefects/Lean/DefEq/DefEqHistoryDependence.lean`](../KernelDefects/Lean/DefEq/DefEqHistoryDependence.lean).
Run from a tree pinned to the toolchain under test:

    lean --trust=0 KernelDefects/Lean/DefEq/DefEqHistoryDependence.lean

## Mechanism

`equiv_manager` is a union-find over expressions. `type_checker::is_def_eq(t,s)`
calls `add_equiv(t,s)` on **every** success, including the recursive calls made by
`is_def_eq_args`, so the structure accumulates the transitive closure of every
definitional equality accepted so far in the current declaration check. But
definitional equality with proof irrelevance is **not** transitive (Carneiro,
*The Type Theory of Lean*), so the closure is strictly larger than the relation.

What normally hides this is the lookup guard in `is_equiv_core`:

    if (m_use_hash && hash(a) != hash(b)) return false;

Two expressions that are transitively merged but structurally different almost
always have different `Expr.hash`, so the union-find is never consulted for them.
Engineering a collision re-opens the lookup. Because `Expr.hash` is computed
bottom-up, a collision between `X` and `Z` propagates to any identical one-hole
context `C`: `hash(C[X]) == hash(C[Z])`.

Ruled out by direct test: `equiv_manager`'s `expr_map` is keyed by **structural
equality, not hash**, so colliding-but-distinct expressions do *not* collapse to a
single node. Only the lookup is hash-gated.

## Witness

A closed non-transitivity triple, `Classical.choice` the only axiom. `Acc Lt2 N2`
with an opaque accessibility proof `hs := Classical.choice ⟨Racc N2⟩`, and `cnt`
counting `Acc.intro` layers via `Acc.rec` at a `Nat` motive:

    A := cnt N2 hs            (stuck: Acc.rec on an opaque proof)
    B := cnt N2 (Racc N2)
    C := 2

    A =?= B   true    (definitional proof irrelevance on the Acc argument)
    B =?= C   true    (iota)
    A =?= C   false   (whnf A is a stuck Acc.rec)

Pad `A` and `C` into `A'`, `C'` sharing `hash = 1500901578` and `approxDepth = 6`
(`padE e n := (fun _ : Nat => e) n`; four collisions were found scanning 200k
constants). `Tag : Nat → Type | mk (n : Nat) : Tag n` forces the kernel's
`infer_let` to compare a let's ascribed index against its value's index, giving
ordered control over which comparisons run.

    isolated  A'=?=B   true
    isolated  B =?=C'  true
    isolated  A'=?=C'  FALSE          (fresh type_checker)

    one declaration = one type_checker = one equiv_manager
      A'=?=C' alone                      rejected
      A'=?=B ; A'=?=C'                   rejected
      B=?=C' ; A'=?=C'                   rejected
      A'=?=B ; B=?=C' ; A'=?=C'          ACCEPTED
      B=?=C' ; A'=?=B ; A'=?=C'          ACCEPTED   (order-independent)
      A'=?=B ; B=?=C' ; C'=?=A'          ACCEPTED   (symmetric)
      same three, no hash collision      rejected   (collision essential)     

    theorem (A' = C') by rfl, bare       rejected
    theorem (A' = C') by rfl, primed     ACCEPTED

The primed theorem states `cnt N2 hs = 2`, which is **true** — `Acc` is a
subsingleton, so `cnt` yields 2 for every proof. The kernel accepted a true
statement by a route it otherwise refuses. Transitively closing a semantically
valid relation stays valid, so the union-find is an amplifier, not a bug source.

## Why it is still worth fixing

1. **Non-reproducible checking.** Editing an unrelated part of a declaration can
   make a proof start or stop typechecking.
2. **Divergence from external checkers.** lean4checker, nanoda and lean4lean need
   not implement this cache, so a term Lean's kernel accepts can be rejected by
   independent verification — the exact guarantee those tools exist to provide.
3. **Amplification.** If any single unsound acceptance is ever found, the
   union-find spreads it transitively across the whole declaration.
   *(2026-08-18: the operative word turned out to be* spreads. *No prior unsound
   acceptance was needed — the closure alone, consulted by a client that asks
   the same question twice, is sufficient. This item was the closest this report
   came to the answer and it still understated the case.)*
4. The guard is a **32-bit** hash and collisions are cheap to search for.
   *(2026-08-18, TWICE corrected. First: confirmed by #14806's exploits, which
   engineer their own — the colliding pair in `EquivManagerMissingIH.lean`
   measures `h0 = h2 = 1470203867`. Then, later the same day, superseded
   outright: **it is not a guard at all** at two of `quick_is_def_eq`'s three
   call sites, which take the `use_hash = false` default declared at
   `type_checker.h:83`. The table row above reading "same three, no hash
   collision → rejected (collision essential)" is true of THAT witness's
   arrangement and false as a general claim — the closure is reachable with
   plain unpadded terms whose hashes differ. See
   [`2026-08-18-defeq-hash-gate-is-not-a-gate.md`](2026-08-18-defeq-hash-gate-is-not-a-gate.md).)*
   *(2026-08-18: confirmed by #14806's exploits, which engineer their own. The
   colliding pair in `EquivManagerMissingIH.lean` measures
   `h0 = h2 = 1470203867` at `_ind_fresh.3` — under 2^32, same width, found by
   search over constant names and pad salts exactly as here.)*

## Upstream movement, 2026-08-01

[lean4#14631](https://github.com/leanprover/lean4/pull/14631) (merged 2026-08-01)
edits `equiv_manager::is_equiv_core` — the same function whose hash guard is quoted
under **Mechanism** — together with `type_checker::is_def_eq_core`. Both compared
only a projection's index and its projected expression, ignoring `proj_sname`;
both now compare the name.

**It does not address anything in this report.** By inspection of the diff, the
union-find, the accumulation of the transitive closure on every `is_def_eq`
success, and the 32-bit `m_use_hash` lookup gate are all untouched. The witness
above uses `Acc.rec` and proof irrelevance, not projections, so nothing in it is
affected. Re-running it on a post-#14631 build is the outstanding check; this
paragraph is source inspection, not a re-measurement.

What is worth recording is that #14631 arrives at item 3 of the previous section
independently, and in the same words. Its stated rationale: *"after #14577 closed
the nested-inductive path that let unchecked projections into the environment
(#14576), these comparisons were the remaining places where a future injection bug
could have been amplified into a def-eq attack surface."* That is the amplifier
argument, made upstream, as the justification for a change with no exploit behind
it. [lean4#14632](https://github.com/leanprover/lean4/pull/14632) does the same for
`reduce_proj_core`, which now takes the structure name and refuses a constructor
belonging to any other inductive.

Item 2 of the previous section also has a concrete instance now, and it cuts the
other way. The #14576 postmortem records that the exploit passed both the official
kernel and a week-old `nanoda`, because `nanoda` had its own unverified
projection-node type name. Independent checkers diverging is the guarantee; the
case where they agreed for unrelated reasons is [`../CATALOG.md`](../CATALOG.md)
§3.0.

## Not usable to derive `False` as-is

**Superseded — see the box at the top.** This section is correct about what it
asked and wrong about what it concluded: no *closed endpoints* can be exported
from the bad equation, and none are needed.

The `Acc` + proof-irrelevance pair `F () (p h) ≡ succ (F () h)` and `p h ≡ h` is
jointly `n ≡ n+1`, but exists only between terms mentioning a hypothesis
`h : Acc r a` with `r a a`, which `acc_irrefl` refutes. The cache having no
context key raises the possibility of merging two *closed* terms through an
intermediate mentioning such a hypothesis — but no closed data term is
definitionally equal to a stuck `Acc.rec`, so the bad equation has no closed
endpoints to export.

## Reproduction notes

- `lean` takes its toolchain from the **current directory**; outside a tree with a
  `lean-toolchain` that is the elan default. Pin explicitly:
  `elan run leanprover/lean4:v4.32.2 lean --trust=0 <file>`.
- **`Lean.addDecl` is asynchronous** in 4.32.x (`Elab.async` defaults true): the
  kernel check runs on a background task and the exception never reaches a
  synchronous `try`/`catch`, which silently turns rejections into "accepted".
  Use `set_option Elab.async false`, or the synchronous oracles
  `(← getEnv).toKernelEnv.addDecl {}` and `Lean.Kernel.isDefEq`.
- Judge outcomes by exit code and `#print axioms`, never by grepping for `error`.
