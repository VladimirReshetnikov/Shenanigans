# Two kernel soundness defects, live on every released toolchain: the def-eq cache and the stuck sort

**Status: unsoundness, unreleased fixes.** Both were merged to `master` on
2026-08-17/18 and **no released toolchain carries either** — not `v4.33.0`
(2026-08-10), not `v4.34.0-rc1` (2026-08-10). `equiv_manager.cpp` is still
present on `releases/v4.33.0` and `releases/v4.34.0`, and `is_prop` on both
branches still reads `whnf(infer_type(e))`.

| | Defect | Fixed on `master` |
| --- | --- | --- |
| [lean4#14806](https://github.com/leanprover/lean4/pull/14806) | The kernel's `is_def_eq` cache was a union-find, so its answer depended on the order of earlier queries. Recursor construction asks the same question twice. | 2026-08-17 |
| [lean4#14807](https://github.com/leanprover/lean4/pull/14807) | `type_checker::is_prop` answered "not a proposition" for a term whose inferred type does not reduce to a sort, instead of rejecting it. `infer_proj` then skips its proof-irrelevance guard. | 2026-08-18 |
| [lean4#14808](https://github.com/leanprover/lean4/pull/14808) | Defence in depth: the kernel now type-checks the recursors it generates, and checks that each computation rule is type-preserving. | 2026-08-18 |

Both were **reported by Daniel Selsam (OpenAI) using their internal models**;
per #14806, "an OpenAI agent then produced two distinct exploits" from the first.
This is the same provenance as the July wave (#14607–#14616), and the second
time in three weeks that a model found a live kernel soundness hole.

Witnesses, all three axiom-free and all three accepted by every released
toolchain tested:

| Witness | Needs | Arena test |
| --- | --- | --- |
| [`KernelDefects/Lean/DefEq/EquivManagerMissingIH.lean`](../KernelDefects/Lean/DefEq/EquivManagerMissingIH.lean) | #14806 | `rec-missing-ih` |
| [`KernelDefects/Lean/DefEq/EquivManagerStuckSort.lean`](../KernelDefects/Lean/DefEq/EquivManagerStuckSort.lean) | #14806 **and** #14807 | `proj-of-stuck-prop` |
| [`KernelDefects/Lean/DefEq/SubstStuckSort.lean`](../KernelDefects/Lean/DefEq/SubstStuckSort.lean) | #14807 alone | `proj-of-subst-prop` |

Control: [`KernelDefects/Lean/Controls/DefEqCollisionControl.lean`](../KernelDefects/Lean/Controls/DefEqCollisionControl.lean).

    elan run leanprover/lean4:v4.33.0 lean --trust=0 KernelDefects/Lean/DefEq/EquivManagerMissingIH.lean
    pwsh KernelDefects/Lean/DefEq/verify.ps1

## The correction this report makes to this repository

[`2026-07-29-defeq-history-dependence.md`](2026-07-29-defeq-history-dependence.md)
documented `equiv_manager`'s union-find, the transitive closure it computes over
a non-transitive relation, and the 32-bit `Expr.hash` gate on its lookup. It
headed the finding **"Status: not unsoundness"**, on this argument:

> Every equivalence the kernel derives this way is semantically valid. […]
> Transitively closing a semantically valid relation stays valid, so the
> union-find is an amplifier, not a bug source.

The first sentence is true and the conclusion does not follow. Every *pair* the
union-find holds is a genuine definitional equality; what the closure changes is
the **verdict returned by `is_def_eq`**, and that verdict is read by code which
is not merely recording an equality but *making a structural decision* from it.
Recursor construction is exactly such a consumer: it calls `is_def_eq` to decide
which constructor fields are recursive, does so more than once while building one
recursor, and assumes it gets the same answer each time. Two calls, two different
answers, and the recursor's type and its computation rule disagree. Nothing
unsound was ever *stored* in the union-find. The unsoundness is in a client that
was promised a function of two arguments and given a function of the query
history.

That report's own section *"Why it is still worth fixing"* listed
**non-reproducible checking**, **divergence from external checkers**, and
**amplification** — item 3 said "if any single unsound acceptance is ever found,
the union-find spreads it transitively". The failure of imagination was in the
word *spreads*: no prior unsound acceptance was needed. The closure alone,
consulted by a client that asks twice, is sufficient.

The report's closing section, *"Not usable to derive `False` as-is"*, argued that
the bad equation `n ≡ n+1` has no closed endpoints to export, and searched for a
`False` **among the terms the cache relates**. #14806's exploits do not export
any equation. They let the cache change a decision *about a declaration*, and take
the `False` from the malformed declaration. The search was aimed one level below
where the defect was.

The witness in
[`DefEqHistoryDependence.lean`](../KernelDefects/Lean/DefEq/DefEqHistoryDependence.lean)
was correct and is unchanged; the measurement it makes still holds. Only its
classification was wrong, and its header now says so.

## Mechanism 1 — the def-eq cache (#14806)

The implemented `is_def_eq` is **sound but incomplete**: it never reports two
terms equal unless they are, but a fixed reduction strategy can get stuck on a
valid equality. An incomplete approximation of a transitive relation need not
itself be transitive, and Lean's is not. All three witnesses use the same triple:

```lean
def run (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => step x m) h

opaque seed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def a := run false 1 seed                                   -- stuck
def b := run false 1 (Acc.intro 1 fun _ => Acc.inv seed)
def c := run false 0 (Acc.inv seed (Nat.lt_succ_self 0))
```

`a ≡ b` by definitional proof irrelevance on the `Acc` argument; `b ≡ c` by iota;
`a ≢ c` asked on its own, because there the two `Acc` proofs have *different
types* (`Acc (·<·) 1` against `Acc (·<·) 0`), so proof irrelevance does not
apply and `a` never reduces.

`equiv_manager` merged every successful query and was consulted before any real
work — but only for terms with equal hashes:

```cpp
if (is_eqp(a, b))                      return true;
if (m_use_hash && hash(a) != hash(b))  return false;   // skips the union-find
...
node_ref r1 = find(to_node(a));
node_ref r2 = find(to_node(b));
if (r1 == r2) return true;
```

So whether `a ≡ c` is answered from the closure depends on the hash of the
surrounding term — which an adversary controls, because `Expr.hash` is computed
bottom-up and a collision propagates through any identical one-hole context. It
is the same 32-bit hash the 2026-07-29 report measured: the colliding pair in
`EquivManagerMissingIH.lean` is `h0 = h2 = 1470203867` at `_ind_fresh.3`, found
by search over constant names and pad salts. The
constant names and pad salts in the witnesses are chosen so the hashes collide
for the free variables the kernel creates while building a recursor's **minor
premises** (`_ind_fresh.3`, `_ind_fresh.9`) and *not* for the pass that builds
its **rules** (`_ind_fresh.14`).

A K-like reduction is then made to depend on that comparison. `Native64TwoHashGate`
is a K-like inductive predicate — one parameter, four `Bool` indices, one
field-less constructor pinning the indices — so reducing `Gate.rec … h` requires
the indices in `h`'s type to be definitionally equal to `Gate.intro`'s. The
recursive argument of `Native64TwoHashOwner.step` has such a `Gate.rec`
application as its type, so it reduces to `Owner` in one pass and not the other.

The result: `Native64TwoHashOwner.rec` has a `step` minor premise expecting four
arguments including the induction hypothesis, and a computation rule applying it
to three. The `ih` binder swallows the next argument. A `Prop`-valued recursor
application then reduces to `Bool`, and a `Prop` with two distinguishable
inhabitants gives `False` in four lines of ordinary surface Lean.

The fix replaces the union-find with a plain cache keyed on the query pair.
Kernel expressions contain no metavariables, so a query's result really is a
function of its two arguments; both positive and negative results can be cached
without exposing a closure. The elaborator already worked this way, so nothing
about what elaboration accepts changes.

**#14808 is the second half of the answer** and is worth reading separately. The
kernel generated recursors and installed them with `add_core`, which does not
re-check them: the surrounding machinery was trusted to be consistent. It now
type-checks each generated recursor and checks that each computation rule is
type-preserving — reducing the recursor applied to a constructor must yield a
term whose type is the recursor's declared result type. Its commit message makes
the sharp point: checking only that a rule's right-hand side *has some type* is
not enough, because an under-applied minor premise is still a well-typed function
term. This is the same shape as
[`Audits/Lean/Nested/IllTypedStoredConstructor.lean`](../Audits/Lean/Nested/IllTypedStoredConstructor.lean)
in this repository — a declaration the kernel stores without checking, on the
grounds that whoever produced it was trusted.

## Mechanism 2 — the stuck sort (#14807)

`type_checker::is_prop` is what keeps proof irrelevance sound in `infer_proj`:
if a projection could read data out of a proof, proof irrelevance would force
that data to be equal for all proofs of the proposition. On every release it
reads:

```cpp
bool type_checker::is_prop(expr const & e) {
    expr s = whnf(infer_type(e));
    return is_sort(s) && normalizes_to_zero(sort_level(s));
}
```

The `is_sort(s) &&` is the defect. When `infer_type(e)` is a **stuck** term that
does not reduce to a sort — an `Eq.rec` whose major premise is a free variable,
say — `whnf` returns the stuck term, `is_sort` is false, and `is_prop` returns
`false`. But `false` means *"not a proposition"*, and `infer_proj` reads it as
permission:

```cpp
bool is_prop_type = is_prop(type);
...
if (is_prop_type && !is_prop(binding_domain(r)))
    throw invalid_proj_exception(env(), m_lctx, e);
```

A value whose type does not reduce to a sort is **ill-formed**, and the right
answer is to reject it, not to answer a question about it. The fix computes the
inferred type with `ensure_sort`, which reduces it and requires a sort, raising
`(kernel) type expected` otherwise. On well-typed terms the type of a type is
always a genuine sort, so the stricter check never fires spuriously.

Note the comment already sitting above that function on every release, and what
it is about:

```cpp
// The level must be tested for zero up to normalization: `imax 1 0` denotes `Prop`
// without being syntactically `zero`. Comparing `s` against `Prop` syntactically
// instead would let `infer_proj` extract non-proof data out of a proof,
// contradicting proof irrelevance.
```

That is [#14613](https://github.com/leanprover/lean4/pull/14613) — the defect
this repository exhibits in
[`Universes/ImaxPropLaundering.lean`](../KernelDefects/Lean/Universes/ImaxPropLaundering.lean),
and *also* still live on every release. **This six-line function has now yielded
two distinct axiom-free `False`s in three weeks**, one for each of its two ways of
being wrong: comparing the sort spelling syntactically (#14613, fixed by making
the level test semantic) and treating a non-sort as a negative answer (#14807,
fixed by making the *reduction* mandatory). The surviving line is the one the
first fix already rewrote — and its comment, quoted above, states exactly the
consequence the second bug then produced anyway, by a route the comment does not
cover.

### The route that needs no cache

[`SubstStuckSort.lean`](../KernelDefects/Lean/DefEq/SubstStuckSort.lean) is the
sharpest of the three, because it needs nothing from `equiv_manager`. Every
comparison it makes comes out the same way in a fresh type-checker session:

* `P := a = b` and `Q := a = c` are definitionally equal **types**, because
  `b ≡ c`. Their proofs are not interchangeable for reduction.
* `gate h := Eq.rec (motive := fun _ _ => Type) Prop h` K-reduces to `Prop` for
  `h : P`, since K-like reduction only needs `h`'s type to be definitionally
  equal to `Eq.refl a`'s type `a = a`, i.e. `b ≡ a`. For the closed
  `witness : Q` it stays stuck, since that would need `c ≡ a`.
* `Owner : ∀ (h : P), gate h` is therefore accepted as a family of
  **propositions** — its recursor eliminates only into `Prop`. `Owner witness` is
  well-typed, since `Q ≡ P`; but its sort does not reduce.

So the sort of an inductive family is not re-examined after a substitution that
definitional equality permits, and `is_prop`'s wrong answer does the rest.
**#14806 alone does not close this**; only #14807 does.

## Version matrix

`lean --trust=0`, exit 0 with every `#guard_msgs` satisfied, meaning both that
the `False` was accepted and that `#print axioms` reported nothing.

| Toolchain | MissingIH | StuckSort | SubstStuckSort | control |
| --- | --- | --- | --- | --- |
| `v4.33.0` (current release) | accepted | accepted | accepted | rejected |
| `v4.34.0-rc1` | accepted | accepted | accepted | rejected |

**The matrix stops at `v4.33.0` for an uninteresting reason, and it is worth
stating rather than leaving as an apparent gap.** These witnesses drive the
kernel through `Environment.addDeclCore`, which gained a `maxRecDepth` parameter
in `v4.33.0`:

```
v4.32.2:  addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration) …
v4.33.0:  addDeclCore (env : Environment) (maxHeartbeats : USize) (maxRecDepth : USize) …
```

so the same file does not elaborate on `v4.31.0` or `v4.32.2` — it fails at
`OfNat Declaration 8000`, in the metaprogram, before the kernel is reached. That
is an API change, not a change in the defect.

The version-independent evidence is the arena's, because an `lean4export` NDJSON
test bypasses the frontend entirely: upstream reports all three accepted at
`v4.28.0`, `v4.29.1`, `v4.33.0` and `nightly-2026-08-01`, and records that the
official kernel **re-derives the malformed recursor when replaying the export
data** — so this is not a frontend-only artefact. `equiv_manager.cpp` has been
in `src/kernel/` since Lean 4's beginning; the `is_prop` weakness dates to
whenever `whnf` replaced a stricter reduction there.

The control is the load-bearing part. Changing one pad salt breaks the hash
collision and the kernel rejects the owner declaration outright, with the honest
error about an invalid occurrence of the datatype being declared; giving the
substituted proof type `P` instead of `Q` makes the sort reduce and the
projection is refused. Acceptance of the exhibits means something only because
the same procedure on the same toolchain rejects those twins.

## What the independent checkers say

From [arena.lean-lang.org](https://arena.lean-lang.org/), where all three landed
as tests on 2026-08-18 (`lean-kernel-arena` #141):

| Test | `official` (v4.33.0) | `nanoda` | `lean4lean` | `ind-models` |
| --- | --- | --- | --- | --- |
| `rec-missing-ih` | **accepts** | rejects | rejects | rejects |
| `proj-of-stuck-prop` | **accepts** | rejects | rejects | rejects |
| `proj-of-subst-prop` | **accepts** | **accepts** | rejects | rejects |

This is the cross-checking argument of *Who Watches the Provers?* doing exactly
what it is for, and it is worth being precise about which way each row cuts.

* For #14806, cross-checking **worked cleanly**: both exploits are caught by
  `nanoda`, and both by `lean-inductive-models`, Joachim Breitner's new checker,
  which was registered in the arena on 2026-08-16 — two days before the tests
  landed. Kernels that construct the recursor independently reject the export.
* For #14807, the third row is
  [`CATALOG.md`](../CATALOG.md) §3.0 happening **again**: `nanoda` accepted the
  bogus proof too, so the official kernel and the main external checker agreed
  and were both wrong. The postmortem's case had two *unrelated* bugs producing
  one agreement; here it is the same omission in both. `lean4lean` is unaffected
  for a reason worth recording — its `isProp` already used `ensureSortCore`, so
  it had the fix before there was a bug to fix.

That last point is the strongest available argument for the lean4lean project.
The bug is not one lean4lean *caught*; it is one lean4lean *never had*, because
writing the checker in a language where the obligation is stated forced the
stricter reading of a function that C++ let return a plausible `false`.

**The `nanoda` row is a snapshot, and it is already stale.** `nanoda` merged both
fixes the same day, in two PRs whose titles are a fair summary of the whole
episode: [`#26`](https://github.com/ammkrn/nanoda_lib/pull/26) *"add additional
checks for underived recursors"* (04:13 UTC, closing the `extra-rec` class), and
[`#27`](https://github.com/ammkrn/nanoda_lib/pull/27) *"is_sort guards, disable
union find eq"* (17:58 UTC) — which is #14807 and #14806 respectively, in one
commit, arrived at independently and in the same order. Its description of the
second change is the clearest one-line statement of #14806 anywhere: it replaces
the union-find with *"sorted pairs which do not try to exploit transitivity."*
So the correct reading of the table is not "`nanoda` is unsound" but "for about
fourteen hours on 2026-08-18 the two most-used Lean kernels shared a blind spot,
and only the official one still does."

## Reproduction notes

* `lean` resolves its toolchain from the current directory. Pin explicitly:
  `elan run leanprover/lean4:v4.33.0 lean --trust=0 <file>`.
* `set_option Elab.async false` is required. `Lean.addDecl` is asynchronous by
  default, so a `try`/`catch` around it silently reports kernel rejections as
  acceptances. The witnesses use `env.addDeclCore` and check the returned
  `Except` directly.
* Each witness takes a few minutes, most of it in `import Lean` and the
  well-founded `run_eq` proof; the kernel work is small.
* Judge by exit code and by `#print axioms`, never by grepping output for
  `error`.

## Public record, as of 2026-08-18

There is essentially none beyond the source. The two fixes are 24 hours old:
there is no postmortem for them, no Zulip thread, and nothing on X or Mathstodon
— the coverage of the July wave (de Moura's
[postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/),
Hacker News, Lobsters, GIGAZINE) is all about #14576 and stops there. The
complete public record of these two is: the two PR descriptions, the three
regression tests they added under `tests/elab/`, and the three arena tests. The
PR descriptions are unusually good and are the primary source for this report.

Worth noting for anyone tracking the July wave's conclusion: de Moura's
postmortem closed on the argument that a kernel bug is survivable because
independent implementations disagree, and the arena made that operational. Three
weeks later the same reporter found two more, one of which the main external
checker also missed. Nothing in the argument is refuted by that — cross-checking
is a *defence*, not a proof of absence — but the base rate it has to be judged
against is now higher than the July wave suggested.
