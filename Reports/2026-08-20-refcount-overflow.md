# A reference counter is part of the trusted computing base

**2026-08-20.** [lean4#14838](https://github.com/leanprover/lean4/pull/14838),
*"fix: freeze objects when their reference count overflows"*, merged the same day
under a label Lean did not have many of: `runtime-soundness`. From the PR body:

> "This PR prevents memory corruption when an object's 32-bit reference count
> overflows. On machines with at least 18GB of free RAM, it could be used to
> trigger use-after-free in the official kernel, which could be extended into a
> proof of False. Other kernels such as nanoda not based on the Lean runtime were
> not affected. […] The issue was reported by Daniel Selsam (OpenAI) using their
> internal models."

This catalog has ninety-odd entries about kernels being wrong. This is the first
about a kernel being *right* and the machine underneath it losing the object it
was reasoning about.

## Why it is a new category

§2 already had five buckets and this fits none of them, which is why it got
[§2.7](../CATALOG.md).

* Not **§2.1–2.3** (kernel logic): the kernel's logic is correct here. Its
  refusal of the ill-typed declaration is the *right* refusal, and it is exactly
  what a corrupted object takes away.
* Not **§2.4** (`native_decide` / compiler trust base): every entry there needs
  the compiler, and `lean4checker` never accepted those proofs because it has no
  compiled-code support. This one goes through `addDeclCore` on the ordinary
  checked path — no `native_decide`, no flag, no escape hatch, and
  `#print axioms` reports nothing.
* Not **§2.5** (precautionary strengthening): there is a reproducer.

The sharpest way to put it: **§2.4 exists to deny the equivalence between "the
compiler said so" and "the kernel said so". Filing #14838 there would assert that
equivalence.**

## The construction

Three honest pieces and one fraudulent step:

```
AllSubsingleton.{u} := ∀ (α : Sort u) (x y : α), x = y
opaque Enc.{u} : { p : Prop // p = AllSubsingleton.{u} }

HONEST   encZero     : Enc.{0}.val            -- Sort 0 = Prop; proof irrelevance
HONEST   encOneFalse : Enc.{1}.val → False    -- Bool : Sort 1 has true ≠ false
FRAUD    Candidate.{u} : Enc.{u}.val := encZero
```

`AllSubsingleton` is true at universe 0 and false at universe 1, so a proof of
the `u := 0` instance passed off as a proof of the schematic `u` gives `False` at
`Candidate.{1}`. Everything except that one generalisation is ordinary Lean.

## Where the counter overflows, and the factor of two

Read from `src/kernel/level.cpp` at the fix commit `8df768b731`; not instrumented.

The declared type is built over a `Level.max` DAG nested `depth` deep over one
shared leaf. Comparing levels runs `is_def_eq(level, level)` → `is_equivalent` →
`normalize`, whose `Max` arm flattens the DAG with `push_max_args` — which has
**no memo table**. So the sharing is destroyed and the expansion is *materialised*
rather than traversed. Each slot is a `buffer<level>` `push_back`, an `object_ref`
copy construction, one increment of the leaf's count.

The peak is **2^(depth+1)**, not 2^depth, and the source shows why:
`push_max_args(r, todo)` fills `todo` with 2^depth copies; the next loop fills
`args` with another 2^depth *while `todo` is still live*; `todo` is only reused
afterwards (`buffer<level> & rargs = todo; rargs.clear();`).

That factor of two is load-bearing arithmetic, not pedantry: **2^30 = 1,073,741,824
is less than `INT_MAX` = 2,147,483,647.** A write-up claiming 2^30 occurrences
overflow a signed 32-bit counter is claiming something false. 2^31 = `INT_MAX` + 1,
so `depth = 30` is exactly the smallest depth that overflows. This report's first
draft had it wrong, and an adversarial check caught it.

**Upstream disagrees with itself about the RAM.** The PR body says "at least
18GB"; the reproducer's own docstring says "~12GB". Both are recorded; neither is
measured here.

## What was measured, and one thing it overturned

Artifact: [`Audits/Lean/Runtime/RefCountOverflow.lean`](../Audits/Lean/Runtime/RefCountOverflow.lean),
`#guard_msgs`-asserted, green on `v4.33.0` and `v4.34.0-rc1`.

The `False` is **not** reproduced — that needs 12–18GB and the reproducer's
commented-out `depth := 30`. What is measured is where the fraud is:

| | Result |
| --- | --- |
| the honest scaffold (`encZero`, `encOneFalse`) | elaborates and typechecks |
| `Candidate.{u}`, depths 0/1/3/8/16 | **REJECTED**, `(kernel) declaration type mismatch` |
| the same with a **transparent** `def` instead of `opaque` | **REJECTED**, identically |
| `imax (maxDag u 8) 0` — mentions `u`, same size, normal form `0` | **ACCEPTED** |

The last two rows are the useful ones, and both correct the natural reading.

**Opacity is not what does the work.** The obvious story is "`Enc` is `opaque`, so
`Enc.{0}.val` and `Enc.{u}.val` cannot be unfolded into agreement." Opacity does
block delta-reduction — that is source-true. But the transparent twin is refused
just the same, so it is not what produces the observed refusal.

**The discriminator is the normal form of the level.** Not opacity, not the DAG's
size, and not whether `u` occurs: a level that mentions `u`, over a DAG just as
large, is accepted as soon as its normal form is `0`. That is the sharpest
statement of what the kernel is actually keying on, and it is a better control
than the one this file started with.

## What is upstream's account and not ours

Stated plainly because the catalog's ground rules require it:

* **Measured here**: the scaffold, the rejections, the two controls above, the
  release status, the `src/kernel/` and keyword-sweep facts below.
* **Source-derivable, read not run**: the two live buffers in `normalize`; that
  `opaque` blocks delta-reduction; the sticky-range logic in the diff.
* **Upstream's claim, neither measured nor derived here**: that the wrap yields a
  use-after-free, and that this "could be extended into a proof of False". Note
  the PR's own hedge — success depends on what the allocator puts in the recycled
  block, so it is heap-layout-dependent, not deterministic. No post-fix toolchain
  was built, so every statement about the fix's effect is a reading of the diff.
* **Not consulted**: whether `nanoda`, Lean4Lean or `lean4checker` are exposed.
  The PR body's sentence — *"Other kernels such as nanoda not based on the Lean
  runtime were not affected"* — is quoted, not extended.

Also worth flagging: the test upstream merged is de-tuned to `depth := 12` (peak
2^13), with `depth := 30` commented out. It exercises the code path; it does not
reproduce the defect. "Upstream shipped a test" should not be read as "upstream
shipped a regression test for the `False`."

## Release status, checked two ways

Ancestry alone is not enough for Lean — release branches carry fixes as
cherry-picks with fresh SHAs, a lesson this catalog learned four days ago and
again this morning. So:

* **By ancestry**: `8df768b731` is an ancestor of neither `v4.33.0` nor
  `v4.34.0-rc1`; `git tag --contains` returns nothing.
* **By content**: the token `sticky` does not occur in
  `src/include/lean/lean.h` on either release branch, and both files the PR adds
  under `tests/elab/` are absent from both.

**Live on every released toolchain** as of 2026-08-20.

## Two consequences for this catalog's own method

Both measured against the commit.

**The `src/kernel/` filter misses it, and so would `src/Lean/`.** The diff touches
zero files under `src/kernel/` — it is `src/include/lean/lean.h`,
`src/runtime/object.cpp`, and two tests. §2.6 already records the lesson
*"soundness is not a property of `src/kernel/`"*, learned when #14609 turned out
to live in `src/Lean/`. This is the stronger instance: soundness is not a property
of the Lean-logic code **at all**.

**The keyword sweep is vindicated for the first time.** §5.2's corrected sweep,
`git log v4.34.0-rc1..origin/master --grep="proof of false" -i`, returns this
commit — because the PR *body* contains the phrase. Every previous pass over that
method ended in a correction to it. The postmortem-driven method would miss this
one entirely: there is no postmortem, and the reliable index is the GitHub label
`runtime-soundness`, which is not text in the commit.

## The provenance line

Reported by **Daniel Selsam (OpenAI) using their internal models** — the PR body's
own wording. That is the same reporter as #14607–#14616 in July and #14806/#14807
on 2026-08-17/18, and the same effort credited in the nine Rocq
`kind: inconsistency` issues of 2026-08-20 that
[the wave report](2026-08-20-rocq-august-wave.md) and
[the Lean transfer table](2026-08-20-rocq-wave-to-lean.md) cover. Grouping those
into one campaign is this catalog's inference across PRs, not an upstream claim.

What the grouping suggests is a change of altitude rather than of subsystem.
Having worked through the kernel's logic, the same effort found the counter
underneath it. A catalog organised by *what the audit reports* should notice that
the trusted computing base now demonstrably includes the allocator: no logical
rule was broken, `#print axioms` had nothing to say, and an independent checker
built on the same runtime would inherit the same hole.
