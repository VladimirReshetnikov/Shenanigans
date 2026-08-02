# A safe declaration that makes a released Lean kernel store constants it rejects

**Date:** 2026-08-01
**Source line numbers** are `v4.32.2`'s unless stated otherwise.
**Toolchains measured:** `v4.27.0-rc1`, `v4.30.0-rc2`, `v4.31.0`, `v4.32.0`, `v4.32.1`,
`v4.32.2`, `v4.33.0-rc1`, against `leanprover/lean4` at `5fa71c9141`.
**Artifacts:** [`Audits/Lean/Nested/IllTypedStoredConstructor.lean`](../Audits/Lean/Nested/IllTypedStoredConstructor.lean),
reconnaissance [`Audits/Lean/Nested/AuxNameReachability.lean`](../Audits/Lean/Nested/AuxNameReachability.lean).

---

## Claim

On every released Lean toolchain, a **safe** module — no flag, no `sorry`, no
axiom, no `unsafe`, `lean --trust=0` exit 0, `#print axioms` clean — can make the
kernel store three constants that the *same kernel's own type checker* rejects:
a constructor, its inductive type's recursor, and that recursor's computation
rule.

This is [lean4#14616](https://github.com/leanprover/lean4/pull/14616)'s mechanism
reached from the safe path. `master` rejects it up front, so it is not a new
defect there. What is new is the route, and the route is the interesting part:
**`check_positivity` cannot see an occurrence that `whnf` erases, and it is the
only gate on the safe path.**

No `False` is derived. §"Why it is inert" says why, and what closing that gap
would need.

---

## Background in three sentences

When the kernel eliminates a nested inductive it creates auxiliary types under
the reserved prefix `_nested` in a *temporary* environment, checks the
declaration there, and then `restore_nested` rewrites those names back to the
real nested occurrences. A declaration naming one of those auxiliaries is
therefore checked against one type and stored with another. #14616 closes this on
`master` with `check_no_nested_aux`; no released toolchain has it, and the
postmortem notes the exploit **cannot be captured as an arena export test**,
which is why no reproduction exists anywhere.

## What was already closing the safe path

[`AuxNameReachability.lean`](../Audits/Lean/Nested/AuxNameReachability.lean)
measures the reachable surface. The auxiliary name is predictable —
`mk_unique_name(*g_nested + J)` (inductive.cpp:1014, :910) appends `_1`, `_2`, …
so the first auxiliary for a nested `Wrap` is exactly `_nested.Wrap_1` — and a
safe declaration naming it *is accepted*. But the two levers that would create a
checked/stored mismatch both die in `check_positivity`:

```cpp
} else if (is_valid_ind_app(t)) {          // inductive.cpp:452ff
```
```cpp
bool is_valid_ind_app(expr const & t, unsigned i) {
    expr I = get_app_args(t, args);
    if (I != m_ind_cnsts[i] || args.size() != m_nparams + m_nindices[i]) return false;
    for (...) if (m_params[i] != args[i]) return false;
```

`I != m_ind_cnsts[i]` is `expr` equality on a constant, which covers **both** the
name and the universe levels — so a swapped level and a swapped parameter are
equally rejected, with `contains a non valid occurrence of the datatypes being
declared`. The `Expr.proj` lever dies on ordering instead: `add_inductive_fn` runs
`declare_inductive_types()`, then `check_constructors()`, then
`declare_constructors()`, so while a constructor is being checked the auxiliary's
*constructor* does not exist yet and `infer_proj` reports
`unknown constant '_nested.Wrap_1.mk'`. And `isUnsafe`, which does skip
positivity, loses to the safety gate afterwards.

## The route

`check_positivity` begins:

```cpp
void check_positivity(expr t, name const & cnstr_name, int arg_idx) {
    t = whnf(t);
    if (!has_ind_occ(t)) {
        // nonrecursive argument
    } else if (is_pi(t)) { ...
```

A field whose type *reduces* to something with no occurrence of the types being
declared is dismissed without being looked at. But the kernel stores the
**unreduced** type, and `restore_nested` rewrites `_nested` occurrences inside it.
So hide the auxiliary behind a definition that discards its argument:

```lean
def Ignore (_ : Prop) : Prop := True
```

`whnf (Ignore X)` is `True` for every `X`, so positivity returns at its first
branch. `Ignore X` still demands `X : Prop`, which the auxiliary satisfies at
`.{0}`, so the declaration type-checks. And after restoration the argument is
`Wrap (@B n)`, which lives in `Sort u`.

```lean
run_cmd liftCoreM (addDecl (.inductDecl [`u] 1
  [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
     ctors := [{ name := `B.node
                 type := .forallE `n (.const `Nat [])
                          (.forallE `w1 (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                            (.forallE `w2 (.app (.const `Ignore [])
                                             (.app (.const `_nested.Wrap_1 [.zero]) (.bvar 1)))
                              (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] false))
```

`isUnsafe` is `false`. What is stored is

```
B.node : (n : Nat) → Wrap (B n) → Ignore (Wrap (B n)) → B n
```

and `Kernel.check` — the same type checker that accepted the declaration —
rejects it:

```
(kernel) application type mismatch
  Ignore (@Wrap (@B n))
argument has type
  Sort u
but function has type
  Prop → Prop
```

as it does `B.rec` and `B.rec`'s computation rule for `B.node`.

**The eraser is the whole difference.** The identical field written with
`def Keep (p : Prop) : Prop := p`, whose `whnf` does not erase the occurrence, is
rejected by positivity. That control is in the artifact.

## Measured behaviour

`lean --trust=0 IllTypedStoredConstructor.lean`, counting the stored constants
the module's own `Kernel.check` pass rejects. The module's `#guard_msgs` asserts
the stored `B.node`, so exit 0 also means the stored type is exactly the one
quoted above.

| Toolchain | exit | stored constants rejected by `Kernel.check` |
| --- | --- | --- |
| `v4.27.0-rc1` | 0 | 3 |
| `v4.30.0-rc2` | 0 | 3 |
| `v4.31.0` | 0 | 3 |
| `v4.32.0` | 0 | 3 |
| `v4.32.1` | 0 | 3 |
| `v4.32.2` | 0 | 3 |
| `v4.33.0-rc1` | 0 | 3 |

The three are `B.node`, `B.rec`, and `B.rec`'s computation rule for `B.node`. The
inductive type `B` itself re-checks fine, which is the expected shape: the
auxiliary only ever appeared in a constructor field.

## Why it is inert

`Ignore X` is definitionally `True` whichever argument it holds, so every *use* of
the constructor reduces past the ill-typed application. The ill-typedness is
latent — the same verdict [#14631](https://github.com/leanprover/lean4/pull/14631)
reached about `proj_sname`, "a broken local invariant with no reachable
consequence."

And the escape is the reason for the inertness. For the occurrence to survive
`whnf` it must appear in the reduced type, and then positivity sees it; for
`whnf` to erase it, the wrapper must discard it, and then it cannot mean
anything. A route to `False` from here needs a wrapper that erases the occurrence
from the reduced form while the restored argument still changes what the type
means — and since `restore_nested` alters only the argument, and the wrapper is a
fixed constant, the only thing that can differ is the argument's universe, which
is exactly what an erasing wrapper throws away.

## Consequences

**lean4#14621 is load-bearing on the release line, not redundant.** Its own
comment reads:

> The preceding checks are expected to make this redundant; it is cheap and it
> keeps a mistake in the restoration from reaching the environment. **Note**:
> these checks are not necessary. We added them to catch additional bugs and
> missing checks in the nested inductive handling.

On `master` that is fair, because `check_no_nested_aux` fires first. On every
released toolchain there is no such check, and this is a concrete safe
declaration whose stored output the re-check would reject. Layered defence
working exactly as intended — and an argument for backporting #14621 alongside
#14616 rather than instead of it.

**`check_positivity`'s leading `whnf` is worth recording on its own.** It makes
positivity's answer depend on the *reduced* form while everything downstream —
storage, `restore_nested`, and `is_rec()`, which scans the raw expression
syntactically — uses the unreduced one. Here the disagreement is exploited
through `_nested`; it is a standing gap between two views of the same
constructor type.

## Scope and honesty

* **Not a `False`.** This is a kernel defect exhibit without a demonstrated
  exploit, in the same category as the `Nat.shiftLeft` abort of
  [`2026-07-31-kernel-shiftleft-panic.md`](2026-07-31-kernel-shiftleft-panic.md).
  It lives in `Audits/`, not `KernelDefects/`, for exactly that reason.
* **Not a `master` defect.** `check_no_nested_aux` rejects the declaration
  because it names `_nested.Wrap_1` as a constant.
* **Reachable only through metaprogramming**, like every defect in the July 2026
  wave, and for the reason the postmortem gives that is not a mitigation.
* **`comparator` is unaffected**, and #14607's commit message says why for the
  neighbouring fvar case: `lean4export` refuses declarations containing free
  variables or metavariables, and it would likewise not emit a declaration naming
  a transient auxiliary.

## A negative result recorded alongside

[#14607](https://github.com/leanprover/lean4/pull/14607) — "missing
`check_no_metavar_no_fvar` checks at `inductive.cpp`" — is the *third* July fix
absent from every release, and CATALOG §2.2 lists it among the defects that
yielded an axiom-free `False`. Five shapes were tried on `v4.32.2`: a free
variable as a plain field type; in a nested occurrence's parameter; in a separate
field beside a nested occurrence; in a **phantom** host parameter, which is the
shape that survives into `m_aux2nested` without appearing in the auxiliary type
or its constructor; and metavariables in the same positions plus an index.

**All five are rejected**, and the phantom one is rejected by a check that is
easy to miss when reading the diff: `add_inductive` already ran

```cpp
res.m_aux2nested.for_each([&](name const &, expr const & nested) {
        tc.check(nested, inductive_decl(d).get_lparams());
    });
```

on every stored nested occurrence, which catches free variables and
metavariables there. So if #14607 is reachable on a released kernel it is by some
other shape; these five are not it.
