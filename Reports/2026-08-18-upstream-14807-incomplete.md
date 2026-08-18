# Draft upstream report: lean4#14807's fix does not reach `inductive.h`

**Intended recipient:** a follow-up comment on
[leanprover/lean4#14807](https://github.com/leanprover/lean4/pull/14807), or a
new issue referencing it. Written to be pasted; the prose below is the report,
not a summary of one.

**Status here:** the source claim is verified against both branches; the
behavioural claim is measured on `v4.33.0`. It is **not** a proof of `False` on
any toolchain, and the report says so.

---

## The report

#14807 fixed `type_checker::is_prop` by replacing `whnf(infer_type(e))` with
`ensure_sort`, so that a term whose inferred type does not reduce to a sort is
rejected rather than reported as "not a proposition". The commit message
explains why the negative answer was dangerous: `infer_proj` reads it as
permission to project a non-proof field out of a value being used as a `Prop`.

`type_checker::is_prop` is not the only place in the kernel that reduces a type
and matches it against `Sort`. `to_cnstr_when_structure`
(`src/kernel/inductive.h`) hand-inlines the same predicate:

```cpp
expr s = whnf(infer_type(e_type));
// See `type_checker::is_prop`: zero must be tested up to normalization, e.g. `imax 1 0` is `Prop`.
if (is_sort(s) && normalizes_to_zero(sort_level(s)))
    return e;
return expand_eta_struct(env, e_type, e);
```

The comment dates the copy: `normalizes_to_zero` was carried here by hand when
#14613 was fixed. The `is_sort(s) &&` conjunct came with it, and that conjunct is
#14807's defect — a **stuck** reduct answers "not a proposition".

Here the negative answer is again permission, and arguably a stronger form of it.
Control falls through to `expand_eta_struct`, which fabricates
`mk_proj(I, i, e)` for every field of the structure and hands the result to the
recursor's computation rule. Those projection nodes are **created by the kernel
inside a reduct**; none of them passes through `infer_proj`, which is the guard
#14807 restores.

**The fix does not reach this site.** `to_cnstr_when_structure` is byte-identical
on `releases/v4.33.0` and on `master` at the time of writing, so the pattern
survives the patch written for it.

A `grep -n 'is_sort('` over the whole kernel returns seven hits. Five assert or
throw — `expr.h` (definition and `lean_assert`), `instantiate.cpp` (level
substitution), and `type_checker.cpp`'s `ensure_sort_core`, which throws, and
which is the correct pattern. The remaining two are the reduce-and-match sites:
`type_checker.cpp`'s `is_prop`, which #14807 fixes, and this one. **Of the two,
only `inductive.h` reads the negative answer as permission to emit new terms
rather than as permission to skip a check.**

### What is and is not claimed

This is **not** a proof of `False` on any released toolchain, and I have not been
able to make it one. Reaching the site needs #14807's own stuck sort, and the
inductive that produces one there is `Prop`-valued, so its recursor eliminates
only into `Prop`. Extracting data still requires `infer_proj` — which is exactly
what #14807 closes.

The blocker looks structural rather than incidental: a `Prop`-valued
one-constructor structure carrying a data field gets a `Prop`-only recursor
(`levelParams = []`, and the frontend refuses its projection outright with
*"field must be a proof, but it has type Bool"*), while a subsingleton that
large-eliminates has no data to extract. Measured on `v4.33.0`.

So the request is not "this is exploitable". It is that **after #14807 ships,
this site is still open**, it is the only remaining place in the kernel where an
unreducible type yields permission rather than rejection, and the thing it
permits is the fabrication of projections. Whatever argument justifies
`ensure_sort` at `type_checker.cpp` appears to apply here verbatim.

### Measured behaviour, for completeness

On `v4.31.0`, `v4.32.2`, `v4.33.0` and `v4.34.0-rc1`, using the surface
`inductive` command rather than raw kernel calls: with the #14807 construction's
`Owner : ∀ (h : P), gate h`, `Kernel.whnf` of the recursor applied to the
stuck-sorted instantiation **eta-expands** (`fun bit => True.intro`), while the
honest control at a reducing instantiation stays stuck. Identical on all four.

### Suggested fix

Use `ensure_sort` here as #14807 does in `type_checker.cpp`, or better, call
`type_checker::is_prop` rather than re-implementing it — the duplication is what
let the two copies drift apart across #14613 and #14807.
