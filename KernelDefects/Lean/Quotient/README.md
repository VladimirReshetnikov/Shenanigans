# The kernel applies quotient computation rules to constants the user declared

> **Warning.** This directory contains a machine-checked proof of `False` that
> **Lean v4.33.0, v4.33.1 (current stable) and v4.34.0-rc2 all accept**, with no
> axiom, no `sorry`, and no flag.

    pwsh KernelDefects/Lean/Quotient/verify.ps1
    pwsh KernelDefects/Lean/Quotient/verify.ps1 -Toolchains v4.33.0,v4.33.1,v4.34.0-rc2

**Found here, 2026-08-21**, by reading `src/kernel/quot.h` and
`src/Lean/Environment.lean`. Not reported upstream at the time of writing.

## The flag that is guessed rather than established

`Kernel.Environment.quotInit` decides whether the kernel may fire the quotient
computation rule. Its own docstring states the invariant:

> `quotInit = true` if the command `init_quot` has already been executed for the
> environment, and `Quot` declarations have been added to the environment. **When
> the flag is set, the type checker can assume that the `Quot` declarations in
> the environment have indeed been added by the kernel and not by the user.**

But nothing establishes that. The flag is **derived by a heuristic**, in
`src/Lean/Environment.lean`:

```lean
quotInit := !imports.isEmpty -- We assume `Init.Prelude` initializes quotient module
```

A `prelude` module chain that never reaches `Init.Prelude` has a **non-empty
import list** and has **never run `init_quot`**. So the flag is `true` while
`Quot`, `Quot.mk` and `Quot.lift` are free names. Measured directly:

```
quotInit = true
Quot      -> defnInfo   (USER-declared)
Quot.mk   -> opaqueInfo (USER-declared)
Quot.lift -> defnInfo   (USER-declared)
```

## The rule that checks nothing

`quot_reduce_rec` (`src/kernel/quot.h`) is keyed on names and an arity, and
performs **no type checking whatsoever**:

```cpp
if (const_name(fn) == *quot_consts::g_quot_lift) { mk_pos = 5; arg_pos = 3; }
...
expr mk = whnf(args[mk_pos]);
if (!is_constant(mk_fn) || const_name(mk_fn) != *quot_consts::g_quot_mk || get_app_num_args(mk) != 3)
    return none_expr();
expr const & f = args[arg_pos];
expr r = mk_app(f, app_arg(mk));      // Quot.lift … f … (Quot.mk _ _ a)  ⟹  f a
```

The single gate on all of it is `env().is_quot_initialized()`
(`type_checker.cpp:394`). Nothing in `environment::add_*` refuses to *declare*
these names — the only `check_name` calls are inside `add_quot`, guarding
`init_quot` against overwriting a user's constant, which is the opposite
direction.

## The construction, and why each piece is there

[`Q/Boom.lean`](Q/Boom.lean) is three declarations:

```lean
noncomputable def Quot (A : Type) (r : A → A → Prop) : Type := MyUnit
opaque Quot.mk (A : Type) (r : A → A → Prop) (a : A) : Quot A r := MyUnit.mk
noncomputable def Quot.lift (A : Type) (r : A → A → Prop) (B : Type)
    (f : A → B) (b0 : B) (q : Quot A r) : B := b0
```

* `Quot` **erases** its arguments to the zero-field structure `MyUnit`, so
  **structure eta makes any two `Quot.mk`s definitionally equal** whatever
  payload they carry.
* `Quot.mk` is **`opaque`**, so `whnf` has no value to unfold and the head stays
  literally `Quot.mk` with three arguments — which is what the rule matches on.
  (A plain `def` unfolds and the rule never fires; a `theorem` is reduced to its
  proof and the rule never fires. Both were measured.)
* `Quot.lift` puts `f` at argument 3 and the `mk` at argument 5, the positions
  the rule reads.

The kernel then holds all of these at once, measured with `Kernel.isDefEq`:

| kernel query | verdict |
| --- | --- |
| `whnf (Quot.lift … (Quot.mk _ _ myTrue))` | `MyBool.myTrue` |
| `whnf (Quot.lift … (Quot.mk _ _ myFalse))` | `MyBool.myFalse` |
| `Quot.mk _ _ myTrue =?= Quot.mk _ _ myFalse` | **true** (structure eta) |
| `myTrue =?= myFalse` | false |

Two terms differing **only** in an argument the kernel calls definitionally
equal reduce to two **different** constructors. Congruence is then proved *in the
logic* with `MyEq.rec` — the kernel is never asked to decide `L1 =?= L2` — and
transporting a discriminating predicate yields `MyFalse`.

## What was measured

[`exploit.lean`](exploit.lean) builds the whole proof as **one self-contained
term** and submits it through `Kernel.Environment.addDeclCore` into a **fresh**
environment, so nothing can have been primed by an earlier declaration.

| | v4.33.0 | v4.33.1 | v4.34.0-rc2 |
| --- | --- | --- | --- |
| exhibit (`Quot.mk`/`Quot.lift`) | **ACCEPTED** | **ACCEPTED** | **ACCEPTED** |
| control (identical shapes, renamed `Safe.mk`/`Safe.lift`) | rejected | rejected | rejected |

The names are the entire difference between the two rows. Also measured:
`MyFalse` has **zero constructors**, and the axiom closure of the proof is
**empty** — no `sorryAx`, no `Classical.choice`, nothing.

## Honest scope, and why it is filed here rather than in `EscapeHatches/`

**It needs `prelude`.** Like the free-name routes of
[`../Accelerators/`](../Accelerators/), the construction cannot be written in a
module that imports `Init.Prelude`, because then the real `Quot` exists and the
names are taken. §2.3 records that upstream closed the analogous
`Lean.reduceBool` free-name route
([lean4#13626](https://github.com/leanprover/lean4/issues/13626)) as
**working-as-intended**, and upstream may well say the same here.

**Two things distinguish it from that family, and they are the reason it is
worth reporting.** The accelerator routes turn on a name-keyed *extension*
firing on a constant that is not the real one. This one turns on a **derived
boolean** standing in for a fact that the derivation cannot establish — the
docstring asserts "added by the kernel and not by the user", and
`!imports.isEmpty` cannot know that. And upstream already treats this exact
surface as worth guarding: [#14632](https://github.com/leanprover/lean4/pull/14632)
added `check_name` to `add_quot` so that `init_quot` cannot overwrite a user's
`Quot` — the mirror image of what happens here.

**The elaborator does not agree with the kernel about these terms.** `Meta.whnf`
gates `reduceQuotRec` on `ConstantInfo.quotInfo`, so it never fires the rule for
a user-declared constant. That is why the proof is submitted through
`addDeclCore` rather than written as a `theorem`: source-level, the elaborator
rejects the very steps the kernel accepts. Measured separately — a `theorem`
the elaborator accepts is then refused by the kernel with
`declaration type mismatch`, and vice versa. The divergence is itself worth
recording, and it is why this is not reachable from ordinary source.

**Cheap fixes, in increasing order of cost.** Serialise `quotInit` instead of
deriving it; or have `quot_reduce_rec` confirm the head is a `quot_val` of the
expected kind, exactly the way `reduce_proj_core` was taught to confirm the
structure name in #14632; or refuse to declare a constant whose name satisfies
`quot_is_decl` when `quotInit` is set.

## The two compiler-internal names

[`Q/Base.lean`](Q/Base.lean) defines `lcErased` and `lcAny`. Those are not part
of the construction: the code generator looks them up **by name** while
compiling an `opaque`, and `Init.Prelude` is not imported here, so they have to
be supplied. They are ordinary `def`s to inert types and play no role in the
`False` — the same free-name situation, one layer down, in the compiler rather
than the kernel.
