# Checking the exhibits against `leanprover/comparator`

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's
trustworthy judge for Lean proofs, built for the AIMO competitions. Given a
`Challenge` module containing `theorem boom : False := sorry` and a `Solution`
module claiming to prove it, comparator guarantees the solution's theorem

1. proves the same statement as the challenge,
2. uses no more axioms than permitted, and
3. is accepted by the Lean kernel.

**Every exhibit in `../Lean/` is rejected by comparator.** That is the correct
outcome.

**But `accepted/` is accepted** — a proof of `False` that comparator passes, exit 0,
`Your solution is okay!`, with `#print axioms boom` reporting nothing. See
[The accepted case](#the-accepted-case) below for what it does and does not show.

## Results

Run on comparator `master` (2026-07-28) with Lean `v4.33.0-rc1`.

| Project | Verdict | Message |
| --- | --- | --- |
| `control` | **accepted**, exit 0 | `Your solution is okay!` |
| `natgcd` | rejected, exit 1 | `Const does not match between challenge and target 'Nat.shiftRight'` |
| `reducebool` | rejected, exit 1 | `Const does not match between challenge and target 'Nat.shiftRight'` |
| `natadd` | rejected, exit 1 | `Const does not match between challenge and target 'String.ofList'` |
| `stringfab` | rejected, exit 1 | `Const does not match between challenge and target 'String.ofList'` |

`control` is an honest solution (`theorem easy : 1 + 1 = 2 := by rfl`). It is
included because without a *passing* control the four rejections would prove
nothing — they could just be the harness failing on Windows.

## This class of construction was already known to the Lean FRO

Comparator's own regression suite contains
[`tests/projects/primitive_issue`](https://github.com/leanprover/comparator/tree/master/tests/projects/primitive_issue),
whose `Solution.lean` is *essentially identical* to `../Lean/NatGcdFreeName.lean`:

```lean
prelude
import Init.Prelude
import Init.Core

def Nat.gcd (_ _ : Nat) : Nat := 0

theorem thm1 a b : Nat.gcd a b = 0 := by unfold Nat.gcd; rfl
theorem thm2 : Nat.gcd 1 1 = 1 := rfl

theorem boom : False := Nat.noConfusion <| Eq.trans (thm1 1 1).symm thm2

-- The following are just to make the export "primitive-complete"
def Nat.land (_ _ : Nat) : Nat := 0
...
```

with `test.json` asserting `"exit_code": 1`. So the "define a kernel-primitive
name the prelude has not claimed" construction is a known one with a deployed
safeguard and a regression test.

## How the check works

`Main.lean:primitiveTargets` pins a list of kernel-special-cased constants
("List from `git grep new_persistent_expr_const src/kernel/`"), and
`Comparator/Compare.lean:compareAt` seeds a worklist with those *plus* every
constant used in the challenge statement, then transitively demands full
`ConstantInfo` equality (type **and** value) between the two exported
environments. A solution that supplies its own `Nat.gcd` — or its own `False`,
or its own `String.ofList` — differs on one of those constants and is rejected.

## The accepted case

`accepted/` contains a `Challenge`/`Solution` pair that comparator **accepts**:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT=0
```

`Solution.lean` proves `theorem boom : False`, and `#print axioms boom` reports
*'boom' does not depend on any axioms*. Every one of comparator's three
guarantees is formally satisfied: the statement matches the challenge's, no
axioms beyond the permitted (empty) list are used, and the Lean kernel accepts
the replayed environment.

### The idea

`Main.lean:primitiveTargets` carries this comment:

> The challenge needs to have all the built-in constants of the kernel, as the
> kernel makes no guarantees when fed other definitions here.

and the README's step 4 states:

> This always includes the declarations from `Init` with special meaning to the
> kernel. **Both `Challenge` and `Solution` therefore need to import the default
> prelude.**

**Nothing enforces that.** `compareAt` checks only that the challenge and the
solution *agree* on those constants — never that they are the *real* ones. So if
the challenge is itself a `prelude` module that never imports `Init`, the entire
primitive mechanism is vacuous: challenge and solution agree perfectly on a set
of primitives that are not Lean's.

`accepted/Challenge.lean` and `accepted/Solution.lean` share a byte-identical preamble
declaring `False`, `Nat`, `Bool`, `List`, `String`, the 15 `primitiveTargets`
constants — and

```lean
inductive Char : Type where
  | ofNat : Empty -> Char
```

`Char.ofNat` is the name the kernel uses when expanding a string literal
(`string_lit_to_constructor` builds `String.ofList (List.cons (Char.ofNat 97)
List.nil)` by name, unchecked). Here its field type is `Empty`, so evaluating a
bare `"a"` makes the kernel fabricate an inhabitant of a type with no
constructors. The rest is three lines of `rec`.

Note it is *identical* in both modules, so even a complete primitive list that
compared `Char.ofNat` would not have caught this. What would catch it is
comparing the primitives against the **checker's own** `Init`, rather than
against the challenge.

### What this does and does not show

* It does **not** break comparator's logic. It defeats a *documented
  precondition* that comparator neither enforces nor warns about, and it relies
  on the kernel bug that README assumption 5 ("The Lean kernel is correct")
  explicitly excludes.
* It does **not** affect a normally-written challenge. An AIMO-style challenge
  that imports `Init` has core's `Char.ofNat : Nat → Char`, and a solution
  cannot displace it — I verified that every kernel-hooked name comes bundled
  with the primitives in the import graph (see below).
* It **does** show that a challenge author gets no protection from the primitive
  mechanism unless they import the standard prelude, and that comparator will
  not tell them so. The same construction works with any kernel-hooked name,
  including `Nat.zero`/`Nat.succ` (commented out of `primitiveTargets`), because
  agreement is all that is ever required.

### Suggested fix

Have comparator validate the primitives against the `Init` of the Lean
installation it is running under, or at minimum assert that both modules
transitively import `Init` — instead of only checking challenge/solution
agreement.

## A gap in the list (not reachable against a normal challenge)

`primitiveTargets` omits several names the kernel really does hard-code:

* `Lean.reduceBool` and `Lean.reduceNat` — both created with
  `new_persistent_expr_const` in `src/kernel/type_checker.cpp`, so they *are*
  matched by the comment's own stated `git grep`, yet are absent from the list.
* `Char.ofNat`, `List.cons`, `List.nil`, `String.mk`, `Char`, `List`, `Nat`,
  `String` — used by `string_lit_to_constructor`/`nat_lit_to_constructor`. These
  appear only in `builtinTargets`, which is returned **only when
  `enable_nanoda` is true**; with the default `false` they are never compared.
  (`String`, `Char` and `List` are still reached transitively from
  `String.ofList`'s type; `Char.ofNat`, `List.cons` and `List.nil` are not.)
* `eagerReduce` — kernel-special-cased, though created with `new name` rather
  than `new_persistent_expr_const`, so arguably outside the comment's scope.

I could not turn any of these into an accepted solution. The reason is a
structural one worth recording: to make the export "primitive-complete" *and*
supply the permitted axioms, the solution must import enough of `Init` — and by
the time `Init.Core` is imported, `Lean.reduceBool`, `Lean.reduceNat` and
`eagerReduce` are all defined by core, so they can no longer be claimed. The
`reducebool` project above was caught only incidentally, by the `Nat.shiftRight`
stub it had to declare to satisfy the export.

Separately, Lean `v4.33.0-rc1` reports `Lean.reduceBool` as **deprecated**
("in-kernel native reduction is deprecated; assert native evaluations with
axioms instead"), so that hook is on its way out regardless.

## Update 2026-08-01: `comparator.live` now enables `nanoda` by default

De Moura's [#14576
postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)
records that [`comparator.live`](https://comparator.live.lean-lang.org/) now runs
`nanoda` by default, and that `nanoda` is tracked daily so the hosted judge does
not drift behind upstream fixes. The standalone CLI is unchanged — the README's
example config and the `config.json` files here still carry
`"enable_nanoda": false`, which is what everything above was measured under.

What this does and does not change, stated carefully, because two things are
easily conflated:

* **The `builtinTargets` gap closes for the hosted judge.** With `enable_nanoda`
  true, `Char.ofNat`, `List.cons`, `List.nil` and `String.mk` are compared. That
  removes the omission described just above.
* **It does not close the `accepted/` construction**, whose whole point is that
  comparison is for *agreement*, never genuineness. `accepted/Challenge.lean` and
  `accepted/Solution.lean` share a byte-identical `Char.ofNat : Empty → Char`, so
  a wider target list compares it and finds it equal — as noted above, "even a
  complete primitive list that compared `Char.ofNat` would not have caught this."
* **The real new obstacle is `nanoda` itself**, as a second kernel that must also
  accept the solution. Whether it does is **untested here**, and it is the obvious
  next measurement: `nanoda` would have to reproduce Lean's `string_lit_to_constructor`
  behaviour of assembling `Char.ofNat` by name without checking it. Do not assume
  either answer from this file.

The relevant caution is §3.0 of [`../../../CATALOG.md`](../../../CATALOG.md):
adding a second checker raises the bar by however much the two checkers' blind
spots differ, which in the one case where it was measured was less than it looked.

Upstream has meanwhile removed one adjacent foothold. Lean
[#14632](https://github.com/leanprover/lean4/pull/14632) (merged 2026-08-01) makes
`add_quot` refuse to declare `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` over existing
names — a path its own description says "only a module replacing the prelude can
arrange, and which Comparator already reports." That is the same prelude-replacing
precondition this directory's exhibits rely on; it is now one constant family
narrower, and none of the exhibits here used it.

## Reproducing

Comparator needs Lean `v4.33.0-rc1`, `lean4export`, and `landrun`. `landrun` is
Linux-only; `fake-landrun.c` here is a Windows stand-in for the repository's
`scripts/fake-landrun.sh` (it does **no** sandboxing — it is only for testing
comparator's *verification* logic, never for judging untrusted input).

```bash
git clone https://github.com/leanprover/comparator
cd comparator && lake build lean4export comparator
gcc -O2 -o fake-landrun.exe path/to/fake-landrun.c

cd <one of the project directories here>
COMPARATOR_LANDRUN=/path/to/fake-landrun.exe \
COMPARATOR_LEAN4EXPORT=/path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env /path/to/comparator/.lake/build/bin/comparator config.json
```

The `Solution.lean` files here carry extra stub definitions of the kernel
primitives (`Nat.land`, `String.ofList`, …). Those are not part of the construction;
they exist only so `lean4export` can emit a primitive-complete export, exactly as
in comparator's own `primitive_issue` test.
