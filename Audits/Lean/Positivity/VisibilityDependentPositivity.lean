import Lean
/-!
ANOMALY (no `False`).  **Lean's strict positivity check is not a property of the
declaration being checked.** Whether it accepts depends on which *other*
definitions have visible bodies — so the same three lines of ordinary surface
Lean are accepted or refused according to an abstraction boundary.

Provenance: mining [`Reports/Counterexamples/`](../../../Reports/Counterexamples/)
— Dolan's *Counterexamples in Type Systems* — for Lean analogues. This is the
entry "A little knowledge…", whose stated principle is that exposing the
implementation of a previously-hidden abstract type should never change whether a
program typechecks. Lean violates that principle, in the direction where **more
knowledge means a weaker check**.

MECHANISM.  `check_positivity` (kernel/inductive.cpp:452) begins

    void check_positivity(expr t, name const & cnstr_name, int arg_idx) {
        t = whnf(t);
        if (!has_ind_occ(t)) {
            // nonrecursive argument
        } else if ...

`whnf` unfolds definitions.  So an occurrence of the type being declared is
invisible to positivity exactly when some enclosing definition's body is
available to reduce it away — and visible when that body is hidden behind
`opaque`, or behind a module boundary that does not expose it.

This is the same gap as
[`../Nested/IllTypedStoredConstructor.lean`](../Nested/IllTypedStoredConstructor.lean),
which uses it to reach lean4#14616's checked-vs-stored divergence.  What this
file adds is that the gap is observable in **plain Lean, with no metaprogramming,
no `_nested` name, and no reserved prefix** — and that what it is sensitive to is
an abstraction boundary.

WHY IT IS NOT A PARADOX.  `IgnoreD X` is definitionally `True` whichever `X` it
holds, so the negative occurrence inserted past the check is inert: the field
really is `True`, and `Bad1` really is `Unit`.  The occurrence can only be hidden
from positivity by being erased, and being erased is what makes it harmless — see
that report's "Why it is inert".

Run with plain `lean --trust=0 VisibilityDependentPositivity.lean`.
-/

/-- Body visible.  `whnf (IgnoreD X)` is `True` for every `X`. -/
def IgnoreD (_ : Prop) : Prop := True

/-- Body hidden.  `whnf (IgnoreO X)` is stuck. -/
opaque IgnoreO (_ : Prop) : Prop

/-! ### The declaration positivity accepts

Note what is inside the field: `Bad1`, the type being declared, in a **negative**
position — the shape `check_positivity` exists to refuse (see
[`../../../Paradoxes/Lean/TypeTheoryParadoxes/Blockers.lean`](../../../Paradoxes/Lean/TypeTheoryParadoxes/Blockers.lean) §5,
and Dolan's "Curry's paradox"). -/

inductive Bad1 : Type where
  | mk : IgnoreD (Bad1 → False) → Bad1

/-- info: 'Bad1' does not depend on any axioms -/
#guard_msgs in
#print axioms Bad1

/-- info: Bad1.mk : IgnoreD (∀ (a : Bad1), False) → Bad1 -/
#guard_msgs in
#check @Bad1.mk

/-! ### The identical declaration positivity refuses

Only the visibility of the wrapper's body has changed. -/

/--
error: (kernel) arg #1 of 'Bad2.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad2 : Type where
  | mk : IgnoreO (Bad2 → False) → Bad2

/-! ### Why `Bad1` is harmless

The field is `True`, so `Bad1` is a unit type and the negative occurrence buys
nothing.  That is not a coincidence: for the occurrence to be hidden from
positivity, `whnf` has to erase it, and an erased argument cannot mean anything. -/

example (x : IgnoreD (Bad1 → False)) : True := x
example : Bad1 := Bad1.mk trivial

/-
Expected on every released toolchain through v4.33.0-rc1: exit 0, with all three
`#guard_msgs` satisfied.

The same flip is reachable across a real module boundary rather than via
`opaque`: put the wrapper in a `module` that does not `@[expose]` it, and the
importing module's kernel cannot unfold it either.  `opaque` is used here because
it makes the whole anomaly a single self-contained file.
-/
