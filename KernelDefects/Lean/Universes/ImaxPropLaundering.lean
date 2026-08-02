/-
KERNEL DEFECT.  An axiom-free `theorem Paradox : False`, accepted by the *released*
Lean kernel under `--trust=0`, with `#print axioms` reporting nothing.

Category: `KernelDefects/` (see ../../../README.md).  Not a `prelude` module, so
lean4#13626's "the kernel assumes the official prelude" policy does not cover it:
every constant used below is the genuine core one.

Upstream: lean4#14613, fixed on `master` 2026-07-31 by commit 17dbc815cf.
No released toolchain carries the fix; see the matrix in
../../../Reports/2026-08-01-imax-prop-laundering.md.

--------------------------------------------------------------------------------
The defect needs TWO independent kernel weaknesses, not one.  Upstream's commit
message and its regression test (`tests/elab/kernelImaxProp.lean`) name only the
second.  (1) below is the first, and it is *not* fixed on master.

  (1) LAUNDERING.  `add_inductive_fn::check_inductive_types` (inductive.cpp:248)
      sets `m_result_level` from the FIRST type of a mutual block and only
      requires the others to be `is_equivalent` to it.  Every downstream gate then
      reads that one spelling.  `check_constructors` (inductive.cpp:439) admits a
      constructor field whose universe exceeds the inductive's when

          is_geq(m_result_level, fieldLevel)  ||  is_zero(m_result_level)

      and `is_zero` is *syntactic* (level.h:106, `kind() == Zero`) while `is_geq`
      normalizes (level.cpp:527).  So `Sort (imax 1 0)` — which denotes `Prop` —
      earns the data-field permission only when some *other* type in the same
      block is spelled `Sort 0`.  MutualResultLevel.lean measures this directly,
      including the reversal, which fails.

  (2) SPELLING.  `type_checker::is_prop` (type_checker.cpp:328) compares
      `whnf(infer_type(e))` against `Prop` syntactically, so it answers `false`
      for `Sort (imax 1 0)`.  `infer_proj` (type_checker.cpp:248, and the guards
      at :253 and :263) skips its "a field of a proof must be a proof"
      restriction when `is_prop` says no.

  Line numbers are v4.32.2's; on the pinned master they are 439/248 unchanged,
  is_prop at 351 and the infer_proj guards at 266/271/281.

  The join is that ONE type is reached through TWO spellings of its own sort.
  Proof irrelevance is consulted through the `Sort 0` spelling (`Paradox.AsProp`)
  and the projection guard through the `Sort (imax 1 0)` spelling (`Weird`), and
  they disagree.  Neither spelling is wrong; the kernel simply never compares them.

The elaborator normalizes levels eagerly, so `Sort (imax 1 0)` is not writable in
surface syntax and the declaration below has to be handed to the kernel directly.
That is not a mitigation — see the postmortem's own paragraph on why soundness
cannot rest on an untrusted elaborator refusing to build a bad term.
-/
import Lean.CoreM
import Lean.AddDecl

open Lean

namespace Paradox

/-! ### Step 1 — the laundered declaration

`Dummy : Sort 0` is inert; its only job is to be *first*, so that
`m_result_level` is the syntactic `Level.zero` for the whole block.  `Weird` is
then admitted with a `Bool` field even though its own sort is spelled
`Sort (imax 1 0)`.  Declared alone it is rejected — see MutualResultLevel.lean. -/

#eval show CoreM Unit from
  addDecl <| .inductDecl [] 0 [
    { name  := `Paradox.Dummy
      type  := .sort .zero
      ctors := [{ name := `Paradox.Dummy.intro, type := .const `Paradox.Dummy [] }] },
    { name  := `Paradox.Weird
      type  := .sort (.imax (.succ .zero) .zero)
      ctors := [{ name := `Paradox.Weird.mk
                  type := .forallE `value (.const ``Bool []) (.const `Paradox.Weird []) .default }] }
  ] false

-- The recursor is correctly restricted to `Prop` motives: the kernel's
-- `elim_only_at_universe_zero` does the right thing here, and this route never
-- uses the recursor at all.
#guard_msgs (drop info) in
#check @Paradox.Weird.rec

/-! ### Step 2 — the second spelling

`Sort (imax 1 0) =?= Sort 0` holds because level equality *does* normalize
(`is_equivalent`, level.cpp:503).  So this alias is honest, and it is what
`is_prop` will see. -/

def AsProp : Prop := Weird

theorem left  : AsProp := Weird.mk false
theorem right : AsProp := Weird.mk true

/-- Proof irrelevance, consulted through the `Sort 0` spelling.  Both sides
really are proofs of a proposition, so this step is *correct*. -/
theorem irrel : left = right := rfl

/-- info: 'Paradox.irrel' does not depend on any axioms -/
#guard_msgs in
#print axioms irrel

/-! ### Step 3 — the projection, guarded through the other spelling

`infer_proj` asks `is_prop (Weird)`, gets `Sort (imax 1 0)`, compares it to
`Sort 0` syntactically, and concludes "not a proposition" — so it does not
require the projected field to be a proof.  On `master` this raises
`(kernel) invalid projection`. -/

#eval show CoreM Unit from
  addDecl <| .defnDecl {
    name        := `Paradox.leak
    levelParams := []
    hints       := .abbrev
    safety      := .safe
    type        := .forallE `proof (.const ``AsProp []) (.const ``Bool []) .default
    value       := .lam `proof (.const ``AsProp []) (.proj `Paradox.Weird 0 (.bvar 0)) .default }

/-! ### Step 4 — `False`

`leak` is a function, `irrel` says its two arguments are the same proof, and the
kernel's own iota rule says the results are `false` and `true`. -/

theorem boom : False :=
  Bool.noConfusion (show false = true from congrArg leak irrel)

-- The whole point: the audit is clean.
/-- info: 'Paradox.boom' does not depend on any axioms -/
#guard_msgs in
#print axioms boom

/-! ### The same defect through a second spelling of zero

`max 0 0` is not `Level.zero` either, and `is_zero` is just as syntactic about
it.  Upstream's commit message and regression test name only `imax 1 0`; the
class is "every spelling of zero that is not literally `Level.zero`". -/

#eval show CoreM Unit from
  addDecl <| .inductDecl [] 0 [
    { name  := `Paradox.Dummy2
      type  := .sort .zero
      ctors := [{ name := `Paradox.Dummy2.intro, type := .const `Paradox.Dummy2 [] }] },
    { name  := `Paradox.Weird2
      type  := .sort (.max .zero .zero)
      ctors := [{ name := `Paradox.Weird2.mk
                  type := .forallE `value (.const ``Bool []) (.const `Paradox.Weird2 []) .default }] }
  ] false

def AsProp2 : Prop := Weird2
theorem left2  : AsProp2 := Weird2.mk false
theorem right2 : AsProp2 := Weird2.mk true
theorem irrel2 : left2 = right2 := rfl

#eval show CoreM Unit from
  addDecl <| .defnDecl {
    name        := `Paradox.leak2
    levelParams := []
    hints       := .abbrev
    safety      := .safe
    type        := .forallE `proof (.const ``AsProp2 []) (.const ``Bool []) .default
    value       := .lam `proof (.const ``AsProp2 []) (.proj `Paradox.Weird2 0 (.bvar 0)) .default }

theorem boom2 : False :=
  Bool.noConfusion (show false = true from congrArg leak2 irrel2)

/-- info: 'Paradox.boom2' does not depend on any axioms -/
#guard_msgs in
#print axioms boom2

end Paradox

-- And the headline, stated the way the catalog states it.
theorem Paradox : False := Paradox.boom

/-- info: 'Paradox' does not depend on any axioms -/
#guard_msgs in
#print axioms Paradox
