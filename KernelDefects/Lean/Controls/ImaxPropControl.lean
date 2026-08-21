/-
CONTROL for ../Universes/ImaxPropSpelling.lean.

Same construction, honest spelling: the inductive's sort is written `Sort 0`
rather than `Sort (imax 1 0)`.  Everything else — the `Bool` field in a `Prop`,
the `Prop` alias, the two proofs, proof irrelevance — is unchanged and is
accepted, because a proposition carrying data is perfectly legal (it is the
squashed/`exProp` type; its recursor simply cannot eliminate).

The one step that must fail is the projection.  With the sort spelled honestly,
`is_prop` answers `true`, `infer_proj` applies its restriction, and the kernel
refuses to hand back the `Bool`.

Acceptance of the exhibit means something only because this is rejected by the
same procedure on the same toolchain.
-/
import Lean.CoreM
import Lean.AddDecl

open Lean

namespace Control

#eval show CoreM Unit from
  addDecl <| .inductDecl [] 0 [
    { name  := `Control.Dummy
      type  := .sort .zero
      ctors := [{ name := `Control.Dummy.intro, type := .const `Control.Dummy [] }] },
    { name  := `Control.Honest
      type  := .sort .zero
      ctors := [{ name := `Control.Honest.mk
                  type := .forallE `value (.const ``Bool []) (.const `Control.Honest []) .default }] }
  ] false

def AsProp : Prop := Honest

theorem left  : AsProp := Honest.mk false
theorem right : AsProp := Honest.mk true

-- Proof irrelevance still holds — that was never the defect.
theorem irrel : left = right := rfl

/-- info: 'Control.irrel' does not depend on any axioms -/
#guard_msgs in
#print axioms irrel

-- The projection is refused.  This is the exact message the released kernel
-- does *not* produce when the same sort is spelled `Sort (imax 1 0)`.
/--
error: (kernel) invalid projection
  proof.1
-/
#guard_msgs in
#eval show CoreM Unit from
  addDecl <| .defnDecl {
    name        := `Control.extract
    levelParams := []
    hints       := .abbrev
    safety      := .safe
    type        := .forallE `proof (.const ``AsProp []) (.const ``Bool []) .default
    value       := .lam `proof (.const ``AsProp []) (.proj `Control.Honest 0 (.bvar 0)) .default }

end Control
