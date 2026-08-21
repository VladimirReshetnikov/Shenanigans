/-
KERNEL DEFECT — an axiom-free `False`, live on every released toolchain.

lean4#14807, on its own.  This is the sharpest of the three exhibits here: it
uses the same non-transitive definitional-equality triple, but NOT the def-eq
cache.  Every comparison below comes out the same way in a fresh type-checker
session, so it is independent of whether, and how, that cache is keyed — and
lean4#14806 alone does not close it.

  a := run false 1 seed                    -- `Acc.rec` on an opaque proof: stuck
  b := run false 1 (Acc.intro 1 …)
  c := run false 0 (Acc.inv seed …)

  a ≡ b   (proof irrelevance on the `Acc` argument)
  b ≡ c   (iota)
  a ≢ c   (the two `Acc` proofs have different types: `Acc (·<·) 1` vs `Acc (·<·) 0`)

So `P := a = b` and `Q := a = c` are definitionally equal TYPES whose proofs
behave differently:

  gate h := Eq.rec (motive := fun _ _ => Type) Prop h

K-reduces to `Prop` for `h : P`, because K-like reduction only needs `h`'s type
to be definitionally equal to `Eq.refl a`'s type `a = a`, i.e. `b ≡ a`.  For the
closed `witness : Q` it stays stuck, since that would need `c ≡ a`.

`Owner : ∀ (h : P), gate h` is therefore accepted as a family of PROPOSITIONS —
its recursor only eliminates into `Prop`.  `Owner witness` is well typed, since
`Q ≡ P`; but its sort does not reduce to `Prop`.  `type_checker::is_prop`
computed `whnf(infer_type(e))` and returned `false` when the result was a stuck
term rather than a sort, and `false` means "not a proposition" — which skips
`infer_proj`'s proof-irrelevance guard.  So the `Bool` field can be projected
out of an inhabitant, proof irrelevance identifies two `Owner.mk` applications
carrying different `Bool`s, and observing them gives `False`.

  `#print axioms` reports NOTHING.  `opaque` is not an axiom.

The fix computes the inferred type with `ensure_sort`, so a stuck sort raises
`(kernel) type expected` instead of answering that the type is not a
proposition.  Merged to `master` 2026-08-18; NO RELEASED TOOLCHAIN CARRIES IT.
The ill-typed proof was ALSO accepted by `nanoda`; `lean4lean` is not affected,
because its `isProp` already used `ensureSortCore`.

Verified accepted here on v4.33.0 and v4.34.0-rc1.  Needs v4.33.0 or later to
ELABORATE: `addDeclCore` gained a `maxRecDepth` parameter there.  Upstream's
version evidence for v4.28.0 / v4.29.1 / nightly-2026-08-01 comes from the
version-independent arena export path.

Control: ../Controls/DefEqCollisionControl.lean — the same construction with a
proof of `P` rather than the opaque proof of `Q`, so the sort reduces and the
kernel refuses the projection.

Source: adapted from `tests/elab/kernel_is_prop_ensure_sort.lean` in
lean4#14807; arena test `proj-of-subst-prop`.  Write-up:
../../../Reports/2026-08-18-defeq-cache-and-stuck-sort.md.
-/
import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Subst

def step (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def run (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => step x m) h

opaque seed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def a := run false 1 seed
def b := run false 1 (Acc.intro 1 fun _ => Acc.inv seed)
def c := run false 0 (Acc.inv seed (Nat.lt_succ_self 0))

theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : run x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [run, step] using ih n (Nat.lt_succ_self n)

def P : Prop := a = b
def Q : Prop := a = c

opaque witness : Q := (run_eq false _ _).trans (run_eq false _ _).symm

def gate (h : P) : Type :=
  Eq.rec (motive := fun _ _ => Type) Prop h

theorem observedProofsFalse (T : Prop) (observe : T → Bool) (p q : T)
    (onFalse : observe p = false) (onTrue : observe q = true) : False := by
  have same : p = q := proof_irrel p q
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg observe same).trans onTrue))

def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 0 10000 decl none with
  | .ok next => return next
  | .error _ => throwError "kernel error"

def define (env : Environment) (name : Name) (type value : Expr) : CoreM Environment :=
  checked env (.defnDecl {
    name := name, levelParams := [], type := type, value := value,
    hints := .abbrev, safety := .safe })

end Subst

/--
info: Kernel accepted `inconsistent : False` from a stuck sort after substitution.
-/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  let owner := `Subst.Owner
  let p := mkConst ``Subst.P
  let bool := mkConst ``Bool
  let gate := mkConst ``Subst.gate
  let ownerType := mkForall `h .default p (mkApp gate (.bvar 0))
  let ctorType := mkForall `h .default p <|
    mkForall `bit .default bool (mkApp (mkConst owner) (.bvar 1))
  env ← Subst.checked env (.inductDecl [] 1 [{
    name := owner, type := ownerType,
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false)
  let some (.recInfo ri) := env.toKernelEnv.find? (mkRecName owner)
    | throwError "missing owner recursor"
  unless ri.levelParams.isEmpty do throwError "owner unexpectedly permits large elimination"

  env ← Subst.define env `Subst.asProp
    (mkForall `h .default p (mkSort 0))
    (mkLambda `h .default p (mkApp (mkConst owner) (.bvar 0)))
  let witness := mkConst ``Subst.witness
  let carrier := mkApp (mkConst `Subst.asProp) witness
  env ← Subst.define env `Subst.proposition (mkSort 0) carrier
  let prop := mkConst `Subst.proposition
  env ← Subst.define env `Subst.observe
    (mkForall `proof .default prop bool)
    (mkLambda `proof .default prop (mkProj owner 0 (.bvar 0)))
  let ctor := mkApp (mkConst (.str owner "mk")) witness
  let falseBit := mkConst ``Bool.false
  let trueBit := mkConst ``Bool.true
  env ← Subst.define env `Subst.falseProof prop (mkApp ctor falseBit)
  env ← Subst.define env `Subst.trueProof prop (mkApp ctor trueBit)
  let refl (bit : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) bool bit
  env ← Subst.checked env (.thmDecl {
    name := `inconsistent, levelParams := [], type := mkConst ``False,
    value := mkAppN (mkConst ``Subst.observedProofsFalse)
      #[prop, mkConst `Subst.observe,
        mkConst `Subst.falseProof, mkConst `Subst.trueProof,
        refl falseBit, refl trueBit] })
  setEnv env
  logInfo "Kernel accepted `inconsistent : False` from a stuck sort after substitution."

/-- info: 'inconsistent' does not depend on any axioms -/
#guard_msgs in #print axioms inconsistent

example : False := inconsistent
