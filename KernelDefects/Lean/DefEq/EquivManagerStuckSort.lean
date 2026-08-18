/-
KERNEL DEFECT — an axiom-free `False`, live on every released toolchain.

The second exploit of lean4#14806, and the one that also needs lean4#14807.
Same non-transitive triple as EquivManagerMissingIH.lean, same hash-gated
union-find, but the consequence is different: instead of a malformed recursor,
the order-dependent comparison decides a RESULT SORT.

`Native64ResultSortGate` is a K-like inductive predicate whose recursor is used
as the result sort of the family `Native64ResultSortOwner`, so the sort
`Gate.rec x … Prop requested h` reduces to `Prop` only when the requested indices
are definitionally equal to `Gate.intro`'s.  Hence `Owner x h` is a proposition
in one context and a stuck sort in another:

  * `Native64ResultSort.asProp` is checked against a CONSTANT standing for
    `∀ x h, Prop`, which makes the kernel introduce `_kernel_fresh.0` for `x`.
    The hashes collide there, the union-find answers `true`, `Owner x h : Prop`
    is accepted, and `Native64ResultSortLeak.proposition` is a `Prop` for every
    later declaration — including for proof irrelevance.

  * `Native64ResultSortLeak.observe` projects field 0 out of that proposition.
    There the sort of the CLOSED term `Owner false closedGate` is needed, and
    that one is stuck.  `type_checker::is_prop` computed `whnf(infer_type(e))`
    and answered "not a proposition" for a type that does not reduce to a sort,
    rather than rejecting the term — so `infer_proj` skipped its proof-
    irrelevance guard and let the hidden `Bool` field out.

Proof irrelevance then identifies two `Owner.mk` applications carrying different
`Bool` fields, and observing them gives `False`.  `#print axioms` reports
NOTHING.

Two upstream fixes are needed to close it, and no released toolchain has either:
lean4#14806 (order-independent def-eq cache, `master` 2026-08-17) removes step
one, lean4#14807 (`is_prop` uses `ensure_sort`, `master` 2026-08-18) removes
step two.  The same projection reached WITHOUT any help from the cache is
SubstStuckSort.lean.

Verified accepted here on v4.33.0 and v4.34.0-rc1.  Needs v4.33.0 or later to
ELABORATE: `addDeclCore` gained a `maxRecDepth` parameter there.  Upstream's
version evidence for v4.28.0 / v4.29.1 / nightly-2026-08-01 comes from the
version-independent arena export path.

Control: ../Controls/DefEqCollisionControl.lean.

Source: adapted from `tests/elab/kernel_is_def_eq_equiv_manager_2.lean` in
lean4#14806; arena test `proj-of-stuck-prop`.  Write-up:
../../../Reports/2026-08-18-defeq-cache-and-stuck-sort.md.
-/
import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace RecClass

def rcStep (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def rcRun (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => rcStep x m) h

opaque rcOpaque : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def rcA (x : Bool) := rcRun x 1 rcOpaque
def rcB (x : Bool) := rcRun x 1 (Acc.intro 1 fun _ => Acc.inv rcOpaque)
def rcC (x : Bool) := rcRun x 0 (Acc.inv rcOpaque (Nat.lt_succ_self 0))

theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : rcRun x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [rcRun, rcStep] using ih n (Nat.lt_succ_self n)

theorem a_eq (x : Bool) : rcA x = x := run_eq x _ _
theorem b_eq (x : Bool) : rcB x = x := run_eq x _ _
theorem c_eq (x : Bool) : rcC x = x := run_eq x _ _

theorem transport (G : Bool → Bool → Bool → Bool → Prop)
    (a b c : Bool) (ab : a = b) (bc : b = c) (h : G c b a c) : G b a a a := by
  cases ab
  cases bc
  exact h

theorem observedProofsFalse (P : Prop) (observe : P → Bool) (p q : P)
    (onFalse : observe p = false) (onTrue : observe q = true) : False := by
  have same : p = q := proof_irrel p q
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg observe same).trans onTrue))

end RecClass

namespace Core64SortRepro

private def a : Name := .num (.num `Native64SortGateA 1) 2023879994
private def b : Name := .num (.num `Native64SortGateB 0) 3766726852
private def c : Name := .num (.num `Native64SortGateC 2) 1809645719
private def gate : Name := `Native64ResultSortGate
private def owner : Name := `Native64ResultSortOwner
private def bool := mkConst ``Bool

private def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 800000 10000 decl none with
  | .ok next => return next
  | .error _ => throwError "kernel error"

private def define (env : Environment) (name : Name) (type value : Expr) :
    CoreM Environment :=
  checked env (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe })

private def pad (salt : Nat) (e : Expr) : Expr :=
  mkApp (mkLambda `salt .default (mkConst ``Nat) (e.liftLooseBVars 0 1)) (mkNatLit salt)

private def values (x : Expr) : Array Expr :=
  let px := pad 125330 x
  let qx := pad 26537 (mkApp (mkLambda `z .default bool (.bvar 0)) x)
  #[mkApp (mkConst a) px, mkApp (mkConst b) px, mkApp (mkConst c) qx]

private def canonical (v : Array Expr) : Array Expr := #[v[2]!, v[1]!, v[0]!, v[2]!]
private def requested (v : Array Expr) : Array Expr := #[v[1]!, v[0]!, v[0]!, v[0]!]
private def gateType (x : Expr) : Expr :=
  mkAppN (mkConst gate) (#[x] ++ requested (values x))

private def gateDecl : Declaration :=
  let x := mkBVar 0
  let result := mkAppN (mkConst gate) (#[x] ++ canonical (values x))
  .inductDecl [] 1 [{
    name := gate
    type := (List.range 5).foldr (fun _ body => mkForall `bit .default bool body) (mkSort 0)
    ctors := [{name := .str gate "intro", type := mkForall `x .default bool result}]
  }] false

private def resultSort (x h : Expr) : Expr :=
  let majorType := mkAppN (mkConst gate)
    #[x.liftLooseBVars 0 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
  let motive := (List.range 4).foldr
    (fun _ body => mkLambda `index .default bool body)
    (mkLambda `proof .default majorType (mkSort 1))
  mkAppN (mkConst (.str gate "rec") [Level.succ Level.one])
    (#[x, motive, mkSort 0] ++ requested (values x) ++ #[h])

private def ownerDecl : Declaration :=
  let type := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) (resultSort (.bvar 1) (.bvar 0))
  let result := mkApp2 (mkConst owner) (.bvar 2) (.bvar 1)
  let ctorType := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) <| mkForall `bit .default bool result
  .inductDecl [] 2 [{
    name := owner, type
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false

private def symm (left right proof : Expr) : Expr :=
  mkAppN (mkConst ``Eq.symm [Level.one]) #[bool, left, right, proof]
private def trans (left middle right first second : Expr) : Expr :=
  mkAppN (mkConst ``Eq.trans [Level.one]) #[bool, left, middle, right, first, second]

private def closedWitness (x : Expr) : Expr :=
  let v := values x
  let av := v[0]!
  let bv := v[1]!
  let cv := v[2]!
  let ae := mkApp (mkConst ``RecClass.a_eq) av.appArg!
  let be := mkApp (mkConst ``RecClass.b_eq) bv.appArg!
  let ce := mkApp (mkConst ``RecClass.c_eq) cv.appArg!
  mkAppN (mkConst ``RecClass.transport)
    #[mkApp (mkConst gate) x, av, bv, cv,
      trans av x bv ae (symm bv x be),
      trans bv x cv be (symm cv x ce),
      mkApp (mkConst (.str gate "intro")) x]

/--
info: Kernel accepted `inconsistent : False` from a stuck result sort.
-/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  for (name, value) in [(a, ``RecClass.rcA), (b, ``RecClass.rcB), (c, ``RecClass.rcC)] do
    env ← checked env (.defnDecl {
      name, levelParams := [], type := mkForall `x .default bool bool,
      value := mkConst value, hints := .regular 1021, safety := .safe })
  env ← checked env gateDecl
  env ← checked env ownerDecl

  -- Check the generic `Prop` alias while its first local is `_kernel_fresh.0`.
  -- Hiding its function type behind a constant preserves that local numbering.
  let aliasType := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) (mkSort 0)
  let .ok aliasSort := Kernel.check env {} aliasType | throwError "invalid alias type"
  env ← define env `Native64ResultSort.asPropType aliasSort aliasType
  let body := mkApp2 (mkConst ``id [Level.one]) (mkSort 0)
    (mkApp2 (mkConst owner) (.bvar 1) (.bvar 0))
  let value := mkLambda `x .default bool <|
    mkLambda `h .default (gateType (.bvar 0)) body
  env ← define env `Native64ResultSort.asProp (mkConst `Native64ResultSort.asPropType) value

  let falseBit := mkConst ``Bool.false
  let trueBit := mkConst ``Bool.true
  env ← checked env (.opaqueDecl {
    name := `Native64ResultSort.closedGate, levelParams := [],
    type := gateType falseBit, value := closedWitness falseBit, isUnsafe := false })
  let h := mkConst `Native64ResultSort.closedGate
  let carrier := mkApp2 (mkConst `Native64ResultSort.asProp) falseBit h
  env ← define env `Native64ResultSortLeak.proposition (mkSort 0) carrier
  let prop := mkConst `Native64ResultSortLeak.proposition

  -- The proposition is genuine, but `infer_proj` treats its stuck inferred sort
  -- as permission to extract the constructor's hidden `Bool` field.
  env ← define env `Native64ResultSortLeak.observe
    (mkForall `p .default prop bool)
    (mkLambda `p .default prop (mkProj owner 0 (.bvar 0)))
  let ctor := mkApp2 (mkConst (.str owner "mk")) falseBit h
  env ← define env `Native64ResultSortLeak.falseProof prop (mkApp ctor falseBit)
  env ← define env `Native64ResultSortLeak.trueProof prop (mkApp ctor trueBit)
  let refl (bit : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) bool bit
  env ← checked env (.thmDecl {
    name := `inconsistent, levelParams := [], type := mkConst ``False,
    value := mkAppN (mkConst ``RecClass.observedProofsFalse)
      #[prop, mkConst `Native64ResultSortLeak.observe,
        mkConst `Native64ResultSortLeak.falseProof, mkConst `Native64ResultSortLeak.trueProof,
        refl falseBit, refl trueBit] })
  setEnv env
  logInfo "Kernel accepted `inconsistent : False` from a stuck result sort."

end Core64SortRepro

/-- info: 'inconsistent' does not depend on any axioms -/
#guard_msgs in #print axioms inconsistent

example : False := inconsistent
