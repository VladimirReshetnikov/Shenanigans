/-
CONTROL for the three exhibits in ../DefEq/ that prove `False` from the
non-transitive definitional-equality triple (lean4#14806 / lean4#14807).

Acceptance of an exhibit means something only if a deliberately-broken twin is
REJECTED by the same procedure on the same toolchain.  Each section below is the
corresponding exhibit with exactly one thing changed, and each asserts the
kernel's refusal with `#guard_msgs`.  All three must print `kernel error` — if
any of them silently succeeds, the exhibit next to it proves nothing.

  1. EquivManagerMissingIH  — pad salt 101831 → 101832, so the `Expr.hash`
     collision the union-find lookup is gated on no longer holds.  The kernel
     then reports the honest error about `Native64TwoHashOwner.step` having an
     invalid occurrence of the datatype being declared.

  2. EquivManagerStuckSort  — pad salt 125330 → 125331, same reason.

  3. SubstStuckSort         — the substituted proof is given type `P` rather
     than the definitionally-equal `Q`.  `gate` then K-reduces to `Prop`, the
     sort of `Owner hP` is a genuine sort, and `infer_proj`'s proof-irrelevance
     guard fires as it should.  ONE TOKEN separates this from the exhibit.

Run: elan run leanprover/lean4:v4.33.0 lean --trust=0 <this file>
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

end RecClass

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

private def boolTy := mkConst ``Bool

-- ===========================================================================
-- 1.  Missing-IH recursor, with the hash collision broken.
-- ===========================================================================

namespace Control1

private def a : Name := .num (.num `Native64TwoHashA 0) 572478232
private def b : Name := .num (.num `Native64TwoHashB 0) 2525080234
private def c : Name := .num (.num `Native64TwoHashC 0) 3119207123
private def gate : Name := `Control1Gate
private def owner : Name := `Control1Owner

-- The ONLY change from ../DefEq/EquivManagerMissingIH.lean: 101831 → 101832.
private def values (x : Expr) : Array Expr :=
  let px := pad 101832 x
  let qx := pad 47770 (mkApp (mkLambda `z .default boolTy (.bvar 0)) x)
  #[mkApp (mkConst a) px, mkApp (mkConst b) px, mkApp (mkConst c) qx]

private def canonical (v : Array Expr) : Array Expr := #[v[2]!, v[1]!, v[0]!, v[2]!]
private def requested (v : Array Expr) : Array Expr := #[v[1]!, v[0]!, v[0]!, v[0]!]

private def gateCall (x : Expr) (args : Array Expr) (major result : Expr) : Expr :=
  let majorType := mkAppN (mkConst gate)
    #[x.liftLooseBVars 0 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
  let motive := (List.range 4).foldr
    (fun _ body => mkLambda `index .default boolTy body)
    (mkLambda `proof .default majorType (mkSort 1))
  mkAppN (mkConst (.str gate "rec") [Level.succ Level.one])
    (#[x, motive, result] ++ args ++ #[major])

private def gateDecl : Declaration :=
  let x := mkBVar 0
  let result := mkAppN (mkConst gate) (#[x] ++ canonical (values x))
  .inductDecl [] 1 [{
    name := gate
    type := (List.range 5).foldr (fun _ body => mkForall `bit .default boolTy body) (mkSort 0)
    ctors := [{name := .str gate "intro", type := mkForall `x .default boolTy result}]
  }] false

private def ownerDecl : Declaration :=
  let self := mkConst owner
  let x := mkBVar 0
  let proofType := mkAppN (mkConst gate) (#[x] ++ requested (values x))
  let x := mkBVar 1
  let childType := gateCall x (requested (values x)) (.bvar 0) self
  .inductDecl [] 0 [{
    name := owner, type := mkSort 1
    ctors := [{name := .str owner "base", type := self},
      {name := .str owner "step", type := mkForall `x .default boolTy <|
        mkForall `h .default proofType <| mkForall `child .default childType self}]
  }] false

/-- error: kernel error -/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  for (name, value) in [(a, ``RecClass.rcA), (b, ``RecClass.rcB), (c, ``RecClass.rcC)] do
    env ← checked env (.defnDecl {
      name, levelParams := [], type := mkForall `x .default boolTy boolTy,
      value := mkConst value, hints := .regular 1021, safety := .safe})
  for i in [3, 9] do
    let v := values (.fvar ⟨.num `_ind_fresh i⟩)
    unless v[0]!.hash != v[2]!.hash do
      throwError "control is not a control: the hashes still collide at {i}"
  env ← checked env gateDecl
  env ← checked env ownerDecl
  setEnv env
  logInfo "CONTROL FAILED: the owner declaration was accepted without a collision."

end Control1

-- ===========================================================================
-- 2.  Stuck result sort, with the hash collision broken.
-- ===========================================================================

namespace Control2

private def a : Name := .num (.num `Native64SortGateA 1) 2023879994
private def b : Name := .num (.num `Native64SortGateB 0) 3766726852
private def c : Name := .num (.num `Native64SortGateC 2) 1809645719
private def gate : Name := `Control2Gate
private def owner : Name := `Control2Owner

-- The ONLY change from ../DefEq/EquivManagerStuckSort.lean: 125330 → 125331.
private def values (x : Expr) : Array Expr :=
  let px := pad 125331 x
  let qx := pad 26537 (mkApp (mkLambda `z .default boolTy (.bvar 0)) x)
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
    type := (List.range 5).foldr (fun _ body => mkForall `bit .default boolTy body) (mkSort 0)
    ctors := [{name := .str gate "intro", type := mkForall `x .default boolTy result}]
  }] false

private def resultSort (x h : Expr) : Expr :=
  let majorType := mkAppN (mkConst gate)
    #[x.liftLooseBVars 0 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
  let motive := (List.range 4).foldr
    (fun _ body => mkLambda `index .default boolTy body)
    (mkLambda `proof .default majorType (mkSort 1))
  mkAppN (mkConst (.str gate "rec") [Level.succ Level.one])
    (#[x, motive, mkSort 0] ++ requested (values x) ++ #[h])

private def ownerDecl : Declaration :=
  let type := mkForall `x .default boolTy <|
    mkForall `h .default (gateType (.bvar 0)) (resultSort (.bvar 1) (.bvar 0))
  let result := mkApp2 (mkConst owner) (.bvar 2) (.bvar 1)
  let ctorType := mkForall `x .default boolTy <|
    mkForall `h .default (gateType (.bvar 0)) <| mkForall `bit .default boolTy result
  .inductDecl [] 2 [{
    name := owner, type
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false

/-- error: kernel error -/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  for (name, value) in [(a, ``RecClass.rcA), (b, ``RecClass.rcB), (c, ``RecClass.rcC)] do
    env ← checked env (.defnDecl {
      name, levelParams := [], type := mkForall `x .default boolTy boolTy,
      value := mkConst value, hints := .regular 1021, safety := .safe })
  unless (values (.fvar ⟨.num `_kernel_fresh 0⟩))[0]!.hash
       != (values (.fvar ⟨.num `_kernel_fresh 0⟩))[2]!.hash do
    throwError "control is not a control: the hashes still collide"
  env ← checked env gateDecl
  env ← checked env ownerDecl
  setEnv env
  logInfo "CONTROL FAILED: the owner declaration was accepted without a collision."

end Control2

-- ===========================================================================
-- 3.  The substitution route, with the substituted proof at type `P`.
--     No cache is involved either way; this is the one-token control.
-- ===========================================================================

namespace Control3

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

-- The exhibit's witness is `opaque witness : Q`.  Here it is `P` — the
-- definitionally equal type on whose proofs `gate` actually reduces.
opaque witness : P := (run_eq false _ _).trans (run_eq false _ _).symm

def gate (h : P) : Type :=
  Eq.rec (motive := fun _ _ => Type) Prop h

end Control3

/-- error: kernel error -/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  let owner := `Control3.Owner
  let p := mkConst ``Control3.P
  let gate := mkConst ``Control3.gate
  let ownerType := mkForall `h .default p (mkApp gate (.bvar 0))
  let ctorType := mkForall `h .default p <|
    mkForall `bit .default boolTy (mkApp (mkConst owner) (.bvar 1))
  env ← checked env (.inductDecl [] 1 [{
    name := owner, type := ownerType,
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false)
  env ← define env `Control3.asProp
    (mkForall `h .default p (mkSort 0))
    (mkLambda `h .default p (mkApp (mkConst owner) (.bvar 0)))
  let carrier := mkApp (mkConst `Control3.asProp) (mkConst ``Control3.witness)
  env ← define env `Control3.proposition (mkSort 0) carrier
  let prop := mkConst `Control3.proposition
  -- Here the sort of `Owner witness` really does reduce, so `is_prop` says yes
  -- and `infer_proj` refuses to hand out the `Bool` field.
  env ← define env `Control3.observe
    (mkForall `proof .default prop boolTy)
    (mkLambda `proof .default prop (mkProj owner 0 (.bvar 0)))
  setEnv env
  logInfo "CONTROL FAILED: the projection out of a genuine proposition was accepted."
