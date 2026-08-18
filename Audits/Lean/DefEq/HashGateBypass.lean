/-
Category (see ../../../README.md): **audit**.  No proof of `False` is produced
here.  What is measured refutes a claim that this repository, upstream's own
pull request, and the Lean Kernel Arena's test descriptions all state as fact.

THE CLAIM, as everyone has it.  lean4#14806's order-dependent `is_def_eq` is
gated on an `Expr.hash` collision.  `equiv_manager::is_equiv_core` opens with

    if (is_eqp(a, b))                      return true;
    if (m_use_hash && hash(a) != hash(b))  return false;   // skips the union-find

and every account of the bug — upstream's PR body, the arena's `rec-missing-ih`,
`proj-of-stuck-prop` and `proj-of-subst-prop` descriptions, this repository's
../../../Reports/2026-07-29-defeq-history-dependence.md ("same three, no hash
collision → rejected (collision essential)") and its
../../../Reports/2026-08-18-defeq-cache-and-stuck-sort.md — presents the
collision as the thing that normally hides the transitive closure, and the
engineered collision as what makes an exploit possible.

THE MEASUREMENT.  It is not gated, at two of the three call sites.

    kernel/type_checker.h:83
      lbool quick_is_def_eq(expr const & t, expr const & s, bool use_hash = false);

    kernel/type_checker.cpp:1090   quick_is_def_eq(t, s, use_hash);   // use_hash = true
    kernel/type_checker.cpp:1114   quick_is_def_eq(t_n, s_n);         // DEFAULT: false
    kernel/type_checker.cpp:965    quick_is_def_eq(t_n, s_n);         // DEFAULT: false

`equiv_manager::is_equiv(e1, e2, use_hash = false)` assigns `m_use_hash` from
that argument, so at :1114 and :965 the hash comparison in `is_equiv_core` is
skipped entirely and the union-find is consulted for ANY pair.  :1114 is reached
whenever `whnf_core` changed either side; :965 is reached from
`lazy_delta_reduction_step`, i.e. after the two sides have been unfolded.

SCOPE OF THE CLAIM.  What is measured below is the BEHAVIOUR — the closure is
consulted for a pair whose hashes differ — together with the two source facts
above, which are quoted from the v4.33.0 tree.  Which of the two ungated sites
actually fires for a given query is NOT measured here; that needs an
instrumented build.  The behavioural claim does not depend on knowing which.

So the order-dependence needs no birthday search, no salt and no padding — only
the non-transitive triple, and for the three comparisons to happen inside one
declaration check.  The exhibits in ../../../KernelDefects/Lean/DefEq/ inherit
their salts and paddings from upstream's regression tests; this file shows the
paddings are not load-bearing for the *mechanism*, whatever else they do in
those particular exploits.

WHAT THIS IS NOT.  It is not a new route to `False`, and it does not by itself
make upstream's exploits collision-free: those use the collision for a SECOND
purpose, selectivity — `rec-missing-ih` needs the closure visible while the
recursor's minor premises are built and invisible while its rules are.  Removing
the gate makes it visible everywhere, which is the opposite of selective.  It is a reachability
result about lean4#14806, which is fixed on `master` and live on every released
toolchain including v4.33.0 and v4.34.0-rc1.  Its value is that it lowers the
stated bar for that bug from "engineer a 32-bit collision" to "write three
ordinary comparisons in one declaration", and that the three write-ups above are
wrong on the point.

Run: elan run leanprover/lean4:v4.33.0 lean --trust=0 <this file>
-/
import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## The non-transitive triple, from lean4#14806's regression tests -/

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

end RecClass

/-- Lifts the `Bool` triple to a triple of closed TYPES, so the comparisons the
    kernel makes are between types rather than between data. -/
def Vec : Bool → Type := fun b => cond b Nat Bool

/-- Forces a definitional-equality query on a `Type` and, on success, merges the
    two into `equiv_manager`. -/
inductive TagT : Type → Type 1 where
  | mk : (t : Type) → TagT t

namespace HashGate

def falseBit := mkConst ``Bool.false

def vecOf (c : Name) : Expr := mkApp (mkConst ``Vec) (mkApp (mkConst c) falseBit)

/-- `(fun _ : Nat => e) salt`: same meaning, different `Expr.hash`. -/
def pad (salt : Nat) (e : Expr) : Expr :=
  mkApp (mkLambda `s .default (mkConst ``Nat) (e.liftLooseBVars 0 1)) (mkNatLit salt)

def vecPadded (c : Name) (salt : Nat) : Expr :=
  mkApp (mkConst ``Vec) (pad salt (mkApp (mkConst c) falseBit))

/-- `let w : TagT y := TagT.mk x; body` — accepted iff the kernel accepts `x ≡ y`. -/
def prime (x y body : Expr) : Expr :=
  .letE `w (mkApp (mkConst ``TagT) y) (mkApp (mkConst ``TagT.mk) x) body false

def unit := mkConst ``Unit.unit

def accepts (env : Environment) (e : Expr) : Bool :=
  match Kernel.check env {} e with
  | .ok _ => true
  | .error _ => false

/-- Substring test, spelled without `|>` so the `unless` guards parse. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

def defeq (env : Environment) (a b : Expr) : Bool :=
  match Kernel.isDefEq env {} a b with
  | .ok r => r
  | .error _ => false

end HashGate

open HashGate

/--
info: unpadded: hashes differ (collision NOT engineered)
isolated: A≡B true, B≡C true, A≡C FALSE
one type_checker, A~B then B~C then A-at-C: ACCEPTED
three type_checkers, the third alone: rejected
padded, deliberately non-colliding hashes: ACCEPTED
containment: a SEPARATE addDecl rejects — closure is per-declaration
-/
#guard_msgs in
run_meta do
  let env ← getEnv

  -- ---------------------------------------------------------------- unpadded
  let A := vecOf ``RecClass.rcA
  let B := vecOf ``RecClass.rcB
  let C := vecOf ``RecClass.rcC
  if A.hash == C.hash then
    throwError "the unpadded pair collides by accident; this file measures nothing"

  unless defeq env A B do throwError "A ≡ B failed; the triple has changed"
  unless defeq env B C do throwError "B ≡ C failed; the triple has changed"
  if defeq env A C then
    throwError "A ≡ C in ISOLATION; the triple is no longer non-transitive"

  -- One declaration = one type_checker = one equiv_manager.  The first two
  -- ascriptions merge A~B and B~C; the third asks the question that fails on
  -- its own.  No collision anywhere.
  unless accepts env (prime A B (prime B C (prime A C unit))) do
    throwError "primed chain was REJECTED — the closure was not consulted"

  -- The same third ascription, alone, in its own type_checker.
  if accepts env (prime A C unit) then
    throwError "the bare ascription was accepted; the control is vacuous"

  -- ------------------------------------------------------------------ padded
  -- Upstream's exploits pad their terms.  Padding with deliberately
  -- NON-colliding salts changes nothing: the closure is still consulted.
  let Ap := vecPadded ``RecClass.rcA 135601
  let Bp := vecPadded ``RecClass.rcB 0
  let Cp := vecPadded ``RecClass.rcC 253
  if Ap.hash == Cp.hash then
    throwError "chose a colliding salt pair by accident"
  unless accepts env (prime Ap Bp (prime Bp Cp (prime Ap Cp unit))) do
    throwError "padded non-colliding chain was rejected"

  -- ------------------------------------------------------------ containment
  -- The bound on all of this: `equiv_manager` lives in the type_checker state,
  -- and a separate `addDecl` gets a fresh one.  Priming in one declaration does
  -- NOT carry into the next, so the order dependence is confined to a single
  -- declaration check.  That is what #14806's analysis says, and it is worth
  -- measuring rather than assuming.
  let mkDef (n : Name) (v : Expr) : Declaration :=
    .defnDecl { name := n, levelParams := [], type := mkConst ``Unit,
                value := v, hints := .abbrev, safety := .safe }
  let .ok env1 := env.addDeclCore 4000000 10000 (mkDef `HGPrime (prime A B (prime B C unit))) none
    | throwError "the priming declaration was rejected"
  match env1.addDeclCore 4000000 10000 (mkDef `HGVictim (prime A C unit)) none with
  | .ok _ => throwError "closure PERSISTED across declarations — worse than documented"
  | .error _ => pure ()

  logInfo "unpadded: hashes differ (collision NOT engineered)\n\
           isolated: A≡B true, B≡C true, A≡C FALSE\n\
           one type_checker, A~B then B~C then A-at-C: ACCEPTED\n\
           three type_checkers, the third alone: rejected\n\
           padded, deliberately non-colliding hashes: ACCEPTED\n\
           containment: a SEPARATE addDecl rejects — closure is per-declaration"

/-! ## The secondary measurement: how close this gets to a stored ill-typed constructor

    `check_constructors` (inductive.cpp) type-checks the whole constructor type
    at :426 and then walks its telescope, comparing each of the first `nparams`
    binder types against the inductive's parameters at :430.

    With the priming lets sitting in the constructor's later binder types, the
    check at :426 ACCEPTS a constructor whose result `PE p` applies `PE : Vec
    (rcA false) → Type` to a `p : Vec (rcC false)` — a term a fresh kernel
    rejects.  What stops the declaration is the *second*, redundant comparison
    at :430, which asks the same question outside the primed context and gets
    the honest answer.

    That is worth recording in both directions.  The kernel does type-check a
    constructor type it should refuse; and the parameter check, which reads like
    a well-formedness formality, is load-bearing as a backstop against the
    def-eq order dependence. -/

/--
info: control  dies at inductive.cpp:426 — application type mismatch
exhibit  dies at inductive.cpp:430 — parameter check, having PASSED :426
-/
#guard_msgs in
run_meta do
  let env ← getEnv
  let A := vecOf ``RecClass.rcA
  let B := vecOf ``RecClass.rcB
  let C := vecOf ``RecClass.rcC
  let unitTy := mkConst ``Unit

  let mk (n : Name) (ctorType : Expr) : Declaration :=
    .inductDecl [] 1 [{
      name := n, type := mkForall `p .default A (mkSort 1)
      ctors := [{ name := .str n "mk", type := ctorType }] }] false

  let err (d : Declaration) : CoreM String := do
    match env.addDeclCore 4000000 10000 d none with
    | .ok _ => return "ACCEPTED"
    | .error e => return (← (e.toMessageData {}).toString)

  let ctl ← err (mk `HGControl (mkForall `p .default C (mkApp (mkConst `HGControl) (.bvar 0))))
  unless hasSub ctl "application type mismatch" do
    throwError "control did not fail at the application: {ctl}"

  let tele :=
    mkForall `p .default C <|
      mkForall `w1 .default (prime A B unitTy) <|
        mkForall `w2 .default (prime B C unitTy) <|
          mkApp (mkConst `HGExhibit) (.bvar 2)
  let exh ← err (mk `HGExhibit tele)
  unless hasSub exh "does not match inductive datatypes parameters" do
    throwError "exhibit did not reach the parameter check: {exh}"

  logInfo "control  dies at inductive.cpp:426 — application type mismatch\n\
           exhibit  dies at inductive.cpp:430 — parameter check, having PASSED :426"
