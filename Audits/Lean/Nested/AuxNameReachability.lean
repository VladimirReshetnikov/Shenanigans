import Lean
/-!
AUDIT: how far can a declaration reach into the kernel's transient `_nested`
auxiliary environment?  (lean4#14616, `master`-only fix, live on every release.)

CONTEXT.  When the kernel eliminates a nested inductive it builds auxiliary types
under the reserved prefix `_nested` in a *temporary* environment, checks the
declaration there, and then `restore_nested` rewrites those names back to the real
nested occurrences.  A declaration that names one of those auxiliaries is therefore
**checked against one type and stored with another**.
[lean4#14616](https://github.com/leanprover/lean4/pull/14616) closes this on
`master` with `check_no_nested_aux`, which rejects the prefix in both `Expr.const`
names and `Expr.proj` structure names.  No released toolchain has that check, and
the postmortem records that the construction **cannot be captured as an arena export
test** because it turns on transient `equiv_manager` state — so no reproduction
exists anywhere.

QUESTION.  Is the divergence reachable from a *safe* declaration on a released
kernel?

ANSWER: not by any of the four levers below.  The divergence is real and §5
demonstrates it — a field checked as a `Prop` is stored as a `Sort u` — but the
only path that reaches it also sets `isUnsafe`, and the safety firewall then
refuses every safe use.  On the safe path `check_positivity` closes it, because
`is_valid_ind_app` compares the occurrence against `m_ind_cnsts[i]` with
**expression** equality, and that covers the universe levels.

Run with plain `lean AuxNameReachability.lean`.
-/
open Lean Elab Command Meta

private def u : Level := .param `u
private def one : Level := .succ .zero

/- Host: `Wrap.{v} (α : Sort v) : Sort v | mk : α → Wrap α`.  The frontend rejects
this ("resulting universe may be `Prop` for some parameter values"), but it is a
legitimate kernel-level inductive — see `../Metatheory/ProjBeyondRecursor.lean`. -/
run_cmd liftCoreM (addDecl (.inductDecl [`u] 1
  [{ name := `Wrap, type := .forallE `a (.sort u) (.sort u) .default
     ctors := [{ name := `Wrap.mk
                 type := .forallE `a (.sort u)
                          (.forallE `x (.bvar 0) (.app (.const `Wrap [u]) (.bvar 1)) .default)
                          .default }] }] false))

private def attempt (tag : String) (d : Declaration) : MetaM Unit := do
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .error e => logInfo m!"rejected  {tag}{Format.line}          {← (e.toMessageData {}).toString}"
  | .ok kenv =>
    match kenv.find? `B.node with
    | some ci => logInfo m!"ACCEPTED  {tag}  (isUnsafe = {ci.isUnsafe}){Format.line}          STORED B.node : {ci.type}"
    | none    => logInfo m!"ACCEPTED  {tag}  (no B.node?)"

/-! ### 1. The auxiliary name is predictable

`mk_unique_name(*g_nested + J_name)` (inductive.cpp:1014, :910) appends `_1`, `_2`,
… until the name is free in the *original* environment.  So the first auxiliary for
a nested `Wrap` is exactly `_nested.Wrap_1`, and a declaration may name it. -/

private def mkNamed (auxName : Name) : Declaration :=
  .inductDecl [`u] 1
    [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
       ctors := [{ name := `B.node
                   type := .forallE `n (.const `Nat [])
                            (.forallE `w1 (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                              (.forallE `w2 (.app (.const auxName [u]) (.bvar 1))
                                (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] false

run_cmd liftTermElabM do
  logInfo "== 1. which spelling of the auxiliary name resolves? =="
  for nm in [`_nested.Wrap_1, `_nested.Wrap1, `_nested.Wrap, `_nested.Wrap_2] do
    attempt s!"aux named {nm}" (mkNamed nm)

/-! ### 2. Lever one — the level argument

The auxiliary carries the *block's* universe parameters, and `restore_nested`
discards its levels entirely: the replacement is built from the real occurrence.
So a different level ought to give a checked/stored mismatch.  It does not get
that far — `check_positivity` → `is_valid_ind_app` tests `I != m_ind_cnsts[i]`,
and `expr` equality on a constant covers its levels. -/

private def mkLevel (lv : Level) (uns : Bool) : Declaration :=
  .inductDecl [`u] 1
    [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
       ctors := [{ name := `B.node
                   type := .forallE `n (.const `Nat [])
                            (.forallE `w1 (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                              (.forallE `w2 (.app (.const `_nested.Wrap_1 [lv]) (.bvar 1))
                                (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] uns

run_cmd liftTermElabM do
  logInfo "== 2. level swap, safe =="
  attempt "honest .{u}" (mkLevel u false)
  attempt "swap .{0}"   (mkLevel Level.zero false)
  attempt "swap .{1}"   (mkLevel one false)

/-! ### 3. Lever two — the parameter arguments

`restore_nested` drops the first `m_params.size()` arguments of the auxiliary
application and substitutes the constructor's own re-created parameters, so
anything else written there is silently replaced.  Also closed by
`is_valid_ind_app`, which requires `m_params[i] == args[i]`. -/

private def mkArg (arg : Expr) : Declaration :=
  .inductDecl [`u] 1
    [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
       ctors := [{ name := `B.node
                   type := .forallE `n (.const `Nat [])
                            (.forallE `w1 (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                              (.forallE `w2 (.app (.const `_nested.Wrap_1 [u]) arg)
                                (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] false

run_cmd liftTermElabM do
  logInfo "== 3. parameter swap =="
  attempt "honest arg (the block parameter)" (mkArg (.bvar 1))
  attempt "swapped arg (a literal)"          (mkArg (mkNatLit 7))

/-! ### 4. Lever three — `Expr.proj` naming the auxiliary

The `master` fix covers projections separately, because the kernel rewrites the
nested occurrence in the constructor to the auxiliary type, so a projection can
reach it without the declaration ever naming it as a constant.  On a released
kernel this is closed by *ordering* instead: `add_inductive_fn` runs
`declare_inductive_types()`, then `check_constructors()`, then
`declare_constructors()` — so while a constructor is being checked the auxiliary
*type* exists but its *constructor* does not, and `infer_proj` cannot find it.
The control shows the rewrite really did happen. -/

private def mkProj (projName : Name) : Declaration :=
  .inductDecl [`u] 1
    [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
       ctors := [{ name := `B.node
                   type := .forallE `n (.const `Nat [])
                            (.forallE `w (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                              (.forallE `p (.app (.const `B [u]) (.proj projName 0 (.bvar 0)))
                                (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] false

run_cmd liftTermElabM do
  logInfo "== 4. Expr.proj naming the auxiliary =="
  attempt "proj sname = _nested.Wrap_1" (mkProj `_nested.Wrap_1)
  attempt "proj sname = Wrap  (control)" (mkProj `Wrap)

/-! ### 5. Lever four — `isUnsafe`, which skips positivity

`check_constructors` guards `check_positivity` with `if (!m_is_unsafe)`.  Setting
the flag removes the only gate closing section 2, and the divergence appears: the
field is **checked** as `_nested.Wrap_1.{0} n`, whose type is `Prop`, and
**stored** as `Wrap (@B n)`, whose type is `Sort u`.  That is exactly the "stored
constructor type that is ill typed" of #14616, reproduced on a released kernel —
and it is also what lean4#14621's re-check would catch.

It does not escape: the declaration is `unsafe`, and `infer_constant`'s safety gate
refuses every safe declaration mentioning it.  The universe bound in
`check_constructors` is *not* guarded by the unsafe flag, which is why `.{1}` still
fails. -/

run_cmd liftTermElabM do
  logInfo "== 5. unsafe, which skips positivity =="
  attempt "UNSAFE .{u} (honest)"   (mkLevel u true)
  attempt "UNSAFE .{0} (DIVERGES)" (mkLevel Level.zero true)
  attempt "UNSAFE .{1}"            (mkLevel one true)
  logInfo "-- and whether a safe declaration can then use it --"
  match (← getEnv).toKernelEnv.addDecl {} (mkLevel Level.zero true) with
  | .error _ => logInfo "   (the unsafe declaration was rejected, nothing to test)"
  | .ok kenv =>
    let d : Declaration := .defnDecl { name := `UseIt, levelParams := [], hints := .abbrev,
                                       safety := .safe, type := .sort .zero,
                                       value := .app (.const `B [.zero]) (mkNatLit 0) }
    match kenv.addDecl {} d with
    | .ok _    => logError "   *** a SAFE definition CAN reference it — that would be a hole ***"
    | .error e => logInfo m!"   safe use rejected: {← (e.toMessageData {}).toString}"

/-
Expected on every released toolchain through v4.33.0-rc1 (see ../../../CATALOG.md 5.2):

  1. only `_nested.Wrap_1` resolves; the other three spellings are unknown constants.
     It is ACCEPTED, and the stored constructor is the honest one.
  2. `.{u}` accepted; `.{0}` rejected by positivity ("non valid occurrence"),
     `.{1}` rejected by the universe bound.
  3. the honest argument accepted; a literal rejected by positivity.
  4. `_nested.Wrap_1` rejected with "unknown constant '_nested.Wrap_1.mk'" — the
     auxiliary's constructor is not declared yet.  The `Wrap` control is rejected
     with "invalid projection", which proves the rewrite happened.
  5. `.{u}` and `.{0}` accepted as unsafe, and `.{0}` STORES `Wrap (@B n)` for a
     field CHECKED as `_nested.Wrap_1.{0} n : Prop`.  `.{1}` still rejected.
     Every safe use refused with "it uses unsafe declaration 'B'".

On `master` all of 1-5 are rejected up front with
  "invalid declaration 'B.node', it uses the reserved prefix '_nested'".
-/
