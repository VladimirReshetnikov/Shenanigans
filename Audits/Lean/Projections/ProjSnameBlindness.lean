import Lean
/-!
ANOMALY (no `False`).  On every released toolchain the kernel is blind to a
projection's structure name in **three** places at once, and this file measures
what each of them actually does.  Two of the three are the primitives
lean4#14616's own commit message says its exploit is built from.

THE THREE SITES, all present on `v4.32.2` and all fixed on `master` only:

  (1) `reduce_proj_core(expr c, unsigned idx)` — type_checker.cpp:359.
      No structure-name parameter at all, so it reduces a projection using the
      constructor it finds, whatever inductive that constructor belongs to.
      lean4#14632 added `name const & sname` and
      `if (mk_val.get_induct() != sname) return none_expr();`.

  (2) `is_def_eq_core` — type_checker.cpp:1101:
          if (is_proj(t_n) && is_proj(s_n) && proj_idx(t_n) == proj_idx(s_n))
      Only the index is compared.  lean4#14631 inserted
      `proj_sname(t_n) == proj_sname(s_n) &&` (master:1132).

  (3) `equiv_manager::is_equiv_core` — equiv_manager.cpp:102:
          result = is_equiv_core(proj_expr(a), proj_expr(b)) && proj_idx(a) == proj_idx(b);
      The union-find that caches def-eq, likewise blind.  lean4#14631 again.

CATALOG.md §2.5 records upstream's reason for calling (2)/(3) unexploitable:
*"`infer_proj` rejects a structure name disagreeing with the projected
expression's type, and kernel-built projections always carry the right one, so
two projections reaching def-eq can differ on the name only if one is
ill-typed."*  That is correct, and §2 below is the measurement that shows the
premise really is what holds the line — the blindness itself is total.

WHY IT IS STILL NOT A ROUTE TO `False`.  The precondition is an ill-typed
projection, and on a released kernel there is nowhere to put one:

  * `infer_proj` (type_checker.cpp:221ff, the throw at :231) tests
    `I_name != proj_sname(e)` against the head of
    `whnf(infer_type(proj_expr(e)))` and throws.  Every projection in a *checked*
    term therefore carries the right name.

    But that guard has a precise coverage limit, and §4 measures it.
    `infer_app` (type_checker.cpp:163) infers its argument **only** when
    `infer_only` is false:

        } else {                                   // infer_only == true
            expr const & f = get_app_args(e, args);
            expr f_type    = infer_type_core(f, true);
            for (...) { /* walks f_type's binders; args are never inferred */ }

    and `whnf` infers types in `infer_only` mode.  So the line holds for every
    subterm of a declaration being checked, and does not run at all on a subterm
    reached only through reduction.  That is why a supplier of *stored*
    ill-typedness is the precondition: it is the one way a projection gets into a
    position the guard never visits.
  * Within a *checked* `addDecl`, the one place a released kernel stores a term
    it never checks is the output of `restore_nested` (that is what lean4#14621 added a re-check for, and what
    [`../Nested/IllTypedStoredConstructor.lean`](../Nested/IllTypedStoredConstructor.lean)
    exploits).  A projection naming a transient `_nested` auxiliary type is
    exactly the shape that would land there — and it is why master's
    `check_no_nested_aux` covers `is_proj` separately from `Expr.const`.  But it
    cannot be *written*: `add_inductive_fn` runs `declare_inductive_types()`,
    then `check_constructors()`, then `declare_constructors()`, so while a
    constructor is being checked the auxiliary *type* exists and its
    *constructor* does not, and `infer_proj` reports
    `unknown constant '_nested.Wrap_1.mk'`.  Measured in
    [`../Nested/AuxNameReachability.lean`](../Nested/AuxNameReachability.lean) §4.

So the three blind sites and the one place that stores unchecked terms are
separated by declaration ordering, and the guard between them runs only in
`infer_only = false` mode.  That is a thinner margin than it looks — ordering is
not a soundness check, and "we always infer this" is a property of one traversal
mode rather than of the kernel — which is the reason lean4#14621's re-check
matters on the release line.

Run with plain `lean --trust=0 ProjSnameBlindness.lean`.
-/
open Lean Elab Command Meta

structure S where
  a : Nat
  b : Bool

/-- Same shape as `S`, different name — so a cross-projection is type-correct at
the field level even though the structures are unrelated. -/
structure T where
  x : Bool
  y : Nat

private def report (tag : String) (e : Expr) : MetaM Unit := do
  match Lean.Kernel.whnf (← getEnv) {} e with
  | .ok r    => logInfo m!"  {tag}\n      whnf = {r}"
  | .error x => logInfo m!"  {tag}\n      error: {← (x.toMessageData {}).toString}"

private def deq (tag : String) (a b : Expr) : MetaM Unit := do
  match Lean.Kernel.isDefEq (← getEnv) (← getLCtx) a b with
  | .ok r    => logInfo m!"  {tag}  isDefEq = {r}"
  | .error x => logInfo m!"  {tag}  error: {← (x.toMessageData {}).toString}"

run_cmd liftTermElabM do
  let smk := mkApp2 (.const `S.mk []) (mkNatLit 5) (.const `Bool.true [])

  logInfo "== 1. reduce_proj_core ignores the structure name =="
  report "proj S 0 (S.mk 5 true)   honest, S.a : Nat" (.proj `S 0 smk)
  report "proj S 1 (S.mk 5 true)   honest, S.b : Bool" (.proj `S 1 smk)
  report "proj T 0 (S.mk 5 true)   WRONG name; T.x : Bool, yet:" (.proj `T 0 smk)
  report "proj T 1 (S.mk 5 true)   WRONG name; T.y : Nat, yet:" (.proj `T 1 smk)

  logInfo "== 2. is_def_eq_core and equiv_manager ignore it too =="
  deq "proj S 0 c =?= proj S 0 c   (control)   " (.proj `S 0 smk) (.proj `S 0 smk)
  deq "proj S 0 c =?= proj T 0 c   name differs" (.proj `S 0 smk) (.proj `T 0 smk)
  deq "proj S 0 c =?= proj T 1 c   name+idx    " (.proj `S 0 smk) (.proj `T 1 smk)
  -- On an OPEN term nothing can reduce, so this is the union-find deciding.
  withLocalDeclD `h (.const `S []) fun h => do
    deq "(h : S).0 =?= (h : S).0    (control)   " (.proj `S 0 h) (.proj `S 0 h)
    deq "(h : S).0 =?= (h : T).0    name differs" (.proj `S 0 h) (.proj `T 0 h)

  logInfo "== 3. and the line that holds: infer_proj rejects the same expression =="
  withLocalDeclD `h (.const `S []) fun h => do
    for (tag, e) in [("proj S 0 (h : S)  honest", Expr.proj `S 0 h),
                     ("proj T 0 (h : S)  WRONG name", Expr.proj `T 0 h)] do
      match Lean.Kernel.check (← getEnv) (← getLCtx) e with
      | .ok t    => logInfo m!"  {tag}: type-checks as {t}"
      | .error x => logInfo m!"  {tag}: REJECTED — {← (x.toMessageData {}).toString}"

  logInfo "== 4. exactly how far that line reaches =="
  -- `Kernel.check` is infer_only = false, so it DOES descend into arguments.
  let bad := Expr.proj `T 0 smk
  let inArg := mkApp2 (.const `id [.succ .zero]) (.const `Nat []) bad
  match Lean.Kernel.check (← getEnv) {} inArg with
  | .ok t    => logError m!"  check (id Nat <bad proj>): ACCEPTED as {t} — the guard did not descend"
  | .error x => logInfo m!"  check (id Nat <bad proj>): rejected — {← (x.toMessageData {}).toString}"
  -- `whnf` infers in infer_only = true mode, where `infer_app` never infers an
  -- argument at all, so the same term passes straight through and reduces.
  match Lean.Kernel.whnf (← getEnv) {} inArg with
  | .ok r    => logInfo m!"  whnf  (id Nat <bad proj>): reduced to {r}   <- guard never ran"
  | .error x => logInfo m!"  whnf  (id Nat <bad proj>): error {← (x.toMessageData {}).toString}"

/-
Expected on every released toolchain through v4.33.0-rc1:

  1. proj T 0 (S.mk 5 true) reduces to `5`  — a `Nat`, where `T.x : Bool`
     proj T 1 (S.mk 5 true) reduces to `true` — a `Bool`, where `T.y : Nat`
  2. `proj S 0 c =?= proj T 0 c` is TRUE, both closed and open; only a differing
     INDEX is caught.
  3. `Kernel.check` rejects `proj T 0 (h : S)` with `(kernel) invalid projection`.
  4. `Kernel.check` rejects the same projection in ARGUMENT position, because
     that traversal is infer_only = false; `Kernel.whnf` reduces it to `5`
     without ever invoking the guard, because its traversal is infer_only = true
     and `infer_app` does not infer arguments there.

On `master` all of 1 and 2 flip: reduce_proj_core declines, and both def-eq sites
compare the name first.
-/
