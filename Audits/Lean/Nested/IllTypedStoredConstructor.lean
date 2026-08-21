import Lean
/-!
STATUS CHANGED, measured 2026-08-21: THIS ROUTE IS CLOSED, and this file no
longer elaborates cleanly.

`check_no_nested_aux` (lean4#14616, shipped in `v4.33.0`) refuses a declaration
naming a `_nested` auxiliary, so on BOTH `v4.33.0` and `v4.33.1` this module
stops at

    (kernel) invalid declaration 'B.node', it uses the reserved prefix '_nested'

and its `#guard_msgs` fail accordingly.  The header below claims `v4.27.0-rc1`
through `v4.33.0-rc1`; read that as ending at `v4.32.2`, the last release
without the check.  The analysis stands -- positivity's `whnf` erases an
occurrence, and a released kernel stored a constant its own `Kernel.check`
rejects -- and what closed it was a NAME check, not a fix to positivity.

--------------------------------------------------------------------------------

DEFECT (no `False` demonstrated).  A **safe**, axiom-free declaration that makes a
released Lean kernel store three constants its own type checker rejects:
`B.node`, `B.rec`, and `B.rec`'s computation rule.  `lean --trust=0` exits 0 and
`#print axioms` reports nothing.

This is lean4#14616's mechanism — a declaration checked against the kernel's
transient `_nested` auxiliary type and stored against the real nested occurrence —
reached from the **safe** path.  `../Nested/AuxNameReachability.lean` shows the two
obvious levers being closed by `check_positivity`, and the third (`isUnsafe`)
being closed by the safety gate.  This file is the way past `check_positivity`.

--------------------------------------------------------------------------------
THE MECHANISM, in one paragraph.

`check_positivity` (inductive.cpp:452) begins

    void check_positivity(expr t, name const & cnstr_name, int arg_idx) {
        t = whnf(t);
        if (!has_ind_occ(t)) {
            // nonrecursive argument
        } else if ...

so a field whose type *reduces* to something with no occurrence of the types being
declared is dismissed without ever being looked at.  But the kernel stores the
**unreduced** type, and `restore_nested` rewrites `_nested` occurrences inside it.
Hide the auxiliary behind a definition that discards its argument and the only gate
standing on the safe path never sees it.

`Ignore (_ : Prop) : Prop := True` is such a definition.  `whnf (Ignore X)` is
`True` for every `X`, so positivity returns at its first branch; `Ignore X` still
demands `X : Prop`, which the auxiliary satisfies at `.{0}`; and after restoration
the argument is `Wrap (@B n)`, which lives in `Sort u`.  The stored constructor is
therefore ill typed, and so is everything the kernel derived from it.

WHY IT IS NOT (YET) A `False`.  `Ignore X` is definitionally `True` whichever
argument it holds, so the ill-typedness is inert: every *use* of the constructor
reduces past it.  That is the same verdict lean4#14631 reached about `proj_sname`
— a broken local invariant with no reachable consequence — and it is exactly what
lean4#14621's re-check of the restored declarations was added to catch.  Upstream's
comment on that PR calls the re-check "redundant by construction" and "not
necessary"; on a released kernel this is a case where it fires.

The escape is also the reason it is inert.  For the occurrence to survive `whnf` it
would have to appear in the reduced type, and then positivity sees it; for it to be
erased by `whnf` it has to be discarded, and then it cannot mean anything.  Closing
that gap is what a route to `False` from here would need.

STATUS.  `master` rejects this before any of it happens — `check_no_nested_aux`
(lean4#14616) rejects the `_nested` prefix in a constructor type, and this
declaration names it.  So this is not a new defect on `master`; it is a strictly
stronger reproduction on every released toolchain, and it locates a second
ingredient the upstream commit message does not mention.

Run with plain `lean --trust=0 IllTypedStoredConstructor.lean`.
-/
open Lean Elab Command Meta

private def u : Level := .param `u

/- Host: `Wrap.{v} (α : Sort v) : Sort v | mk : α → Wrap α`.  A legitimate
kernel-level inductive that the frontend refuses; see
`../Metatheory/ProjBeyondRecursor.lean`. -/
run_cmd liftCoreM (addDecl (.inductDecl [`u] 1
  [{ name := `Wrap, type := .forallE `a (.sort u) (.sort u) .default
     ctors := [{ name := `Wrap.mk
                 type := .forallE `a (.sort u)
                          (.forallE `x (.bvar 0) (.app (.const `Wrap [u]) (.bvar 1)) .default)
                          .default }] }] false))

/-- The eraser.  Ordinary, safe, axiom-free — and `whnf (Ignore X) = True`. -/
def Ignore (_ : Prop) : Prop := True

/-- info: 'Ignore' does not depend on any axioms -/
#guard_msgs in
#print axioms Ignore

/-
`B.{u} (n : Nat) : Sort u` with one constructor and two fields:

  w1 : Wrap.{u} (B n)                        -- the real nested occurrence; creates
                                             --   the auxiliary `_nested.Wrap_1`
  w2 : Ignore (_nested.Wrap_1.{0} n)         -- names that auxiliary, at level 0,
                                             --   behind the eraser

`isUnsafe` is `false`.  Nothing here is a flag, a `sorry`, or an axiom.
-/
run_cmd liftCoreM (addDecl (.inductDecl [`u] 1
  [{ name := `B, type := .forallE `n (.const `Nat []) (.sort u) .default
     ctors := [{ name := `B.node
                 type := .forallE `n (.const `Nat [])
                          (.forallE `w1 (.app (.const `Wrap [u]) (.app (.const `B [u]) (.bvar 0)))
                            (.forallE `w2 (.app (.const `Ignore [])
                                             (.app (.const `_nested.Wrap_1 [.zero]) (.bvar 1)))
                              (.app (.const `B [u]) (.bvar 2)) .default) .default) .default }] }] false))

-- The auxiliary is gone; what was stored is the real occurrence, at the real
-- universe, in an argument position that demanded a `Prop`.
/-- info: B.node : (n : Nat) → Wrap (B n) → Ignore (Wrap (B n)) → B n -/
#guard_msgs in
#check @B.node

/-! ### The kernel rejects what the kernel stored

Every one of these is a constant in the environment right now.  `Kernel.check` is
the same type checker that accepted the declaration. -/

run_cmd liftTermElabM do
  let env ← getEnv
  let mut bad : Nat := 0
  let chk (what : String) (e : Expr) : MetaM Bool := do
    match Lean.Kernel.check env {} e with
    | .ok _    => logInfo m!"  {what}: re-checks OK"; return false
    | .error x => logInfo m!"  {what}: ILL-TYPED — {← (x.toMessageData {}).toString}"; return true
  for nm in [`B, `B.node, `B.rec] do
    let some ci := env.find? nm | continue
    if ← chk s!"type of {nm}" ci.type then bad := bad + 1
  let some (ConstantInfo.recInfo ri) := env.find? `B.rec | return
  for r in ri.rules do
    if ← chk s!"rhs of B.rec's rule for {r.ctor}" r.rhs then bad := bad + 1
  if bad == 0 then
    logError "*** no ill-typed constant found — this toolchain has the fix, update the matrix ***"
  else
    logInfo m!"{bad} stored constants are rejected by the kernel that stored them."

/-
Expected on every released toolchain through v4.33.0-rc1:

  type of B:      re-checks OK
  type of B.node: ILL-TYPED — application type mismatch, Ignore (@Wrap (@B n)),
                  argument has type Sort u but function has type Prop → Prop
  type of B.rec:  ILL-TYPED — same
  rhs of B.rec's rule for B.node: ILL-TYPED — same
  3 stored constants are rejected by the kernel that stored them.

On `master`, the declaration itself is rejected:
  "invalid declaration 'B.node', it uses the reserved prefix '_nested'".

Note the control in `AuxNameReachability.lean` section 2: written *without* the
eraser, the identical field is rejected by `check_positivity` with
"contains a non valid occurrence of the datatypes being declared".  The eraser is
the whole difference.
-/
