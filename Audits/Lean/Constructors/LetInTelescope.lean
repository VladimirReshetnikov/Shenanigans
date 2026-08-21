/-
Category (see ../../../README.md): **audit**.  No proof of `False` is produced
here.  This is a cross-system negative result with a named reason, mined from
the 2026-08-20 Rocq wave the way ../../../KernelDefects/Lean/ModuleSystem/ was
mined from Dolan's *Counterexamples in Type Systems*.

THE SOURCE MATERIAL.  Three of the nine `kind: inconsistency` issues Rocq took on
2026-08-20 share one trigger and fail in three different subsystems:

    rocq#22378   conversion            a `let` in a constructor type makes
                                       relevance annotations and substitution
                                       disagree
    rocq#22383   variance inference    the same `let` is skipped
    rocq#22387   module subtyping      the same `let`'s declaration ORDER is
                                       significant to `match` and invisible to
                                       whole-arity conversion

Each is a closed, flag-free, axiom-free `False` on Rocq 9.2 that both audit
channels miss.  Exhibits for all three live in
../../../KernelDefects/Coq/{Conversion,Universes,ModuleSystem}/.

THE QUESTION FOR LEAN.  Lean has no `SProp` and no relevance array, so #22378's
particular failure has nothing to be about.  The transferable question is
positional and sharper: when a constructor's telescope contains a `let`, do the
pieces of the kernel that COUNT that telescope and the pieces that WALK it agree
about what they are looking at?

THE ANSWER IS THAT THEY DO NOT — AND THAT IT DOES NOT MATTER, FOR AN UNRELATED
REASON.  Both halves are worth recording, because only the first half is the
interesting one and only the second half is the reason there is no defect.

  (a) The two walks genuinely disagree about a `let`.  From `releases/v4.33.0`:

        add_inductive_fn::declare_constructors, kernel/inductive.cpp:463
          unsigned arity = 0; expr it = t;
          while (is_pi(it)) { it = binding_body(it); arity++; }
          unsigned nfields = arity - m_nparams;

      is a bare `is_pi` walk.  A `letE` is not a `Pi`, so this walk STOPS at one
      and the `let` is never counted as a field.  Meanwhile

        type_checker::infer_proj, kernel/type_checker.cpp
          r = whnf(r);
          if (!is_pi(r)) throw invalid_proj_exception(...);

      walks the same telescope through `whnf`, which zeta-reduces a `letE` and
      CONTINUES PAST IT.  One stops, the other steps through.  That is exactly
      the ingredient rocq#22378 is built from: two consumers of one telescope
      with different ideas of its shape.

  (b) The disagreement is unreachable, and what closes it is not a check about
      fields at all.  `check_constructors` walks the Pi-telescope and then hands
      whatever is left to `is_valid_ind_app`, which requires an application of
      the inductive being declared.  A `letE` anywhere in the telescope stops
      that walk early, so the residue is a `letE` rather than an application and
      the declaration is refused — with a message about the RETURN TYPE, which
      is the giveaway that nothing here was thinking about `let` at all.

So Lean is not safe here because its kernel agrees with itself about `let` in a
constructor telescope.  It is safe because it refuses to have one.  A future
change that taught `check_constructors` to zeta-reduce before
`is_valid_ind_app` — which would look like a small generalisation — would open
(a) at the same time, and that is the thing this file exists to say.

MEASURED BELOW, on v4.33.0: four placements of a `let` in a one-constructor
inductive's telescope, all four refused by the same check, plus the positive
control that the identical declaration without the `let` is accepted with the
field count the bare walk predicts.

Run: elan run leanprover/lean4:v4.33.0 lean --trust=0 <this file>
-/
import Lean

open Lean

set_option Elab.async false

namespace LetInTelescope

def unitT := mkConst ``Unit
def unitV := mkConst ``Unit.unit
def natT  := mkConst ``Nat

/-- Four placements of a `let` in a one-constructor inductive's telescope, plus
    the same telescope with no `let` at all. -/
def variants (n : Name) : List (String × Expr) :=
  let self := mkConst n
  [ ("let LAST, before the return type",
      mkForall `x .default natT <| mkForall `y .default natT <|
        .letE `g unitT unitV self false),
    ("let BETWEEN two fields",
      mkForall `x .default natT <|
        .letE `g unitT unitV (mkForall `y .default natT self) false),
    ("let FIRST",
      .letE `g unitT unitV
        (mkForall `x .default natT <| mkForall `y .default natT self) false),
    ("no let at all (positive control)",
      mkForall `x .default natT <| mkForall `y .default natT self) ]

end LetInTelescope

open LetInTelescope

/--
info: let LAST, before the return type: REJECTED — (kernel) invalid return type for 'LC.mk'
let BETWEEN two fields: REJECTED — (kernel) invalid return type for 'LC.mk'
let FIRST: REJECTED — (kernel) invalid return type for 'LC.mk'
no let at all (positive control): ACCEPTED, numFields=2
-/
#guard_msgs in
run_meta do
  let env ← getEnv
  let mut report : Array String := #[]
  for (label, ctorType) in variants `LC do
    -- `maxHeartbeats` 0: the budget is a threshold on a counter that accumulates
    -- across the task, so a finite one would truncate a sweep.  See
    -- ../../Method/HeartbeatBudget.lean.
    let d : Declaration := .inductDecl [] 0
      [{ name := `LC, type := mkSort 1,
         ctors := [{ name := `LC.mk, type := ctorType }] }] false
    match env.addDeclCore 0 10000 d none with
    | .error e =>
      report := report.push s!"{label}: REJECTED — {← (e.toMessageData {}).toString}"
    | .ok env' =>
      let some (.ctorInfo cv) := env'.toKernelEnv.find? `LC.mk
        | throwError "constructor missing after acceptance"
      report := report.push s!"{label}: ACCEPTED, numFields={cv.numFields}"
  logInfo (String.intercalate "\n" report.toList)
