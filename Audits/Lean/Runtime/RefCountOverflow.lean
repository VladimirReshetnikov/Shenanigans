/-
Category (see ../../../README.md): **audit**.  No proof of `False` is produced
here, and the reason is hardware rather than anything about the defect -- see
"What is NOT measured here".

THE DEFECT.  lean4#14838, "fix: freeze objects when their reference count
overflows", merged 2026-08-20, label `runtime-soundness`.  From the PR body:

    "This PR prevents memory corruption when an object's 32-bit reference count
     overflows.  On machines with at least 18GB of free RAM, it could be used to
     trigger use-after-free in the official kernel, which could be extended into
     a proof of False.  Other kernels such as nanoda not based on the Lean
     runtime were not affected. ... The issue was reported by Daniel Selsam
     (OpenAI) using their internal models."

This is a different KIND of defect from the rest of this catalog's Lean column.
It is not a kernel-logic mistake and not a `native_decide` divergence: it is a
**memory-safety** defect in the runtime's reference counter, reached through the
kernel's ordinary declaration-checking path by a proof that is merely enormous.
`#print axioms` reports nothing, no flag is set, no escape hatch is used.

THE CONSTRUCTION, simplified from the PR's own reproducer (`tests/elab/14383.lean`
-- that number is an internal report id; the public issue #14383 is an unrelated
`vcgen` PR and is NOT this).  Upstream's declared type also carries two
nondependent `let`s and an 8192-node `Nat.add` padding tree, which are omitted
here; what is kept is the part the audit is about.  Three honest pieces and one
fraudulent step:

  AllSubsingleton.{u} := forall (a : Sort u) (x y : a), x = y
  opaque Enc.{u} : { p : Prop // p = AllSubsingleton.{u} }

  HONEST   encZero     : Enc.{0}.val          -- Sort 0 is Prop; proof irrelevance
  HONEST   encOneFalse : Enc.{1}.val -> False -- Bool : Sort 1 has true != false
  FRAUD    Candidate.{u} : Enc.{u}.val := encZero

The fraud is the universe generalisation: a proof of the `u := 0` instance is
offered as a proof of the schematic `u`.  With `Candidate.{u}` in hand,
`Candidate.{1}` feeds `encOneFalse` and gives `False`.

WHERE THE COUNTER OVERFLOWS.  Read from `src/kernel/level.cpp` at the fix commit
`8df768b731`, not instrumented.  The declared type is built over a `Level.max`
DAG nested `depth` deep over ONE shared leaf level object.  Comparing levels goes
`type_checker::is_def_eq(level, level)` -> `is_equivalent` -> `normalize`, and
`normalize`'s `Max` arm flattens the DAG with `push_max_args`, which has **no
memo table** -- so the sharing is destroyed and the expansion is materialised.
Each slot is a `buffer<level>` `push_back`, i.e. an `object_ref` copy
construction, i.e. one increment of the leaf's reference count.

The peak is **2^(depth+1)**, not 2^depth, and the reason is visible in the
source: `push_max_args(r, todo)` fills `todo` with 2^depth copies, the following
loop fills `args` with another 2^depth *while `todo` is still live*, and `todo`
is only reused afterwards (`buffer<level> & rargs = todo; rargs.clear();`).  So
`depth = 30` gives 2^31 = INT_MAX + 1 -- exactly the smallest depth that
overflows a signed 32-bit counter.  A file claiming 2^30 would not overflow at
all; that arithmetic is why this paragraph exists.

Upstream disagrees with itself about the RAM required: the PR body says "at
least 18GB", the reproducer's own docstring says "~12GB".  Both are recorded
here; neither is measured.

WHAT IS MEASURED BELOW, on v4.33.0 and v4.34.0-rc1.  Not the `False`.  What is
measured is where the fraud is, and -- more usefully -- what the kernel's
acceptance actually keys on:

  * the scaffold (`encZero`, `encOneFalse`) elaborates and typechecks;
  * the fraudulent `Candidate.{u}` is REJECTED with a genuine
    `(kernel) declaration type mismatch` at every depth tried (0, 1, 3, 8, 16);
  * a TRANSPARENT twin -- the same construction with `Enc` a plain `def` instead
    of `opaque` -- is rejected identically.  **So opacity is not what does the
    work**, which is worth stating because it is the natural guess and it is
    wrong;
  * the discriminator is the **normal form of the level**.  A DAG that mentions
    `u`, and is just as large, but whose normal form is `0` -- `imax (maxDag u 8) 0`
    -- is ACCEPTED.  That is the sharp control: it isolates the fraud to the
    level's normal form rather than to the DAG's size, to opacity, or to whether
    `u` occurs at all.

WHAT IS *NOT* MEASURED HERE.  The `False`, and the causal chain from a wrapped
reference count to an accepted ill-typed declaration.  That chain is **upstream's
account**, quoted above, not something re-measured in this repository, and the PR
body itself only claims the use-after-free "could be extended into" a proof of
`False` -- success depends on what the allocator puts in the recycled block, so
it is heap-layout-dependent rather than deterministic.  Reproducing it needs the
reproducer's commented-out `depth := 30` and 12-18GB of free RAM.  Note also that
the test upstream actually merged is de-tuned to `depth := 12`, whose peak is
2^13 references: it exercises the code path and does not reproduce the defect.

RELEASE STATUS, measured 2026-08-20 two ways, because ancestry alone is not
sufficient for Lean -- release branches carry fixes as cherry-picks with fresh
SHAs, a lesson this catalog has already had to learn once:

  * by ancestry -- `8df768b731` is an ancestor of neither `v4.33.0` nor
    `v4.34.0-rc1`, and `git tag --contains` returns nothing;
  * by content -- the token `sticky` does not occur in
    `src/include/lean/lean.h` on either release branch, and both files the PR
    adds under `tests/elab/` are absent from both.

So this is **live on every released toolchain** as of 2026-08-20.

Run: elan run leanprover/lean4:v4.33.0 lean --trust=0 <this file>
-/
import Lean

open Lean

set_option Elab.async false

namespace RCOverflow

/-- Every type in `Sort u` is a subsingleton. True for `u = 0` (proof
    irrelevance), false for `u = 1` (`Bool` has two distinct elements). -/
def AllSubsingleton.{u} : Prop := ∀ (α : Sort u) (x y : α), x = y

/-- As upstream declares it: `opaque`, so it is never delta-reduced. The
    measurement below shows the rejection does NOT depend on this. -/
opaque Enc.{u} : { p : Prop // p = AllSubsingleton.{u} } := ⟨AllSubsingleton.{u}, rfl⟩

theorem encSpec.{u} : Enc.{u}.val = AllSubsingleton.{u} := Enc.{u}.property

/-- Honest: at `Sort 0 = Prop`, proof irrelevance makes `rfl` go through. -/
theorem allZero : AllSubsingleton.{0} := by intro α x y; rfl

/-- Honest. -/
theorem encZero : Enc.{0}.val := Eq.mpr encSpec.{0} allZero

/-- Honest: `AllSubsingleton.{1}` is refutable, since `Bool : Sort 1`. -/
theorem encOneFalse (value : Enc.{1}.val) : False :=
  Bool.noConfusion ((Eq.mp encSpec.{1} value) Bool false true)

/-- The transparent twin: identical, but delta-reducible. -/
def EncD.{u} : { p : Prop // p = AllSubsingleton.{u} } := ⟨AllSubsingleton.{u}, rfl⟩

theorem encDSpec.{u} : EncD.{u}.val = AllSubsingleton.{u} := EncD.{u}.property

theorem encDZero : EncD.{0}.val := Eq.mpr encDSpec.{0} allZero

/-- `Level.max` nested `n` deep over one shared leaf. The DAG holds only `n+1`
    distinct nodes; `2^n` is the size of its *expansion*, which is what
    `normalize` materialises. -/
def maxDag (leaf : Level) : Nat → Level
  | 0 => leaf
  | d + 1 => let p := maxDag leaf d; Level.max p p

end RCOverflow

open RCOverflow

/--
info: FRAUDULENT (a `u := 0` proof offered for schematic `u`), every depth tried:
  opaque      Enc.[maxDag u  0]   REJECTED  declaration type mismatch
  transparent EncD.[maxDag u  0]  REJECTED  declaration type mismatch
  opaque      Enc.[maxDag u  1]   REJECTED  declaration type mismatch
  transparent EncD.[maxDag u  1]  REJECTED  declaration type mismatch
  opaque      Enc.[maxDag u  3]   REJECTED  declaration type mismatch
  transparent EncD.[maxDag u  3]  REJECTED  declaration type mismatch
  opaque      Enc.[maxDag u  8]   REJECTED  declaration type mismatch
  transparent EncD.[maxDag u  8]  REJECTED  declaration type mismatch
  opaque      Enc.[maxDag u 16]   REJECTED  declaration type mismatch
  transparent EncD.[maxDag u 16]  REJECTED  declaration type mismatch
-- so opacity is NOT the discriminator; the level's NORMAL FORM is:
  opaque      Enc.[imax (maxDag u 8) 0]   mentions u, normalises to 0:  ACCEPTED
  transparent EncD.[imax (maxDag u 8) 0]  mentions u, normalises to 0:  ACCEPTED
-/
#guard_msgs in
run_meta do
  let env ← getEnv
  let mut out := #["FRAUDULENT (a `u := 0` proof offered for schematic `u`), every depth tried:"]
  let mk (n c v : Name) (dag : Level) : Declaration :=
    .thmDecl { name := n, levelParams := [`u]
               type := mkProj ``Subtype 0 (mkConst c [dag]), value := mkConst v }
  let verdict (d : Declaration) : MetaM String := do
    match env.addDeclCore 0 4000 d none with
    | .ok _ => return "ACCEPTED"
    | .error e =>
      let m ← (e.toMessageData {}).toString
      return if (m.splitOn "declaration type mismatch").length > 1
             then "REJECTED  declaration type mismatch" else s!"REJECTED  other: {m}"
  for (depth, pad) in [(0, " 0"), (1, " 1"), (3, " 3"), (8, " 8"), (16, "16")] do
    let dag := maxDag (Level.param `u) depth
    let v1 ← verdict (mk `RCOverflow.C1 ``RCOverflow.Enc ``RCOverflow.encZero dag)
    out := out.push s!"  opaque      Enc.[maxDag u {pad}]   {v1}"
    let v2 ← verdict (mk `RCOverflow.C2 ``RCOverflow.EncD ``RCOverflow.encDZero dag)
    out := out.push s!"  transparent EncD.[maxDag u {pad}]  {v2}"
  out := out.push "-- so opacity is NOT the discriminator; the level's NORMAL FORM is:"
  -- Mentions `u`, same DAG size, but `imax _ 0` normalises to `0`.
  let z := Level.imax (maxDag (Level.param `u) 8) Level.zero
  out := out.push ("  opaque      Enc.[imax (maxDag u 8) 0]   mentions u, normalises to 0:  " ++
    (← verdict (mk `RCOverflow.C3 ``RCOverflow.Enc ``RCOverflow.encZero z)))
  out := out.push ("  transparent EncD.[imax (maxDag u 8) 0]  mentions u, normalises to 0:  " ++
    (← verdict (mk `RCOverflow.C4 ``RCOverflow.EncD ``RCOverflow.encDZero z)))
  logInfo (String.intercalate "\n" out.toList)
