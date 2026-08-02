/-
MEASUREMENT (no `False` here).  The first of the two weaknesses behind
ImaxPropLaundering.lean, isolated and measured on its own.

`add_inductive_fn::check_inductive_types` (kernel/inductive.cpp:246) sets

    m_result_level = sort_level(type)          // FIRST type of the block, verbatim
    m_is_not_zero  = is_not_zero(m_result_level)

and requires every later type only to be `is_equivalent` to it.  Every downstream
gate then reads that single spelling.  `check_constructors` admits an oversized
constructor field when `is_geq(m_result_level, fieldLevel) || is_zero(m_result_level)`,
and `is_zero` (kernel/level.h:106) is `kind() == Zero` — syntactic — while
`is_geq` normalizes.  So the permission a syntactic `Sort 0` earns is inherited
by every other type in the block, whatever *its* sort is spelled as.

The table below is the direct measurement.  The reversal is the control: swap the
two types and the same block is rejected, which is what pins the behaviour on
"first type" rather than on "some type".

Run with plain `lean MutualResultLevel.lean`.
-/
import Lean

open Lean Elab Command

private def weirdT (l : Level) : InductiveType :=
  { name  := `W
    type  := .sort l
    ctors := [{ name := `W.mk, type := .forallE `v (.const ``Bool []) (.const `W []) .default }] }

private def dummyT (l : Level) : InductiveType :=
  { name := `D, type := .sort l, ctors := [{ name := `D.intro, type := .const `D [] }] }

private def imax10 : Level := .imax (.succ .zero) .zero
private def max00  : Level := .max .zero .zero

run_cmd liftTermElabM do
  let env ← getEnv
  let attempt (tag : String) (types : List InductiveType) : MetaM Unit := do
    match env.toKernelEnv.addDecl {} (.inductDecl [] 0 types false) with
    | .ok _     => logInfo m!"ACCEPTED  {tag}"
    | .error _  => logInfo m!"rejected  {tag}"
  attempt "W : Sort (imax 1 0)                       -- alone"        [weirdT imax10]
  attempt "W : Sort (max 0 0)                        -- alone"        [weirdT max00]
  attempt "W : Sort 0                                -- alone"        [weirdT .zero]
  attempt "D : Sort 0        , W : Sort (imax 1 0)   -- laundered"    [dummyT .zero, weirdT imax10]
  attempt "D : Sort 0        , W : Sort (max 0 0)    -- laundered"    [dummyT .zero, weirdT max00]
  attempt "D : Sort (imax 1 0), W : Sort 0           -- REVERSED"     [dummyT imax10, weirdT .zero]
  attempt "D : Sort (max 0 0) , W : Sort 0           -- REVERSED"     [dummyT max00, weirdT .zero]

/-
Expected on every released toolchain through v4.33.0-rc1:

  rejected  W : Sort (imax 1 0)                       -- alone
  rejected  W : Sort (max 0 0)                        -- alone
  ACCEPTED  W : Sort 0                                -- alone
  ACCEPTED  D : Sort 0        , W : Sort (imax 1 0)   -- laundered
  ACCEPTED  D : Sort 0        , W : Sort (max 0 0)    -- laundered
  rejected  D : Sort (imax 1 0), W : Sort 0           -- REVERSED
  rejected  D : Sort (max 0 0) , W : Sort 0           -- REVERSED

On `master` (after lean4#14615) the first two flip to ACCEPTED, because
`check_constructors` now asks `normalizes_to_zero` instead of `is_zero`; the
laundering therefore becomes unnecessary rather than blocked.  The first-type
inheritance itself is unchanged on master, and the REVERSED rows are expected to
stay rejected there.  It is harmless there only because every gate that reads
`m_result_level` became semantic in the same wave — a global invariant standing in
for a local one, which is the pattern lean4#14631 and #14632 were closing.
-/
