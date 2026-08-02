import Lean
/-!
NEGATIVE RESULT.  Dolan's *Overdetermined recursion*
([`Reports/Counterexamples/`](../../../Reports/Counterexamples/)) is Nada Amin's
Scala counterexample, in which each half of a recursive definition is used to
justify the other:

    trait O { type A >: Any <: B; type B >: A <: Nothing }

The `Any <: B` check that `A`'s declaration requires passes because `Any <: A`
by `A`'s declaration and `A <: B` by `B`'s — circular reasoning, and unsound.

Lean's mutual inductive blocks are the obvious place to look for that shape,
because `add_inductive_fn` declares **every** type in the block before checking
**any** constructor, so a constructor really is justified by its siblings.

The circularity is confined to constructors, and that is ordinary mutual
recursion.  It cannot reach the *types*, because `check_inductive_types()` runs
in full before `declare_inductive_types()` — so while a block member's type is
being checked, no member of the block exists yet.  A type that mentions a sibling
is `unknown constant`, whichever way round it is written.

Lean also has no subtyping and no universe *bounds*, so there is no analogue of
`>: Any <: B` for the circularity to be about even if the ordering allowed it.

Run with plain `lean --trust=0 MutualTypeCircularity.lean`.
-/
open Lean Elab Command Meta

private def T : Expr := .sort (.succ .zero)

private def attempt (tag : String) (types : List InductiveType) : MetaM Unit := do
  match (← getEnv).toKernelEnv.addDecl {} (.inductDecl [] 0 types false) with
  | .error e => logInfo m!"rejected  {tag}\n          {← (e.toMessageData {}).toString}"
  | .ok kenv =>
    let mut s := ""
    for n in [`A, `B] do
      if let some ci := kenv.find? n then s := s ++ s!"\n            {n} : {← ppExpr ci.type}"
    logInfo m!"ACCEPTED  {tag}{s}"

run_cmd liftTermElabM do
  -- One way round: B's TYPE indexes over its sibling A.
  attempt "B's type indexes over sibling A"
    [{ name := `A, type := T, ctors := [{ name := `A.mk, type := .const `A [] }] },
     { name := `B, type := .forallE `a (.const `A []) T .default,
       ctors := [{ name := `B.mk,
                   type := .forallE `a (.const `A []) (.app (.const `B []) (.bvar 0)) .default }] }]

  -- The other way round, and fully circular — the Amin shape.
  attempt "A's type mentions B and B's mentions A"
    [{ name := `A, type := .forallE `b (.app (.const `B []) (.const `A.mk [])) T .default, ctors := [] },
     { name := `B, type := .forallE `a (.const `A []) T .default, ctors := [] }]

  -- Control: the circularity Lean does allow, which is through CONSTRUCTORS.
  attempt "ordinary mutual recursion through constructors (control)"
    [{ name := `A, type := T,
       ctors := [{ name := `A.mk, type := .forallE `b (.const `B []) (.const `A []) .default }] },
     { name := `B, type := T, ctors := [{ name := `B.mk, type := .const `B [] }] }]

/-
Expected on every released toolchain through v4.33.0-rc1:

  rejected  B's type indexes over sibling A            (kernel) unknown constant 'A'
  rejected  A's type mentions B and B's mentions A     (kernel) unknown constant 'B'
  ACCEPTED  ordinary mutual recursion through constructors (control)
              A : Type
              B : Type

The ordering that forecloses this is in `add_inductive_fn::operator()`
(kernel/inductive.cpp:781ff):

    check_inductive_types();      // <- every type checked, in an env with none of them
    declare_inductive_types();    // <- now they exist
    check_constructors();         // <- so constructors may refer to siblings
    declare_constructors();
    mk_rec_infos();
    declare_recursors();

which is the same ordering that forecloses the `Expr.proj` route into the
`_nested` auxiliaries (see `AuxNameReachability.lean` §4).  Two different attacks
stopped by one property of the phase order, which is worth noticing: the order is
load-bearing, and it is not itself a check.
-/
