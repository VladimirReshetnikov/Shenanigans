import Lean
/-!
IS_NOT_ZERO FUZZER.  `is_not_zero` (kernel/level.cpp:150) is the one level
predicate the July-2026 strengthening wave did **not** convert to a semantic test:
#14613 and #14615 replaced `is_zero` with `normalizes_to_zero` at five sites and
left `is_not_zero` alone.

It matters because `elim_only_at_universe_zero` (kernel/inductive.cpp:478) reads
it *first*, before the two branches that would otherwise force a `Prop`-only
recursor:

    if (m_is_not_zero) return false;            // large elimination allowed
    if (m_ind_types.size() > 1) return true;    // mutual  => Prop only
    if (num_intros > 1)         return true;    // 2+ ctors => Prop only

So `is_not_zero(l) = true` for a level `l` that *can* be zero would hand a
two-constructor inductive predicate a data-eliminating recursor, and proof
irrelevance would then give `False`.  This is the shape of the Lean Kernel
Arena's `large-elim-param` test, asked of Lean's own predicate.

CHANNEL.  `is_not_zero` is not exposed, so observe it: declare
`X.{u,v,w} : Sort l` with TWO constructors and read whether the generated
recursor gained an elimination universe parameter.  It did iff the kernel
answered `is_not_zero l`.

ORACLE.  `l` can be zero iff some valuation of `u`,`v`,`w` makes it zero.

RESULT (v4.32.2): 360 level spellings at depths 1-3, 360 declared, 91
large-eliminating, **0 unsound**.
-/
open Lean Elab Command

private def evalLvl (s : Name → Nat) : Level → Nat
  | .zero      => 0
  | .succ l    => evalLvl s l + 1
  | .max a b   => Nat.max (evalLvl s a) (evalLvl s b)
  | .imax a b  => let vb := evalLvl s b; if vb == 0 then 0 else Nat.max (evalLvl s a) vb
  | .param n   => s n
  | .mvar _    => 0

/-- Can `l` be `0` under some assignment inside the box? -/
private def canBeZero (l : Level) (box : Nat) : Bool := Id.run do
  for i in [0:box] do
    for j in [0:box] do
      for k in [0:box] do
        let s : Name → Nat := fun n => if n == `u then i else if n == `v then j else k
        if evalLvl s l == 0 then return true
  return false

private def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % (2^64)

private partial def genLvl (seed depth : Nat) : Level × Nat :=
  let r := lcg seed
  if depth == 0 then
    match r % 6 with
    | 0 => (.zero, r) | 1 => (.succ .zero, r) | 2 => (.succ (.succ .zero), r)
    | 3 => (.param `u, r) | 4 => (.param `v, r) | _ => (.param `w, r)
  else
    match r % 7 with
    | 0 => (.zero, r) | 1 => (.param `u, r) | 2 => (.param `v, r) | 3 => (.param `w, r)
    | 4 => let (a, r1) := genLvl r (depth-1); (.succ a, r1)
    | 5 => let (a,r1) := genLvl r (depth-1); let (b,r2) := genLvl r1 (depth-1); (.max a b, r2)
    | _ => let (a,r1) := genLvl r (depth-1); let (b,r2) := genLvl r1 (depth-1); (.imax a b, r2)

run_cmd do
  let mut seed : Nat := 20260801
  let mut lvls : Array Level := #[]
  for d in [1,2,3] do
    for _ in [0:120] do
      let (l,s) := genLvl seed d; seed := s; lvls := lvls.push l
  let mut declared  : Nat := 0
  let mut largeElim : Nat := 0
  let mut bad       : Nat := 0
  let mut idx       : Nat := 0
  for l in lvls do
    idx := idx + 1
    let n    := Name.mkSimple s!"FZ{idx}"
    let self : Expr := .const n [.param `u, .param `v, .param `w]
    let d : Declaration := .inductDecl [`u,`v,`w] 0
      [{ name := n, type := .sort l,
         ctors := [{ name := n ++ `c1, type := self }, { name := n ++ `c2, type := self }] }] false
    match (← getEnv).toKernelEnv.addDecl {} d with
    | Except.error _ => pure ()
    | Except.ok env' =>
      declared := declared + 1
      let some (ConstantInfo.recInfo ri) := env'.find? (n ++ `rec) | continue
      -- the recursor gained an elimination universe iff the kernel said `is_not_zero l`
      if ri.levelParams.length > 3 then
        largeElim := largeElim + 1
        if canBeZero l 5 then
          bad := bad + 1
          if bad ≤ (10:Nat) then
            logError m!"*** LARGE ELIMINATION OF A POSSIBLE Prop *** Sort ({l}), 2 constructors, recursor lparams = {ri.levelParams}"
  logInfo m!"[is_not_zero] levels={lvls.size} declared={declared} largeElim={largeElim} UNSOUND={bad}"
