import Lean
/-! NEGATIVE CONTROL for `leanchecker`.
    Adds a blatantly ill-typed `theorem illTyped : False` to the environment with the
    kernel check disabled.  If `leanchecker` is really re-checking, it MUST reject
    this module. -/
open Lean Elab Command

structure Pair where
  fst : Nat
  snd : Bool

set_option debug.skipKernelTC true in
run_cmd do
  let d : Declaration := .thmDecl {
    name := `illTyped
    levelParams := []
    type := mkConst ``False
    value := mkApp2 (mkConst ``Pair.mk) (mkNatLit 0) (mkConst ``Bool.true) }
  liftCoreM <| Lean.addDecl d
  logInfo "added `illTyped : False` with kernel type-checking disabled"

#print axioms illTyped
