module

public import Lean

/-!
KERNEL DEFECT, producer half.  A `partial` definition whose type is `False`.

The kernel accepts this.  `environment::add_mutual` requires a mutual block to be
tagged `unsafe`/`partial` (it rejects `safe`), and a `partial` block carries no
inhabitance obligation at the kernel level — the `Inhabited`/`Nonempty` obligation
belongs to the `partial def` *elaborator*, not to `Declaration.mutualDefnDecl`.
What protects soundness is the safety gate in `type_checker::infer_constant`,
which refuses to let a safe declaration mention this one.  Within THIS module
that gate works; see `Control.lean`.

Nothing here is a flag, a `sorry`, an axiom, or `debug.skipKernelTC`.
-/

open Lean

public section

run_meta do
  addDecl (.mutualDefnDecl [{
    name        := `partialFalse
    levelParams := []
    type        := mkConst ``False
    value       := mkConst `partialFalse
    hints       := .opaque
    safety      := .partial
  }])

end
