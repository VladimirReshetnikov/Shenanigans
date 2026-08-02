module

public import Lean

/-!
CONTROL.  The identical `partial` definition of `False`, used from a safe theorem
in the SAME module — so no stub is ever created and the kernel sees the real
`partial` definition.  It refuses.

Acceptance of `Consumer.lean` means something only because this is rejected by
the same kernel on the same toolchain.  The two error messages differ, and the
difference is the whole defect: here the kernel is told it is looking at a
`partial` *definition*; across the boundary it is told it is looking at a safe
*axiom*.
-/

open Lean

public section

run_meta do
  addDecl (.mutualDefnDecl [{
    name        := `sameModuleFalse
    levelParams := []
    type        := mkConst ``False
    value       := mkConst `sameModuleFalse
    hints       := .opaque
    safety      := .partial
  }])

/--
error: (kernel) invalid declaration, safe declaration must not contain partial declaration 'sameModuleFalse'
-/
#guard_msgs in
theorem sameModuleBoom : _root_.False := sameModuleFalse

end
