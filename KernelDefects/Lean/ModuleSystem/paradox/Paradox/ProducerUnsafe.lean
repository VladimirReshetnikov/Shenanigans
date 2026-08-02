module

public import Lean

/-!
DIFFERENTIAL CONTROL, producer half.  The identical construction with
`safety := .unsafe` instead of `.partial`.

This is the control that isolates the defect to a single token.  `addDeclCore`
builds the export stub with `isUnsafe := defn.safety == .unsafe`; for `.unsafe`
that is `true`, so the stub stays unsafe and the boundary blocks it.  For
`.partial` it is `false`, and the boundary does not.  Everything else about the
two constructions is the same.
-/

open Lean

public section

run_meta do
  addDecl (.mutualDefnDecl [{
    name        := `unsafeFalse
    levelParams := []
    type        := mkConst ``False
    value       := mkConst `unsafeFalse
    hints       := .opaque
    safety      := .unsafe
  }])

end
