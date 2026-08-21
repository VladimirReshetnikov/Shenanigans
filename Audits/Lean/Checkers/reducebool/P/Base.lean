/-
The constant the kernel's native hook evaluates.  It lives in its OWN module,
and that placement is the entire finding: see ../README.md.
-/
prelude
import Init.Prelude

def probe : Bool := Bool.false
