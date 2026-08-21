/-
The `False` crosses a plain `import`, with a clean audit.  Nothing here mentions
`Lean.reduceBool`, `probe`, or the hook.

  #print axioms downstream   ->  'downstream' does not depend on any axioms
  leanchecker P.Downstream   ->  exit 0
-/
prelude
import Init.Prelude
import P.Boom

theorem downstream : False := boom

#print axioms downstream
