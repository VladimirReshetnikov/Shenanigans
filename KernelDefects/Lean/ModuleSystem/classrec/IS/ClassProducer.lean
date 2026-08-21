/-
KERNEL DEFECT (lean4#14875), producer half.

`import all` lets this module see through `ClassHidden` to its body, `False`.
That is what makes `classValue` typecheck: `fun h => False.elim h` needs to know
that a `ClassHidden` IS a `False`.

The generated recursor `ClassVictim.rec` retains a reference to `ClassHidden` --
but `ClassHidden` is omitted from this module's EXPORTED view, because it
arrived through `import all`.  So a downstream module receives a recursor whose
dependency it cannot see, and is free to bind that global name to something else.

CONTROL, measured: replacing `import all` with a plain `import` makes this file
fail to build --
    Application type mismatch: The argument ...
at the `False.elim` -- because without `import all` the body of `ClassHidden` is
invisible here too.  The one token is load-bearing.
-/
module

import all IS.ClassHidden

public def ClassWrap (P : Prop) : Prop := ClassHidden → P

public class inductive ClassVictim : Prop where
  | public roll : ClassWrap ClassVictim → ClassVictim

public instance classValue : ClassVictim :=
  ClassVictim.roll (fun h => False.elim h)
