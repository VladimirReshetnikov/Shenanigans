/-
KERNEL DEFECT (lean4#14875), consumer half.  `theorem boom : False`, axiom-free.

Nothing here is unusual.  This module declares an inductive called
`ClassHidden` -- a name it has every right to use, because `ClassProducer`'s
exported view does not mention it -- and then applies the imported recursor.

`ClassVictim.rec` was CHECKED against the producer's `ClassHidden` (`:= False`)
and is INTERPRETED here against this module's `ClassHidden` (a one-constructor
`Prop`).  `ih` therefore wants a proof of the local `ClassHidden`, which
`ClassHidden.intro` supplies, and returns the `False` the original type promised.

CONTROL, measured: withdraw the redefinition below and this module does not
compile at all --
    Unknown constant `ClassHidden`
-- which is the finding stated as a measurement.  The name really is absent from
the exported view, and the recursor really does depend on it.
-/
module

import IS.ClassProducer

public inductive ClassHidden : Prop where
  | intro : ClassHidden

public theorem boom : False :=
  ClassVictim.rec
    (motive := fun _ => False)
    (fun _ ih => ih ClassHidden.intro)
    classValue

/-- info: 'boom' does not depend on any axioms -/
#guard_msgs in
#print axioms boom

public theorem clearly_False : 2 + 2 = 5 := by
  have h : False := boom
  contradiction
