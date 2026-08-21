/-
KERNEL DEFECT (lean4#14875), hidden half.

An ordinary public definition.  Its only role is to be visible to the producer
through `import all` and ABSENT from the producer's exported view.
-/
module

public def ClassHidden : Prop := False
