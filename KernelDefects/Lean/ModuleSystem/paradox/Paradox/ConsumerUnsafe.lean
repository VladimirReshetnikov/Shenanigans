module

public import Paradox.ProducerUnsafe

/-!
DIFFERENTIAL CONTROL, consumer half.  The same module boundary, the same shape,
the same `addDecl` — and the kernel refuses, because `.unsafe` satisfies
`defn.safety == .unsafe` and the stub keeps its marking.

Contrast [`Consumer.lean`](Consumer.lean), which is accepted.  The whole
difference between the two files is `.partial` versus `.unsafe` in the producer.
-/

/--
error: (kernel) invalid declaration, it uses unsafe declaration 'unsafeFalse'
-/
#guard_msgs in
public theorem unsafeBoom : _root_.False :=
  unsafeFalse
