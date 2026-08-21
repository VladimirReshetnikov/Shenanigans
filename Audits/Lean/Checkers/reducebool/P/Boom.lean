/-
An axiom-free `False` that `leanchecker` ACCEPTS.

The mechanism is the one in
../../../../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean, unchanged:
`Init.Prelude` leaves the name `Lean.reduceBool` free, the kernel's
`reduce_native` hook is keyed on that name and is tried FIRST in `whnf`, so
defining it gives the kernel two disagreeing rules for one constant.

The ONE difference from that file is that `probe` is imported from `P.Base`
instead of being declared here.  That changes nothing about the kernel -- the
`False` is identical -- and it changes `leanchecker`'s verdict from reject to
accept, because the interpreter it calls resolves imported constants and not
module-local ones.  `P/LocalControl.lean` is the same construction with `probe`
local, and is rejected.
-/
prelude
import Init.Prelude
import P.Base

/-- An ordinary definition of a name `Init.Prelude` leaves free. -/
def Lean.reduceBool (_b : Bool) : Bool := Bool.true

/-- (1) A free variable is not a constant, so `reduce_native` declines and the
    kernel delta-reduces, agreeing with the declaration. -/
theorem rb_decl (b : Bool) : Eq (Lean.reduceBool b) Bool.true := rfl

/-- (2) A nullary constant makes the kernel run the compiled code for `probe`
    and believe the answer. -/
theorem rb_native : Eq (Lean.reduceBool probe) Bool.false := rfl

/-- (3) Hence `true = false`. -/
theorem true_eq_false : Eq Bool.true Bool.false :=
  @Eq.rec Bool (Lean.reduceBool probe) (fun x _ => Eq x Bool.false)
    rb_native Bool.true (rb_decl probe)

def IsTrue (b : Bool) : Prop :=
  @Bool.rec (fun _ => Prop) False True b

/-- (4) `False`. -/
theorem boom : False :=
  @Eq.rec Bool Bool.true (fun x _ => IsTrue x) True.intro Bool.false true_eq_false

#print axioms boom
