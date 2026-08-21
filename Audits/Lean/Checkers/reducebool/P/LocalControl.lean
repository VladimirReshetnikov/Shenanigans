/-
THE CONTROL, and the reason the finding is about `leanchecker` rather than about
the kernel.

Byte-for-byte the construction in `P/Boom.lean`, except that `probe` is declared
HERE instead of imported.  The kernel's verdict is identical -- `lean --trust=0`
accepts, `#print axioms` is clean, `boomLocal : False`.  `leanchecker` refuses
it:

  leanchecker P.LocalControl
    leanchecker found a problem in P.LocalControl
    uncaught exception: while replaying declaration 'rb_nativeL':
    (kernel) (interpreter) unknown declaration 'probeL'
    exit 1

That message is the whole story: `leanchecker` DOES replay the native hook -- it
names the declaration it was replaying -- and the interpreter it calls fails to
resolve a constant local to the module under replay.  Import the same constant
and the interpreter resolves it and the replay succeeds.
-/
prelude
import Init.Prelude

def probeL : Bool := Bool.false

def Lean.reduceBool (_b : Bool) : Bool := Bool.true

theorem rb_declL (b : Bool) : Eq (Lean.reduceBool b) Bool.true := rfl

theorem rb_nativeL : Eq (Lean.reduceBool probeL) Bool.false := rfl

theorem true_eq_falseL : Eq Bool.true Bool.false :=
  @Eq.rec Bool (Lean.reduceBool probeL) (fun x _ => Eq x Bool.false)
    rb_nativeL Bool.true (rb_declL probeL)

def IsTrueL (b : Bool) : Prop :=
  @Bool.rec (fun _ => Prop) False True b

theorem boomLocal : False :=
  @Eq.rec Bool Bool.true (fun x _ => IsTrueL x) True.intro Bool.false true_eq_falseL

#print axioms boomLocal
