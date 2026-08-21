prelude
import Q.Base

/-- Erases its arguments: `Quot A r` is the ZERO-FIELD structure `MyUnit`
    for every `A` and `r`, so structure eta equates any two inhabitants. -/
noncomputable def Quot (A : Type) (r : A → A → Prop) : Type := MyUnit

/-- OPAQUE, so the kernel has no value to unfold and the head stays literally
    `Quot.mk` with three arguments -- what `quot_reduce_rec` matches on. -/
opaque Quot.mk (A : Type) (r : A → A → Prop) (a : A) : Quot A r := MyUnit.mk

/-- args[3] = `f`, args[5] = the `mk`. -/
noncomputable def Quot.lift (A : Type) (r : A → A → Prop) (B : Type)
    (f : A → B) (b0 : B) (q : Quot A r) : B := b0

noncomputable def rel (_ _ : MyBool) : Prop := MyFalse

/-- `P myTrue` is `MyTrue`; `P myFalse` is `MyFalse`. -/
noncomputable def P (b : MyBool) : Prop :=
  MyBool.rec (motive := fun _ => Prop) MyTrue MyFalse b

/-- CONTROL: byte-identical shapes, ordinary names.  `quot_reduce_rec` is keyed
    on `Quot.lift`/`Quot.mk`, so nothing fires for these. -/
opaque Safe.mk (A : Type) (r : A -> A -> Prop) (a : A) : Quot A r := MyUnit.mk

noncomputable def Safe.lift (A : Type) (r : A -> A -> Prop) (B : Type)
    (f : A -> B) (b0 : B) (q : Quot A r) : B := b0
