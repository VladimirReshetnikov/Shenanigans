prelude

inductive MyUnit : Type where
  | mk : MyUnit

inductive MyBool : Type where
  | myTrue  : MyBool
  | myFalse : MyBool

inductive MyEq {A : Sort u} (a : A) : A → Prop where
  | refl : MyEq a a

inductive MyFalse : Prop

inductive MyTrue : Prop where
  | intro : MyTrue

/-- The code generator looks this up BY NAME while compiling an `opaque`.
    `Init.Prelude` is not imported here, so the name is free and we supply it. -/
def lcErased : Type := MyUnit

/-- Same story as `lcErased`: a compiler-internal name, free here. -/
def lcAny : Type := MyUnit
