module

public import Paradox.Producer

/-!
KERNEL DEFECT, consumer half.  `theorem Paradox : False`, from a **safe**
declaration, on every released toolchain.

`Producer` is a `module` and is not `@[expose]`d, so its definitions cross the
boundary as axiom stubs: `Lean.addDeclCore` (`src/Lean/AddDecl.lean:118`)
publishes `.axiomInfo { defn with isUnsafe := defn.safety == .unsafe }`.  That
test is **false for `DefinitionSafety.partial`**, so the stub is an ordinary safe
axiom of type `False`, and both of the kernel's safety gates miss it — the first
because `is_unsafe()` answers false, the second because it only inspects
definitions and a stub is an axiom.

This is lean4#14609, fixed on `master` 2026-07-30 by `d53dcb222f`
(`defn.safety != .safe`).  No released toolchain carries the fix, and it is not
on `releases/v4.33.0` either.
-/

public theorem partialBoom : _root_.False :=
  partialFalse

/-- It really is `False`; anything follows. -/
public theorem oneEqTwo : (1 : Nat) = 2 := partialBoom.elim

/-- The headline, stated the way the catalog states it. -/
public theorem Paradox : _root_.False := partialBoom
