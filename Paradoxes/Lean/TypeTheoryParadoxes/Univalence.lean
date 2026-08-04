/-!
# Univalence, and why Lean needs no second hypothesis to refute it

PARADOX (see `../../README.md`): the cost is a hypothesis in the *statement*.
`univalence_false` is axiom-free, and it is a negative result about type theory —
a proof that univalence cannot be added to Lean — never a defect in Lean.

## The classical statement, and the Lean one

The classical inconsistency is **univalence + UIP**. Univalence makes
`Bool = Bool` inhabited by something other than `rfl` — the swap — while UIP
(uniqueness of identity proofs, Streicher's axiom K) says every proof of `a = a`
*is* `rfl`. Transport along the swap sends `true` to `false`; transport along
`rfl` sends `true` to `true`; UIP identifies the two.

**In Lean only one of the two hypotheses is needed, because the other is a
theorem — indeed a definitional one.** `Eq` is a `Prop`, and Lean's kernel has
definitional proof irrelevance, so any two proofs of `Bool = Bool` are *equal by
`rfl`*. §1 machine-checks that. Univalence alone therefore contradicts Lean, and
`univalence_false` below takes exactly one hypothesis.

The Rocq counterpart is `../../Coq/UnivalenceUIP.v`, and it needs **two** — Rocq
refuses all three judgments of §1, which is why HoTT can be developed there and
cannot be developed here. That asymmetry is the point of having both files.
-/

namespace Univalence

/-! ## 1. UIP is definitional in Lean

Nothing is assumed here. These are the judgments Lean *accepts*, and each is the
ingredient the classical statement has to assume separately. -/

/-- Any two proofs of a type equation are definitionally equal. -/
example (h₁ h₂ : (Bool : Type) = Bool) : h₁ = h₂ := rfl

/-- Hence every proof of `Bool = Bool` is `rfl`. -/
example (h : (Bool : Type) = Bool) : h = rfl := rfl

/-- Hence transport along *any* such proof is definitionally the identity —
which is precisely what univalence must contradict. -/
example (h : (Bool : Type) = Bool) (b : Bool) : cast h b = b := rfl

/-! ## 2. The hypothesis

A bijection, and the univalence ingredient: a map from bijections to equalities
whose transport computes. This is weaker than full univalence (which asks that
`A = B → A ≃ B` be an *equivalence*), so refuting it refutes univalence a
fortiori. -/

structure Bijection (α β : Type) where
  toFun  : α → β
  invFun : β → α
  left   : ∀ a, invFun (toFun a) = a
  right  : ∀ b, toFun (invFun b) = b

/-- The withheld ingredient. Note it is a *structure*, not an `axiom`: the cost
is in the type of `univalence_false`, and the audit stays clean. -/
structure Univalence where
  ua      : {α β : Type} → Bijection α β → α = β
  ua_cast : ∀ {α β : Type} (e : Bijection α β) (a : α), cast (ua e) a = e.toFun a

/-- Boolean negation is a bijection — the swap the classical argument uses. -/
def notBij : Bijection Bool Bool where
  toFun  := not
  invFun := not
  left   := by decide
  right  := by decide

/-! ## 3. `False`

`U.ua_cast notBij true` has type `cast (U.ua notBij) true = not true`. By §1 the
left side is definitionally `true` and the right is definitionally `false`, so
that one term already *is* a proof of `true = false`. -/

theorem univalence_false (U : Univalence) : False :=
  Bool.noConfusion (show (true : Bool) = false from U.ua_cast notBij true)

/-- info: 'Univalence.univalence_false' does not depend on any axioms -/
#guard_msgs in
#print axioms univalence_false

/-! ## 4. The blocker, stated positively

`Blockers.lean` records what Lean refuses by capturing an error message. Here the
same content is available as a *theorem*, which is more robust and says more:
Lean does not merely lack `ua`, it proves that no `Bool = Bool` can transport
`true` anywhere but to `true`. That is the judgment univalence would have to
contradict, and `rfl` proves it. -/

theorem transport_is_trivial (h : (Bool : Type) = Bool) : cast h true = true := rfl

/-- info: 'Univalence.transport_is_trivial' does not depend on any axioms -/
#guard_msgs in
#print axioms transport_is_trivial

/-! ## 5. Why this is not a defect

`Prop` being proof-irrelevant is a deliberate and load-bearing choice — it is
what makes `Decidable` erasure sound and what
`../../../Audits/Lean/Metatheory/Findings.md` §5 lists as valid in the intended
model. Univalence is incompatible with it, and the incompatibility is a fact
about the two rules, not about either implementation. A system wanting
univalence gives up proof irrelevance; that is what HoTT does, and it is why the
Rocq file next door needs UIP spelled out as a hypothesis. -/

end Univalence
