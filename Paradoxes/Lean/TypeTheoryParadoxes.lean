import TypeTheoryParadoxes.Girard
import TypeTheoryParadoxes.CoquandPaulin
import TypeTheoryParadoxes.LargeElimination
import TypeTheoryParadoxes.Univalence
import TypeTheoryParadoxes.Blockers

/-!
# Paradoxes of type theory, in Lean 4

Every theorem in this library derives `False` from an explicit hypothesis that
Lean's type theory withholds, and every one of them reports **no axioms at all**.
Read a `… → False` here as a negative result about type theory — a proof that the
hypothesised rule cannot be added — never as a defect in Lean.

| Module | Hypothesis granted | Classical name |
| --- | --- | --- |
| `Girard` | `Type u` closed under products indexed by `Type u` | Girard 1972 / Hurkens 1995 |
| `CoquandPaulin` | a retraction of `(α → Prop) → Prop` into `α` | Coquand–Paulin 1990; Cantor |
| `LargeElimination` | data-carrying elimination out of a proof-relevant `Prop` | the subsingleton-elimination barrier |
| `Univalence` | a map from bijections to equalities whose transport computes | univalence — and Lean needs no second hypothesis, because proof irrelevance makes UIP definitional |
| `Blockers` | *nothing* — records the exact judgment Lean refuses, machine-checked | — |

The Rocq counterparts are in `Paradoxes/Coq/`; the routes that need
no hypothesis because a *flag* or an escape hatch grants it are in
`EscapeHatches/`.
-/
