# Rocq kernel defects — seven regression witnesses and two live routes

Seven soundness defects from the 2026 sweep, each a proof of `False` on an
affected toolchain and each **fixed upstream**. That makes those seven
*regression witnesses*: each must be **rejected** by a current Rocq, and
acceptance would signal a regression.

[`ModuleSystem/UniverseFlagDesync.v`](ModuleSystem/UniverseFlagDesync.v) is the
exception and the reason this README changed. [rocq#22287](https://github.com/rocq-prover/rocq/issues/22287)
is **OPEN**, so that one must be **accepted** — and it is the only route in this
whole repository reachable from nine lines of ordinary source with no
metaprogramming.

Same ground rules as the rest of the directory (see
[`../../README.md`](../../README.md)): a `False` here is a claim about a program,
never a mathematical fact.

> **Warning.** Every file in this directory is a proof of `False` on an affected
> toolchain. They are not part of any build: this repository ships no
> `_CoqProject`, and nothing imports them.

## Contents

| File | Upstream | Verdict on Rocq 9.2 |
| --- | --- | --- |
| [`GuardChecker/NestedMutualCrossCall.v`](GuardChecker/NestedMutualCrossCall.v) | [rocq#21682](https://github.com/rocq-prover/rocq/issues/21682) | rejected — `Recursive definition of F is ill-formed` |
| [`GuardChecker/HigherOrderFixpoint.v`](GuardChecker/HigherOrderFixpoint.v) | [rocq#21683](https://github.com/rocq-prover/rocq/issues/21683) | rejected — `Recursive definition of russell is ill-formed` |
| [`GuardChecker/UniformArgsLet.v`](GuardChecker/UniformArgsLet.v) | [rocq#21701](https://github.com/rocq-prover/rocq/issues/21701) | rejected — `Recursive definition of F_let is ill-formed` |
| [`ModuleSystem/AliasChainDeltaResolver.v`](ModuleSystem/AliasChainDeltaResolver.v) | [rocq#21685](https://github.com/rocq-prover/rocq/issues/21685) | rejected — `Unable to unify` |
| [`GuardChecker/UniformArgsHiddenSelfCall.v`](GuardChecker/UniformArgsHiddenSelfCall.v) | [rocq#21797](https://github.com/rocq-prover/rocq/issues/21797) | rejected — `Recursive definition of F2 is ill-formed`, naming `a`, the argument wrongly believed uniform |
| [`ModuleSystem/WithDefUniverses.v`](ModuleSystem/WithDefUniverses.v) | [rocq#21702](https://github.com/rocq-prover/rocq/issues/21702) | rejected — `universe inconsistency`; the constraint `with Definition` dropped is exactly the one now enforced |
| [`Conversion/RegisterInlineVM.v`](Conversion/RegisterInlineVM.v) | [rocq#21736](https://github.com/rocq-prover/rocq/issues/21736) | rejected **at `Qed`** — `while it is expected to have type`. Affected 8.5–9.1, **and `coqchk` with it** |
| [`GuardChecker/WrongEnvReduction.v`](GuardChecker/WrongEnvReduction.v) | [rocq#21839](https://github.com/rocq-prover/rocq/issues/21839), fixed in 9.2.1 — the installed toolchain is 9.2.**0** | **accepted**, exit 0 — and **`coqchk` accepts it too**. The only exhibit here that both audit channels miss |
| [`GuardChecker/WrongEnvReductionEscape.v`](GuardChecker/WrongEnvReductionEscape.v) | the escape half | **accepted** — ordinary Rocq that merely `Require`s the exhibit and proves `2 + 2 = 5`, with its own clean audit and clean `coqchk` |
| [`ModuleSystem/UniverseFlagDesync.v`](ModuleSystem/UniverseFlagDesync.v) | [rocq#22287](https://github.com/rocq-prover/rocq/issues/22287), **OPEN** | **accepted**, exit 0 — `Closed under the global context`. `coqchk` rejects the `.vo` |
| [`ModuleSystem/UniverseFlagDesyncImport.v`](ModuleSystem/UniverseFlagDesyncImport.v) | the containment half | rejected at the `Require` — `Universe inconsistency` |

**The live one in one paragraph.** `ugraph` keeps a *copy* of the
universe-checking flag, so `Local Unset Universe Checking` inside a `Module`
leaves it desynced when the module closes. `Type` is then an element of itself
outside any flag scope, Hurkens goes through, and `Print Assumptions` reports
`Closed under the global context` — because no flag is in scope where it looks.
Two controls in the same file show the paradox refused before the module and
after a module that does not touch the flag.

It is **contained**: the inconsistency is written into the `.vo`'s universe
graph, so `coqchk` refuses it and any `Require` of it fails at the `Require`
line. What the bug costs is the *local* audit. Compare
[`../../EscapeHatches/Coq/TypingFlags.v`](../../EscapeHatches/Coq/TypingFlags.v)
§3, where the same paradox obtained honestly reports `relies on an unsafe
hierarchy` — and [`../Lean/ModuleSystem/`](../Lean/ModuleSystem/), the same
*shape* in Lean, where the `False` does escape into ordinary downstream code.
Write-up: [`Reports/2026-08-01-rocq-universe-flag-desync.md`](../../Reports/2026-08-01-rocq-universe-flag-desync.md).

**Looking for [rocq#22024](https://github.com/rocq-prover/rocq/issues/22024)?**
It is an open guard-checker defect and it belongs here by subject, but its `False`
is *conditional* — the guard bug needs univalence to witness it — so ground rule 1
puts it in [`../../Paradoxes/Coq/GuardVsUnivalence.v`](../../Paradoxes/Coq/GuardVsUnivalence.v)
instead. That file says so in its own header. It is the only exhibit in this
catalog whose category and whose subject-matter home disagree.

The Rocq paradoxes moved to [`../../Paradoxes/Coq/`](../../Paradoxes/Coq/), and
the flag-gated routes to `False` — including `Unset Guard Checking` and
`Unset Positivity Checking`, which reach the same failures *by design* — are in
[`../../EscapeHatches/Coq/`](../../EscapeHatches/Coq/).

## Reproducing

```powershell
pwsh KernelDefects/Coq/verify.ps1
```

Each exhibit is compiled in a scratch directory outside the repository, and the
script **asserts** both the verdict and a distinguishing substring of the output.
Expected final line: `All 11 Coq exhibits behaved as documented.`
Verified on **The Rocq Prover 9.2** (OCaml 4.14.2).

## Why these four, and why they cluster

All three guard-checker defects are failures of the *same* analysis — uniform
argument computation for nested mutual fixpoints — reached three different ways:
cross-calls, `let`-bound recursive aliases, and higher-order passing. That is why
they share a directory rather than being filed separately.

The clustering is structural rather than accidental, and it is the sharpest
Lean/Rocq contrast this repository has:

* Rocq checks recursion with a syntactic **guard checker** over `Fixpoint`
  definitions. Deciding termination from the shape of a term is subtle enough
  that a single refactor —
  [PR #17986](https://github.com/rocq-prover/rocq/pull/17986), the V8.20
  nested/uniform-parameter rework — introduced **four** separate proofs of
  `False`, of which three are witnessed here. Worse, the fix for one of them
  ([#20555](https://github.com/rocq-prover/rocq/issues/20555)) introduced
  another ([#21683](https://github.com/rocq-prover/rocq/issues/21683)), the
  `HigherOrderFixpoint.v` case. Lean compiles recursion to recursors and
  eliminators, so it has no guard checker and no analogue of this family.
* Rocq's **module system** — functors, aliases, `Include`, delta-resolution — is
  a large piece of trusted infrastructure with no Lean counterpart at all.
  `AliasChainDeltaResolver.v` is one of a family; [#21051](https://github.com/rocq-prover/rocq/issues/21051)
  is the same defect for non-aliased functors, and
  [#22287](https://github.com/rocq-prover/rocq/issues/22287) — a universe-flag
  desync on module close, still **open** — is the newest.

Neither observation makes Lean safer overall: see
[`../Lean/`](../Lean/) for its own defects, which cluster instead around
name-keyed normalizer extensions, unchecked term construction in the
nested-inductive path, and C++ fixed-width integer truncation. The point is that
the two systems' soundness risks live in structurally different places, so a
catalog of one says very little about the other.

## Sources

* Rocq's own [`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
  — the maintainer-curated ledger of every soundness bug since 8.0. There is no
  Lean equivalent.
* Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood)
  — the systematic AI-driven search that produced seven of the eight Rocq proofs
  of `False` from this wave, four of them witnessed here.
* The [`rocq-prover/rocq`](https://github.com/rocq-prover/rocq/issues) tracker,
  label `kind: inconsistency`.
* Full ledger with affected version ranges: [`../../CATALOG.md`](../../CATALOG.md) §4.
