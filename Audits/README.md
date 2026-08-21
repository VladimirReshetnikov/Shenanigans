# Audits: searches for a route, and what they did not find

The other three categories exhibit ways to derive `False`. This one exhibits the
*absence* of one. Each subdirectory is a systematic search for a soundness hole
in a specific mechanism, and the headline result is almost always negative —
which is the useful part of the output, and the reason the harnesses are kept
rather than deleted. Two searches did turn up genuine defects without turning up
a `False`; they are below.

Category (see [`../README.md`](../README.md)): none of these produces `False`.
Where a search turned up something real but sound, it is recorded as an
*anomaly* — a gap between a mechanism and its specification, not a defect.

The Rocq column of this directory was empty until 2026-08-18, and that was a
genuine gap rather than a claim that Rocq has no analogous questions. It now has
two entries — [`Coq/CheckerCoverage/`](Coq/CheckerCoverage/), which asks what a
green `rocqchk` has actually established, and
[`Coq/PrintAssumptions/`](Coq/PrintAssumptions/), which asks the same of Rocq's
own audit command. Both answer "less than you would think", and both are
measurements rather than empty searches. The rest of the gap stands; see
[`../CATALOG.md`](../CATALOG.md) §5.

## Contents

| Path | Question asked | Answer |
| --- | --- | --- |
| [`Lean/Fuzz/NatAcceleratorBoundaries.lean`](Lean/Fuzz/NatAcceleratorBoundaries.lean) | Do the kernel's fourteen name-keyed `Nat` accelerators agree with the compiled implementation at powers-of-two boundaries? | 39,510 applications: **0 divergences** — but the sweep's `shiftLeft` cap hid a kernel abort, see below |
| [`Lean/Fuzz/LevelFuzzer.lean`](Lean/Fuzz/LevelFuzzer.lean) | Does the kernel's `Sort a ≡ Sort b` agree with denotational equality of the level expressions? | 880 random levels, 774,400 pairs: **0 unsound**, 162 incompleteness cases (very likely all instances of [lean4#12747](https://github.com/leanprover/lean4/issues/12747)) |
| [`Lean/Fuzz/DefEqFuzzer.lean`](Lean/Fuzz/DefEqFuzzer.lean) | Can `Kernel.isDefEq a b` hold when the kernel's own `whnf` gives `a` and `b` different `Bool` constants? | 3,354 differing pairs: **0 unsound** |
| [`Lean/Fuzz/IsNotZeroFuzzer.lean`](Lean/Fuzz/IsNotZeroFuzzer.lean) | `is_not_zero` is the one level predicate the July-2026 wave did not make semantic, and `elim_only_at_universe_zero` reads it *before* the "mutual" and "2+ constructors" branches. Does it ever call a possibly-zero level nonzero, and so large-eliminate an inductive predicate? | 360 level spellings, 91 large-eliminating: **0 unsound** |
| [`Lean/Fuzz/CompilerKernelDiff.lean`](Lean/Fuzz/CompilerKernelDiff.lean) | Does `Lean.Kernel.whnf` ever disagree with the compiler on closed terms over `String`/`Char`/`Nat`/`Int`/`UInt`/`BitVec`/`List`/`Array`? | 72 terms: **0 divergences** |
| [`Lean/Checkers/`](Lean/Checkers/) | Every verdict in this repo about an independent checker is a *citation*. Does `nanoda` really reject the universe-spelling defect — and does it reject the **non-normal** `Sort (imax 1 0)` spelling, not just the honest `Sort 0` its own regression test uses? | **Yes, both**, measured on `nanoda_lib` 0.4.10-beta: control accepts (exit 0), both spellings reject (exit 101, `infer_proj prop`). The cross-checking safeguard holds on the exact construction [`Universes/`](../KernelDefects/Lean/Universes/) constructions. |
| [`Lean/Projections/`](Lean/Projections/) | lean4#14631 and #14632 are `master`-only, so a released kernel ignores a projection's structure name in three places. How blind is it, and what stops the blindness becoming a `False`? | **Totally blind, and stopped only by declaration ordering.** `whnf (.proj T 0 (S.mk 5 true))` is `5` where `T.x : Bool`; `.proj S 0 h =?= .proj T 0 h` is `true`. What holds the line is `infer_proj`, which rejects the same expression — and the one place a release stores an unchecked term is separated from it by the order `declare_inductive_types / check_constructors / declare_constructors`. |
| [`Lean/Runtime/RefCountOverflow.lean`](Lean/Runtime/RefCountOverflow.lean) | [lean4#14838](https://github.com/leanprover/lean4/pull/14838) (merged 2026-08-20, label `runtime-soundness`) is a 32-bit reference-count overflow that upstream says could be driven to a use-after-free in the kernel and extended into a proof of `False`. Reproducing it needs 12–18GB of RAM, so it cannot be an exhibit here. What *can* be measured about it? | **Where the unsound step is, and what the kernel's acceptance actually keys on.** The construction's honest scaffold typechecks, and its one unsound step — a `u := 0` proof offered for a schematic `u` — is refused with `(kernel) declaration type mismatch` at every depth tried, on `v4.33.0` and `v4.34.0-rc1`. Two controls overturn the natural reading: a **transparent** twin of upstream's `opaque` constant is refused identically, so opacity is *not* what does the work; and a level that mentions `u` and is just as large but whose normal form is `0` (`imax (maxDag u 8) 0`) is **accepted**. The discriminator is the level's normal form — not opacity, not DAG size, not whether the parameter occurs. The `False` itself, and the chain from a wrapped count to an accepted declaration, are upstream's account and are labelled as such. Also corrects a factor of two that matters: the peak is 2^(depth+1), and 2^30 does *not* exceed `INT_MAX`. See [CATALOG §2.7](../CATALOG.md) and [the report](../Reports/2026-08-20-refcount-overflow.md) |
| [`Lean/Checkers/reducebool/`](Lean/Checkers/reducebool/) | [`../CATALOG.md`](../CATALOG.md) §4.7 said its Lean column was empty "for a structural reason rather than a lucky one", because `leanchecker` "cannot replay [`Lean.reduceBool`] at all". Is that true? | **No, on both halves — and this is the one place in this directory where the answer is a `False` the checker accepts.** `leanchecker` replays the hook; its refusal of the module-local case *names the declaration it was replaying* and fails in the interpreter with `unknown declaration 'probeL'`. The interpreter resolves imported constants and not module-local ones, so moving the evaluated constant into an imported module — leaving the kernel's verdict, the proof term and `#print axioms` untouched — flips the verdict to **accept**. Three modules at exit 0, one of them a `False` crossing a plain `import` with `#print axioms` reporting *"does not depend on any axioms"*. All three of [rocq#22352](https://github.com/rocq-prover/rocq/issues/22352)'s properties at once. **Not a new kernel defect** — the `False` is the §2.3 free-name hook, closed upstream as working-as-intended and needing `prelude`. The finding is the *checker's* verdict, and the axiom accounting that covers `native_decide` does not cover this channel, because it uses no axiom |
| [`Lean/Constructors/LetInTelescope.lean`](Lean/Constructors/LetInTelescope.lean) | Three of the nine `kind: inconsistency` issues Rocq took on 2026-08-20 ([rocq#22378](https://github.com/rocq-prover/rocq/issues/22378), [#22383](https://github.com/rocq-prover/rocq/issues/22383), [#22387](https://github.com/rocq-prover/rocq/issues/22387)) share one trigger: a `let` in a constructor's telescope, which different parts of the kernel count differently. Does Lean's kernel have the same disagreement? | **Yes — and what closes it is an unrelated check.** `declare_constructors` counts fields with a bare `while (is_pi(it))` walk that **stops** at a `letE`; `infer_proj` walks the same telescope through `whnf`, which zeta-reduces and **steps past** one. So the two consumers genuinely disagree — the ingredient #22378 is built from. It is unreachable only because `is_valid_ind_app` needs an application of the inductive where a `letE` now sits: all four placements are refused as an **invalid return type**, a message about something else entirely. Measured on v4.33.0 and v4.34.0-rc1; the no-`let` control is accepted at `numFields=2`. Lean is not safe here because its kernel agrees with itself about `let` — it is safe because it refuses to have one. |
| [`Lean/Positivity/`](Lean/Positivity/) | Dolan's *A little knowledge…* says exposing a hidden implementation should never change whether a program typechecks. Does Lean's strict positivity check depend on visibility? | **Yes.** `inductive Bad1 \| mk : IgnoreD (Bad1 → False) → Bad1` — the type being declared in a **negative** position — is accepted when the wrapper's body is visible and refused when it is `opaque`. Three lines of plain Lean, no metaprogramming. Not a paradox: the field is definitionally `True`. |
| [`Lean/Arena/`](Lean/Arena/) | `CATALOG.md` §5 calls the Lean Kernel Arena corpus the single largest Lean-side gap. An arena test is an *export* test, so most of it is a statement about a checker rather than about Lean source. Which probes are reachable from inside Lean, through `addDecl`? | **Of the fourteen probes in the corpus when this was measured, the kernel rejects every reachable one**, with the exact messages pinned, except the `nested-nonuniform-param` case the arena itself scores `either` — and byte-identically across all seven released pins. **That answer is specific to those fourteen:** three of the four probes added on 2026-08-18 are reachable from inside Lean and are *accepted* on every release, which is why they are defects rather than audits — [`../KernelDefects/Lean/DefEq/`](../KernelDefects/Lean/DefEq/). The table of what is *not* reachable, and why, is the more useful half. The `ctor-num-fields`/`rec-k-lie` family is reachable, but not through `addDecl`, and it turned out to be an escape hatch: [`../EscapeHatches/Lean/ArenaTrustedMetadata.lean`](../EscapeHatches/Lean/ArenaTrustedMetadata.lean). |
| [`Lean/Nested/`](Lean/Nested/) | How far can a declaration reach into the kernel's transient `_nested` auxiliary environment — i.e. is [lean4#14616](https://github.com/leanprover/lean4/pull/14616), which no released toolchain fixes and which has no reproduction anywhere, reachable from a *safe* declaration? | **Yes.** [`IllTypedStoredConstructor.lean`](Lean/Nested/IllTypedStoredConstructor.lean) is a safe, axiom-free module that makes every released kernel store three constants its own `Kernel.check` rejects. No `False` — the ill-typedness is inert. [`AuxNameReachability.lean`](Lean/Nested/AuxNameReachability.lean) is the survey that located the route. **Closed, measured 2026-08-21**: `check_no_nested_aux` ([#14616](https://github.com/leanprover/lean4/pull/14616), shipped in `v4.33.0`) refuses a declaration naming a `_nested` auxiliary, so the exhibit is now rejected on both `v4.33.0` and `v4.33.1` with `(kernel) invalid declaration 'B.node', it uses the reserved prefix '_nested'` — read its "every released toolchain" as ending at `v4.32.2`. |
| [`Lean/Metatheory/`](Lean/Metatheory/) | Is the `Acc` + proof-irrelevance interaction reachable? Is `Expr.proj` conservative over the recursor? | No, and no — but both produce sound anomalies worth recording. See [`Findings.md`](Lean/Metatheory/Findings.md). |
| [`Coq/PrintAssumptions/`](Coq/PrintAssumptions/) | [`../CATALOG.md`](../CATALOG.md) §1.4 asserted that `Print Assumptions` "reports every `bypass_check` flag by name". Does it? | **No, and three separate ways, all live on 9.2.0.** A flag or axiom reachable only through a constant's **type** is dropped ([rocq#21825](https://github.com/rocq-prover/rocq/pull/21825), live on every released Coq/Rocq) — measured with the same guard flag reported through the body and silent through the type. A proof that went through `abstract` loses the declaration's typing flags entirely ([rocq#20550](https://github.com/rocq-prover/rocq/issues/20550), `kind: inconsistency`, and absent from upstream's own `critical-bugs.md`). And cross-file `-impredicative-set` is reported or not depending on how the **reading session** was invoked, over the same `.vo`s ([rocq#22164](https://github.com/rocq-prover/rocq/issues/22164)). Each is paired with a control the same procedure reports correctly. No `False`: these are audit holes, and §1.4 is corrected. |
| [`Method/HeartbeatBudget.lean`](Method/HeartbeatBudget.lean) | An audit of this repository's own method. README ground rule 5 told harnesses to pass a finite `maxHeartbeats` to `addDeclCore`. Is that safe? | **No.** That argument is a THRESHOLD on a counter that accumulates across the whole task, not a per-call allowance. 3000 identical declarations submitted in one command split into accepted and refused at a finite budget and are all accepted at `0` — so a sweep that reads `Except.error` as "the kernel refused this" truncates its own corpus and reports it as a completed sweep. Lean core passes `0` in both places it replays declarations in bulk. **No recorded result here is invalidated**: the largest `addDecl`-looping sweep, [`Lean/Fuzz/IsNotZeroFuzzer.lean`](Lean/Fuzz/IsNotZeroFuzzer.lean), re-runs on v4.33.0 as `levels=360 declared=360 largeElim=91 UNSOUND=0` — nothing dropped. The rule is corrected. |
| [`Coq/CheckerCoverage/`](Coq/CheckerCoverage/) | [`../CATALOG.md`](../CATALOG.md) §4.7 exists because "a CI script that only checks the exit code proves less than it appears to." How much less, on Rocq 9.2? | **Two positive findings and one negative.** Which libraries `rocqchk` validates depends on the ORDER of its `-norec` arguments ([rocq#22362](https://github.com/rocq-prover/rocq/issues/22362)) — two invocations differing only in that give exit 129 and exit 0 on the same files — and the accepting run still prints `Checking library:` for the file it read raw, so neither the log nor the exit code is evidence of validation. Negative result: a `.vo` whose recorded segment MD5 does not match its contents is accepted in every mode, which is **not** unsoundness but does locate the line — the digest is an accident detector, and re-typechecking the bodies is the entire [safeguard]. Which is the limit [rocq#22352](https://github.com/rocq-prover/rocq/issues/22352) relies on, in [`../KernelDefects/Coq/Checker/`](../KernelDefects/Coq/Checker/). |
| [`Lean/StringIdentity/`](Lean/StringIdentity/) | Do Lean's components disagree about when two strings — hence two `Name`s, hence two constants — are the same? | **No soundness gap and no checker break.** Every disagreement found fails closed. One genuine machine-level defect: `Name.toString` is not injective. |

## The three defects this directory has produced

None is a `False`; all three are real, and all three came out of a search whose
headline answer was negative.

### `Nat.shiftLeft` aborts the kernel

`example : (1 : Nat) <<< 4294967296 = 0 := rfl`
terminates the `lean` process with `INTERNAL PANIC: Nat.shiftl exponent is too
big` on every toolchain from `v4.31.0` to `v4.33.0-rc1`, under `--trust=0`, from
one line of ordinary source. `reduce_pow` bounds its exponent and declines
gracefully; the shift helper has no bound and the runtime aborts.

It is a robustness defect, **not** unsoundness — the process dies rather than
continuing with a wrong value, which is the precise difference from
[lean4#8554](https://github.com/leanprover/lean4/pull/8554), where a `panic!`
that did *not* abort made `hasFVar` non-conservative. Write-up and controls:
[`../Reports/2026-07-31-kernel-shiftleft-panic.md`](../Reports/2026-07-31-kernel-shiftleft-panic.md).

The provenance is the useful part: the fuzzer capped `shiftLeft`'s exponent at
4096 to avoid allocating gigabytes, and that cap is exactly what hid the defect
on the first pass. A bound introduced for the harness's own safety is a place
where the harness stops testing.

### Strict positivity depends on what else is visible

`check_positivity` begins `t = whnf(t)`, and `whnf` unfolds definitions — so an
occurrence of the type being declared is invisible to positivity exactly when
some enclosing definition's body is available to reduce it away.
[`Lean/Positivity/VisibilityDependentPositivity.lean`](Lean/Positivity/VisibilityDependentPositivity.lean)
puts the two halves side by side in one file: with a visible wrapper the kernel
accepts a constructor carrying `Bad1 → False`, the negative occurrence positivity
exists to refuse; with `opaque` it refuses the identical declaration.

It is not a paradox, and the reason is the same one that makes the nested-inductive
route below inert: for the occurrence to be hidden from positivity, `whnf` has to
erase it, and an erased argument cannot mean anything. What it does establish is
that **strict positivity is not a property of the declaration being checked** —
it is a property of the declaration plus the ambient set of unfoldable bodies,
and an abstraction boundary changes the answer.

### A safe declaration makes a released kernel store constants it rejects

**Every released Lean toolchain, `v4.27.0-rc1` through `v4.33.0-rc1`.**
`lean --trust=0` exits 0, `#print axioms` is clean, `isUnsafe` is false — and
`B.node`, `B.rec` and `B.rec`'s computation rule all fail `Kernel.check`.
Write-up:
[`../Reports/2026-08-01-positivity-whnf-erasure.md`](../Reports/2026-08-01-positivity-whnf-erasure.md);
artifact [`Lean/Nested/IllTypedStoredConstructor.lean`](Lean/Nested/IllTypedStoredConstructor.lean).

The route is the finding. `check_positivity` begins `t = whnf(t)` and returns
immediately when the reduced form has no occurrence of the types being declared —
but the kernel stores the *unreduced* type, and `restore_nested` rewrites
`_nested` occurrences inside it. Hide the auxiliary behind `def Ignore (_ : Prop)
: Prop := True` and the only gate on the safe path never sees it. Written without
the eraser the identical field is rejected, which is the control.

[`AuxNameReachability.lean`](Lean/Nested/AuxNameReachability.lean) is the
survey that got there: it establishes that the auxiliary name is
predictable, that a safe declaration naming it is accepted, and that the level and
parameter levers both die in `is_valid_ind_app` — which compares the occurrence
against `m_ind_cnsts[i]` with `expr` equality, so the universe levels are covered
too — while the `Expr.proj` lever dies on declaration ordering.

**It is not a `False`, and the reason is structural.** `Ignore X` is
definitionally `True` whichever argument it holds, so every use reduces past the
ill-typed application; and for the occurrence to survive `whnf` it would have to
appear in the reduced type, where positivity would see it. The containment is
also **incidental** — positivity is not a type-preservation check, and it is what
stands between a released kernel and an ill-typed stored constructor, which is
exactly why [#14621](https://github.com/leanprover/lean4/pull/14621) added a
re-check of the restored declarations. That PR's own comment calls the re-check
"not necessary"; here is a case on the release line where it fires.

## The two findings worth carrying forward

**`Expr.proj` is strictly stronger than the recursor, and this refutes a
specification.** For the kernel-level inductive `I2 (a : Sort u) : Sort u | mk :
a → I2 a`, `I2.rec` is restricted to `Prop` motives while `Expr.proj` eliminates
into `Sort v`. It is sound — any substitution making the structure a `Prop` also
makes the field a `Prop` — but it refutes the "a projection is equivalent to an
application of the recursor" desugaring that Lean4Lean's specification of
`Expr.proj` rests on ([arXiv:2403.14064](https://arxiv.org/abs/2403.14064)).
Upstream has the same observation open as
[lean4#7637](https://github.com/leanprover/lean4/issues/7637): *"primitive
projections are currently not conservative over recursors."*

**The kernel's `is_def_eq` is not transitive.** `A ≡ B`, `B ≡ C`, `A ≢ C` for
closed terms over `Acc.rec`. This is incompleteness — the safe direction — and
Carneiro's thesis §3.1 already establishes it, but it is worth having measured,
because the Lean Kernel Arena has since made it an official test category:
`tests/undecidability/alg-conv-trans-acc` scores `either` precisely because
inventing the middle term is a step no algorithm takes. The arena's companion
tests go further and exhibit a **subject-reduction failure**: a term the kernel
accepts reduces to one it rejects.

Both of these say the same thing from different angles, and it is the honest
summary of this whole directory: **Lean's declared conversion relation and the
algorithm implementing it are not the same relation, and the gap is permanent,
not a bug.**

## The `StringIdentity` result, stated precisely

The motivating worry was real: `Name` is the identity of every constant in Lean,
`Name`s are built from `String`s, and wherever two components of a system
disagree about string equality, something can be slipped past the one that is
checking. The answer is that Lean is byte-exact and uniform internally, and
every decision path in [`leanprover/comparator`](https://github.com/leanprover/comparator)
carries names as structural `Lean.Name` — no normalisation, case folding,
collation or dot-splitting anywhere.

The headline lexical result is a negative one: **no character Lean accepts in a
*bare* identifier is one that collation-, NFKC- or `Cf`-stripping comparison
would treat as equal to its absence** — 0 of the 43 invisible/ignorable
characters tested. Every such character requires French quotes `«…»`, which are
conspicuous in source. That is a meaningfully better position than Rocq's, which
accepts bare Cyrillic homoglyphs; the comparison is drawn in
[`../EscapeHatches/Lean/Misreading.lean`](../EscapeHatches/Lean/Misreading.lean) §3
and its Rocq counterpart.
