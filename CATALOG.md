# Catalog: every known way to prove `False` in Lean 4 and Rocq/Coq

The completeness ledger for [`README.md`](README.md)'s claim that this directory
represents every currently known route to `theorem Paradox : False` in both
systems. §1 is the taxonomy and is meant to be exhaustive by *mechanism*. §§2–4
are the defect ledgers and are exhaustive only as far as the sources in §6 go.

**How to read the coverage column.**

| Mark | Meaning |
| --- | --- |
| **artifact** | A machine-checked exhibit lives here, with a control and a pinned-toolchain matrix. |
| **report** | A written analysis lives in [`Reports/`](Reports/), pinned to toolchain versions. |
| **noted** | Recorded here only: understood and cited, no local artifact. |
| **gap** | Not represented. Candidate work. |

**Verification status is stated separately from coverage.** "Verified here" means
it was reproduced on this machine with an explicitly pinned toolchain during the
survey dated below. Everything else is recorded from an upstream source and is
*not* independently confirmed — say so when citing it.

Last survey: **2026-07-31**, against the Lean and Rocq trackers, the
[Lean Kernel Arena](https://arena.lean-lang.org/), Rocq's own
[`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md),
Lean's release-note corpus, `lean4lean`'s `bugs-found.md` and `divergences.md`,
and the blog posts in §6. Local exhibits verified on Lean `4.32.0` and Rocq `9.2`.

Second pass **2026-08-01**, on the released toolchains rather than on `master`.
Diffing `src/kernel/` between `v4.32.2` and the pinned `master` gives the exact
set of checks the shipped kernels lack; two of them are axiom-free proofs of
`False` against the current release, and neither had an artifact anywhere. One is
now [`KernelDefects/Lean/Universes/`](KernelDefects/Lean/Universes/) (§2.1,
§2.6); the other, #14616, is the largest remaining gap (§5). The lesson is worth
stating separately from either: **a fix on `master` is not a fix**, and this file
had been reading the tracker rather than the tags.

Partial re-survey **2026-08-01**, prompted by de Moura's
[postmortem for #14576](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)
(§6). Scope: the Lean kernel PRs of the last week, the arena corpus and its live
results, `nanoda`'s history, and the `releases/v4.33.0` branch. Rocq (§4) was not
re-surveyed. Everything the postmortem asserts was checked against the upstream
artifact rather than taken from the prose; where the two differ, the difference is
recorded at the point of use.

Third pass **2026-08-18**, on the two soundness fixes merged to `master` the day
before and the day of ([#14806](https://github.com/leanprover/lean4/pull/14806),
[#14807](https://github.com/leanprover/lean4/pull/14807)) plus the hardening PR
that accompanies them ([#14808](https://github.com/leanprover/lean4/pull/14808)),
and on the arena's corpus and checker roster, which have both grown
substantially since 08-01. Scope: `leanprover/lean4` issues and PRs since 08-01,
`leanprover/lean-kernel-arena` since 08-10, the two release branches, and a
search of the public discussion — of which, for these two, **there is none**:
no postmortem, no Zulip thread, nothing on X or Mathstodon. The whole public
record is the two PR descriptions, their regression tests, and three arena tests.
Both defects are **live on every released toolchain**, and one of them refutes
this file's own classification of a 2026-07-29 finding (§2.6). Rocq (§4) was not
re-surveyed. Local exhibits verified on Lean `4.33.0` and `4.34.0-rc1`.

---

## 1. The taxonomy: every mechanism, both systems

This is the part that is meant to be complete. A route that is not here is
either unknown to the survey or a special case of one of these.

### 1.1 Assume what the theory withholds — [`Paradoxes/`](Paradoxes/)

The `False` is conditional; the hypothesis is in the statement; the audit is
clean. These are permanent facts about type theory.

| Mechanism | Lean | Rocq | Coverage |
| --- | --- | --- | --- |
| `Type : Type` / a second impredicative sort (Girard 1972, Hurkens 1995) | not expressible as a flag; hypothesised as `pi`/`lam`/`app`/`beta` | stdlib `Hurkens.Generic`, `TypeNeqSmallType`, `PropNeqType` | **artifact** — [`Paradoxes/Lean/…/Girard.lean`](Paradoxes/Lean/TypeTheoryParadoxes/Girard.lean), [`Paradoxes/Coq/Hurkens.v`](Paradoxes/Coq/Hurkens.v) |
| Tarski-style internal universe (`El`/`code` with a section) | `no_internal_universe` | `NoRetractToImpredicativeUniverse` | **artifact** — same files |
| Retract of a large universe into a small one (the general pattern) | — | `NoRetractFromTypeToProp`, `NoRetractFromSmallPropositionToProp`, `NoRetractToModalProposition`, `NoRetractToNegativeProp` | **artifact** (two of six) + **noted** |
| Non-strict positivity (Coquand–Paulin 1990) | `coquand_paulin` | same statement | **artifact** — [`CoquandPaulin.lean`](Paradoxes/Lean/TypeTheoryParadoxes/CoquandPaulin.lean) |
| Negative occurrence (Curry) | kernel refuses; `#guard_msgs`-checked | reachable via a flag, see §1.2 | **artifact** — [`Blockers.lean`](Paradoxes/Lean/TypeTheoryParadoxes/Blockers.lean) §5 |
| Powerset retract (Cantor) | `no_powerset_retract` | `Reynolds.v` in `rocq-archive/paradoxes` | **artifact** (Lean); **noted** (Rocq) |
| Data-carrying elimination out of a proof-relevant `Prop` | `no_large_elim_of_or`, `no_witness_extraction` | refman's `exProp` / `Squash` examples | **artifact** — [`LargeElimination.lean`](Paradoxes/Lean/TypeTheoryParadoxes/LargeElimination.lean) |
| Reynolds 1984 (no set-theoretic model of System F) | not statable — `Type u` is predicative | `Reynolds.v`, refuting `Iinject : Prop → Heyt` | **gap** |
| Burali-Forti (ordinal of ordinals) | Mathlib `ZFSet.isOrdinal_notMem_univ` | `BuraliForti.v` | **gap** |
| Berardi (EM ⟹ proof irrelevance) | harmless; Lean has definitional PI | stdlib `Berardi` — note its only hypothesis is **excluded middle**, not prop-ext | **noted** |
| Diaconescu (choice ⟹ EM) | `Classical.em` in core — a *derivation*, not a paradox | stdlib `Diaconescu` | **noted** |
| Univalence + UIP / Streicher K / `eq_rect_eq` / `JMeq_eq` | inconsistent: `Eq` is a singleton-eliminating `Prop`, so Lean has K outright — and **definitionally**, so univalence alone is refuted, with no UIP hypothesis needed | inconsistent for the *global* axiom; UIP on a decidable type is a theorem (Hedberg, `Eqdep_dec`), so the Rocq statement genuinely needs **both** hypotheses | **artifact**, both systems — [`Univalence.lean`](Paradoxes/Lean/TypeTheoryParadoxes/Univalence.lean) (one hypothesis) and [`UnivalenceUIP.v`](Paradoxes/Coq/UnivalenceUIP.v) (two, with each of Lean's three `rfl`s asserted to *fail* in Rocq) |
| Univalence + unrestricted `LEM∞ := ∀ A, A + ¬A` | — | inconsistent (HoTT book Cor. 3.2.7); LEM for h-props is *consistent* | **gap** |
| Chicli–Pottier–Simpson (proof-relevant quotients + impredicativity) | blocked: `Quot` at `u = 0` is a subsingleton | reachable, see §1.2 | **artifact** (Rocq) |

### 1.2 Use a sanctioned escape hatch — [`EscapeHatches/`](EscapeHatches/)

The `False` is closed, but something discloses the cost.

| Mechanism | System | What the audit says | Coverage |
| --- | --- | --- | --- |
| `sorry` — explicit | Lean | `sorryAx` | **artifact** — [`Sorry.lean`](EscapeHatches/Lean/Sorry.lean) §1 |
| `sorry` — **synthetic**, from a failed tactic or a type error | Lean | `sorryAx`; the declaration still enters the environment | **artifact** — same file §2 |
| `axiom` | Lean | the axiom, by name | **artifact** — [`Axioms.lean`](EscapeHatches/Lean/Axioms.lean) |
| `Admitted` / `Axiom` / `Parameter` / `Hypothesis` / `Conjecture` | Rocq | the assumption, by name. Trap: an `Axiom` inside a `Section` is **not** discharged at `End`, unlike `Variable` | **artifact** — [`Assumptions.v`](EscapeHatches/Coq/Assumptions.v) |
| `Program` + `Admit Obligations` | Rocq | `<name>_obligation_N` | **artifact** — same file |
| `unsafe def f : False := f` | Lean | **blocked by the kernel** at the use site: `(kernel) invalid declaration, it uses unsafe declaration` | **artifact** — [`Unsafe.lean`](EscapeHatches/Lean/Unsafe.lean) §1 |
| `partial def` | Lean | **blocked**: needs `Inhabited`/`Nonempty` of the return type. With a bogus `Nonempty False` axiom it works, and the axiom is reported | **artifact** — same file §2 |
| `unsafeCast` / `lcProof` / `lcCast` / `lcUnreachable` | Lean | `lcProof` is literally `unsafe axiom {α : Prop} : α`. `#print axioms` on an `unsafe` definition using `unsafeCast` reports `[lcProof]`; the kernel gate stops it reaching a theorem | **noted** |
| `@[implemented_by]` + `native_decide` | Lean | a fresh per-use axiom `<thm>._native.native_decide.ax_N_M` (since `v4.29.0`, [RFC #12216](https://github.com/leanprover/lean4/issues/12216)) | **artifact** — [`NativeDecide.lean`](EscapeHatches/Lean/NativeDecide.lean) |
| `@[extern]` + `native_decide` | Lean | same. Needs a shared library, so it is harder to exhibit in one file | **noted** |
| `@[csimp]` + `native_decide` | Lean | **under-reports**: axioms used in the `csimp` proof are not propagated ([lean4#7463](https://github.com/leanprover/lean4/issues/7463), OPEN). Worse, an *honest* `rfl` csimp lemma pointing at an `@[implemented_by]`-replaced constant gives `False` with no extra axiom at all | **noted** |
| `set_option debug.skipKernelTC true` + hand-built `addDecl` | Lean | **nothing.** One of *two* Lean routes invisible to `#print axioms` — the other is the module-boundary stub of §2.1/#14609, which needs no option at all. `leanchecker` rejects both. On the Rocq side the equivalent blind spot is worse: §4.1/#21839 is invisible to `Print Assumptions` **and** to `coqchk`, and escapes through a `Require` | **artifact** — [`Metaprogramming.lean`](EscapeHatches/Lean/Metaprogramming.lean), and used as the control in [`KernelDefects/Lean/Controls/`](KernelDefects/Lean/Controls/) |
| `Unset Guard Checking` / `#[bypass_check(guard)]` | Rocq | `loop is assumed to be guarded.` | **artifact** — [`TypingFlags.v`](EscapeHatches/Coq/TypingFlags.v) §1 |
| `Unset Positivity Checking` / `#[bypass_check(positivity)]` | Rocq | `Curry is assumed to be positive.` | **artifact** — same file §2 |
| `Unset Universe Checking` / `-type-in-type` / `#[bypass_check(universes)]` | Rocq | `… relies on an unsafe hierarchy.` plus, *while the flag is off*, `Theory: Type hierarchy is collapsed` | **artifact** — same file §3–4 |
| `Symbol` + `Rewrite Rule` | Rocq | the symbols, plus `Theory: Rewrite rules are allowed (subject reduction might be broken)`. Confluence and termination are **not checked at all** | **artifact** — [`RewriteRules.v`](EscapeHatches/Coq/RewriteRules.v) |
| `-impredicative-set` + decidability in `Set` | Rocq | `Theory: Set is impredicative`, plus `classic` and `dependent_unique_choice` | **artifact** — [`ImpredicativeSet.v`](EscapeHatches/Coq/ImpredicativeSet.v) |
| `vm_compute` / `native_compute` | Rocq | **nothing.** Both are kernel-level conversion machines, not tactics — they leave a `VMcast`/`NATIVEcast` the *kernel* re-runs at `Qed`, so the trusted base becomes `kernel/byterun/coq_interp.c` or the OCaml native compiler invoked at proof-checking time. **Correction, measured:** the row used to end "Both ignore `Opaque`", which is true of the machines and overstates the consequence. `Opaque` sets a `Conv_oracle` priority that the six reduction *tactics* honour and that conversion never consults, so the sealed goal is closable by plain `reflexivity` anyway. What `vm_compute` defeats is the *displayed* abstraction, not provability — and it is the only one of Rocq's three hiding mechanisms it defeats: `Qed`-opacity and signature ascription hold against it, at tactic and kernel level both, with `Fail` controls | **artifact** — [`EscapeHatches/Coq/ComputeMachines.v`](EscapeHatches/Coq/ComputeMachines.v) |
| `Extraction` with `Extract Constant` | Rocq | nothing; the spliced OCaml *"is currently not checked at all by extraction, even for syntax errors"* | **artifact** — [`EscapeHatches/Coq/ExtractConstant.v`](EscapeHatches/Coq/ExtractConstant.v). Measured: `coqc` exit 0, `Print Assumptions` clean, `coqchk` clean, and the extracted binary disagrees with the Coq theorems 3 times out of 3. Syntactically invalid OCaml and an arity mismatch both survive `coqc` and are caught only by `ocamlc` |
| `Declare ML Module` | Rocq | nothing. Loads OCaml into the kernel's own process | **artifact** — [`EscapeHatches/Coq/DeclareMLModule.v`](EscapeHatches/Coq/DeclareMLModule.v). Measured with shipped plugins; loading a plugin *we wrote* was not achieved on this machine (ABI mismatch with the opam switch's prebuilt binaries) and the file says so. No Lean row exists for this line |
| Tampered or stale `.vo` / `.olean` | both | nothing. Neither system re-typechecks on import | **noted** — [lean4#13615](https://github.com/leanprover/lean4/issues/13615) (closed as by-design); Rocq hardened its `coqchk` path in 8.19 |
| A statement that does not mean what it reads as | both | `Closed under the global context` / no axioms — **correctly** | **artifact** — [`Spoofing.lean`](EscapeHatches/Lean/Spoofing.lean), [`Spoofing.v`](EscapeHatches/Coq/Spoofing.v) |
| An over-general statement (`autoImplicit`, a missing side condition, an instance argument quantifying over all structures) | Lean | nothing | **artifact** — [`Axioms.lean`](EscapeHatches/Lean/Axioms.lean) §4 |

### 1.3 Exploit an implementation defect — [`KernelDefects/`](KernelDefects/)

Closed `False`, clean audit, no flag. Ledgers in §§2–4.

### 1.4 Things commonly believed to be routes, and are not

Worth recording so they are not chased again.

| Claim | Reality |
| --- | --- |
| `Quot.sound` on a non-equivalence relation is unsound | No. `Quot.lift f h` demands `h : ∀ a b, r a b → f a = f b`, and `=` is an equivalence, so anything liftable already respects the equivalence closure of `r`. Carneiro's model interprets `Quot r` as classes of that closure. |
| `partial def` alone gives `False` | No. The `Inhabited` obligation is real and is recorded in the opaque's *value*, so `#print axioms` reports it. |
| `noncomputable` is a soundness device | No. It is a code-generation annotation. |
| `Ltac`/`Ltac2` can produce an ill-typed term | No — `Qed` re-checks the whole term. Even `exact_no_check` and `change_no_check` are caught. |
| `Print Assumptions` is unreliable | Mostly false, and better than its reputation: it reports every `bypass_check` flag by name. Its real blind spots are ML plugins, extraction, `vm_compute`/`native_compute`, notation, and `.vo` provenance — plus two open functor bugs, [#12155](https://github.com/rocq-prover/rocq/issues/12155) and [#16646](https://github.com/rocq-prover/rocq/issues/16646). |
| A sort disagreeing with a reference sort is a library bug | Not necessarily — and this bit during the sweep above. `Array.qsort` takes a **strict** `lt`; passing `≤` violates its precondition and silently yields unsorted output that looks exactly like a defect. `List.mergeSort` takes a non-strict `le`. Using each function's `autoParam` default avoids the trap. No proof depends on the output, so this is a correctness hazard for programs, not a soundness one. |
| Berardi assumes propositional extensionality | No — its only hypothesis is excluded middle. The prop-ext ⟹ proof-irrelevance result is `ClassicalFacts.ext_prop_dep_proof_irrel_cic`. |
| `JMeq_eq` is axiom-free in modern Rocq | No. It is a `Theorem` now, but the file still `Require`s `Eqdep`, so `Print Assumptions` reports `Eqdep.eq_rect_eq`. |
| Univalence rejects classical logic | Only *unrestricted* classical logic. LEM for mere propositions is consistent with univalence (simplicial model). |

---

## 2. Lean 4 — official kernel

Lean 3's record for contrast: *"for the entire release history of Lean 3, there
were no soundness bugs reported against the kernel"*
([Lean4Lean paper](https://arxiv.org/abs/2403.14064)). Lean 4's bugs come almost
entirely from the three kernel *extensions* Lean 3's FAQ told you to disable with
`-t0` — GMP `Nat` arithmetic, structure eta, nested inductives — plus C++
fixed-width integer fields.

### 2.1 Live defects (not fixed as of the survey)

"Live" means *no released toolchain carries the fix*, whether or not `master`
does. **Five** fixes are now `master`-only, and every one of them is an
axiom-free proof of `False` against the current release: three from the July
wave, and two merged on 2026-08-17/18, after `v4.33.0` and `v4.34.0-rc1` were
both cut on 08-10. None is on `releases/v4.33.0` or `releases/v4.34.0` —
checked directly: `src/kernel/equiv_manager.cpp` is still present on both
branches, and `type_checker::is_prop` on both still reads
`whnf(infer_type(e))` with an `is_sort(s) &&` guard.

The August pair share a provenance and a root ingredient. Both were **reported
by Daniel Selsam (OpenAI) using their internal models** — the same source as
#14607–#14616 in July — and both are built on the fact that Lean's `is_def_eq`
is a *sound but incomplete*, hence non-transitive, approximation of a transitive
relation.

| Issue | Defect | Coverage |
| --- | --- | --- |
| [#14806](https://github.com/leanprover/lean4/pull/14806) | **`master`-only fix (2026-08-17); live on every release.** The kernel cached successful `is_def_eq` queries in a **union-find** (`equiv_manager`), consulted whenever two expressions share an `Expr.hash`. Since the implemented `is_def_eq` is incomplete and therefore not transitive, exposing the union-find's transitive closure makes a query's answer depend on which unrelated queries ran earlier. Recursor construction calls `is_def_eq` to decide which constructor fields are recursive, calls it more than once, and assumes a stable answer: a crafted collision makes a K-like reduction fire while the **minor premises** are built and not while the **rules** are, so `Owner.rec`'s `step` premise takes four arguments and its rule supplies three. A `Prop`-valued application then reduces to `Bool`. **`#print axioms` reports nothing.** Two distinct exploits, both produced by an OpenAI agent. This is §2.6's def-eq history dependence, reclassified. | **artifact** ×2 + **report** — [`DefEq/EquivManagerMissingIH.lean`](KernelDefects/Lean/DefEq/EquivManagerMissingIH.lean), [`DefEq/EquivManagerStuckSort.lean`](KernelDefects/Lean/DefEq/EquivManagerStuckSort.lean), [`Reports/2026-08-18-defeq-…`](Reports/2026-08-18-defeq-cache-and-stuck-sort.md). **Verified here** on `v4.33.0` and `v4.34.0-rc1`; controls rejected on both |
| [#14807](https://github.com/leanprover/lean4/pull/14807) | **`master`-only fix (2026-08-18); live on every release.** `type_checker::is_prop` computed `whnf(infer_type(e))` and returned `false` when the result was a **stuck term rather than a sort** — but `false` means "not a proposition", so `infer_proj` skipped its proof-irrelevance guard and let a data field out of a proof. A value whose type does not reduce to a sort is ill-formed and should be *rejected*, not answered about; the fix uses `ensure_sort`. **The second distinct way `is_prop` has been found wrong in three weeks**, after #14613's syntactic sort comparison — same six lines of code, one `False` each, and #14613 is *also* still live. The sharpest witness needs nothing from #14806's cache: `P := a = b` and `Q := a = c` are definitionally equal types whose proofs behave differently under K-like reduction, so an inductive family declared over `P` is a family of propositions while its instance at a proof of `Q` has a sort that does not reduce. **Also accepted by `nanoda`** — §3.0 happening a second time. `lean4lean` never had it: its `isProp` already used `ensureSortCore`. | **artifact** + **report** — [`DefEq/SubstStuckSort.lean`](KernelDefects/Lean/DefEq/SubstStuckSort.lean), [`Reports/2026-08-18-defeq-…`](Reports/2026-08-18-defeq-cache-and-stuck-sort.md). **Verified here** on `v4.33.0` and `v4.34.0-rc1`; control rejected on both |
| [#14609](https://github.com/leanprover/lean4/pull/14609) | **`master`-only fix; live on every release.** A `module` publishes a definition whose body stays private as an axiom stub, and `addDeclCore` (`src/Lean/AddDecl.lean:118`) built it with `isUnsafe := defn.safety == .unsafe` — false for `.partial`. The kernel accepts a `partial` definition of type `False` (a `partial` mutual block has no inhabitance obligation), the boundary launders it into a *safe* axiom, and both of `infer_constant`'s gates miss: the first because `is_unsafe()` says false, the second because it inspects definitions and a stub is an axiom. **`#print axioms` reports nothing**; `leanchecker` rejects. Not a `src/kernel/` defect, which is why §5.2's first pass missed it. | **artifact** + **report** — [`ModuleSystem/`](KernelDefects/Lean/ModuleSystem/), [`Reports/2026-08-01-module-boundary-…`](Reports/2026-08-01-module-boundary-partial-stub.md). **Verified here** on `v4.27.0-rc1` … `v4.33.0-rc1`; control rejected and `leanchecker` rejects on all of them |
| [#14613](https://github.com/leanprover/lean4/pull/14613) | **`master`-only fix; live on every release.** `type_checker::is_prop` compares `whnf(infer_type(e))` against `Prop` syntactically, so `Sort (imax 1 0)` — which denotes `Prop` — is a proposition for proof irrelevance and not one for `infer_proj`'s field restriction. Projecting a `Bool` out of two proofs of it gives `false = true`. See §2.2 for the fix and §2.6 for the *second* weakness the reproducer needs. | **artifact** + **report** — [`Universes/ImaxPropLaundering.lean`](KernelDefects/Lean/Universes/ImaxPropLaundering.lean), [`Reports/2026-08-01-imax-prop-…`](Reports/2026-08-01-imax-prop-laundering.md). **Verified here** on `v4.27.0-rc1` … `v4.33.0-rc1`; control rejected on all of them |
| [#14616](https://github.com/leanprover/lean4/pull/14616) | **`master`-only fix; live on every release.** An inductive declaration may name one of the kernel's transient `_nested` auxiliary types, and `restore_nested` then rewrites the name back to a type in a different universe, leaving a stored constructor that is ill typed; `equiv_manager` closes the consequences transitively. Cannot be captured as an arena export test, so **no artifact exists anywhere**. | **gap** — the highest-value remaining item in §5 |
| [#14582](https://github.com/leanprover/lean4/pull/14582) | **The live one.** Follow-up to #14577 by Arthur Adjedj: a datatype being declared can occur applied to arguments that are *not* the parameters of the mutual declaration, hidden in the parametric arguments of a nested inductive, which are dropped from the generated auxiliary declaration and so escape type checking. Adds `check_uniform_params`. The FRO's own framing: it makes the kernel *"check that the parameters of a nested occurrence actually behave as parameters, rather than only re-type-checking them"* (§6 postmortem). **OPEN as of 2026-08-01.** | **noted** — now an arena test, §3.1 `nested-nonuniform-param` |
| [#12746](https://github.com/leanprover/lean4/issues/12746) | `Expr.proj` indices narrowed `size_t`→C++ `unsigned` in `infer_proj`, `reduce_proj`, `lazy_delta_proj_reduction`, guarded only by `is_small()` (`< 2^63`, not `< 2^32`). Index `2^32 + k` silently becomes `k`. Not a `False` by itself — truncation is consistent, and a collision needs a structure with 2^32 fields. [#13602](https://github.com/leanprover/lean4/issues/13602) is the same defect reported *with* an axiom-free accepted theorem, closed as a duplicate. **Fixed on `master` 2026-08-01 by [#14632](https://github.com/leanprover/lean4/pull/14632)** (`to_proj_idx`, §2.5); the issue is still OPEN and unlabelled-as-fixed, and no released toolchain carries the fix. | **artifact** — [`Projections/ProjIndexTruncation.lean`](KernelDefects/Lean/Projections/ProjIndexTruncation.lean). **Verified here** present on `v4.32.0`, `v4.32.2`, `v4.33.0-rc1`; control rejected on all three. The artifact keeps its value as the regression witness — re-run it on the first release after `v4.33` and it should flip. |
| [#12747](https://github.com/leanprover/lean4/issues/12747) | `Level.normalize` does not canonicalize when an `imax` collapses to a `max`. **Incompleteness, not unsoundness.** OPEN, `P-low`. | **artifact** (as incompleteness) — [`DefEq/LevelNormalizeIncomplete.lean`](KernelDefects/Lean/DefEq/LevelNormalizeIncomplete.lean). **Verified here** on `v4.32.0`. |
| [#7637](https://github.com/leanprover/lean4/issues/7637) | Primitive projections are not conservative over recursors. OPEN. | **artifact** — [`Audits/Lean/Metatheory/ProjBeyondRecursor.lean`](Audits/Lean/Metatheory/ProjBeyondRecursor.lean), which reaches the same conclusion independently |
| [#8982](https://github.com/leanprover/lean4/issues/8982) | An unsound `unif_hint` makes everything defeq and crashes Lean. Elaborator-level. OPEN; fix PR #8988 unmerged. | **gap** |
| [#7463](https://github.com/leanprover/lean4/issues/7463) | `@[csimp]` does not propagate axioms used in its proof through `native_decide`. OPEN, `P-low`. | **noted** — §1.2 |
| [#10760](https://github.com/leanprover/lean4/issues/10760) | Visibility of section variables not verified correctly under the module system. OPEN. | **gap** |

### 2.2 Fixed defects that yielded an axiom-free `False`

Chronological. Every one of these was accepted by the *checked* kernel.

| Issue / PR | Defect | Fixed |
| --- | --- | --- |
| [#1433](https://github.com/leanprover/lean4/issues/1433) | `lean_nat_mod` truncates `size_t`→`unsigned`, so `2^65 % (2^33+1)` reduces to `1`. **Proof of `False` by plain `rfl`** — no metaprogramming, no `native_decide`. | same day, 2022-08-06 |
| [#1781](https://github.com/leanprover/lean4/pull/1781) | `imax u v + N` normalized to `imax u v` regardless of `N`. Title is literally *"fix: bug in level normalization (soundness bug)"*. Does not exist in Lean 3. | 2022-10-26 |
| [#2125](https://github.com/leanprover/lean4/issues/2125) | Self-referential index: `inductive C : Bool → Type | c : C (f (C false))` with `f α := Nonempty α`. **The only one exploitable from plain surface Lean.** Lean 3 had this check; Lean 4 lost it. | next day, 2023-02-28 |
| [#8060](https://github.com/leanprover/lean4/pull/8060) | `reduce_pow` interpreted an expression as an `mpz` without checking it was a `Nat` literal. Found by fuzzing with GMP and mimalloc disabled. | 2025-04-23 |
| [#8554](https://github.com/leanprover/lean4/pull/8554) family | `Expr.Data`/`Level.Data` overflow handled by `panic!`, which **does not abort** — execution continued with the field's default `0`, so `hasFVar`, `hasMVar`, `hasLevelParam`, `hasLooseBVars` all stopped being conservative. Found by Carneiro *via lean4lean*, by failing to prove a theorem and working backwards. #8554 closed unmerged; fixed by [#8559](https://github.com/leanprover/lean4/pull/8559)/[#8560](https://github.com/leanprover/lean4/pull/8560). | 2025-05-31 |
| [#14484](https://github.com/leanprover/lean4/issues/14484) | The checked `Declaration.opaqueDecl` path did not reject free variables in the body; with the inference cache, a safe metaprogram adds an opaque `False` whose value is an unbound fvar. | 2026-07-22, `v4.32.1` |
| [#14576](https://github.com/leanprover/lean4/issues/14576) | Nested-inductive parametric arguments substituted **without being type-checked**; a wrong-structure projection hidden behind a deliberate `Expr.hash` + `approxDepth` collision. Parameters that are *phantom* — not mentioned in any constructor field — vanish from the generated auxiliary type and so are never seen. **Exploitable even through `comparator`** — the release notes say so. Provenance, from the postmortem: Ramana Kumar published a `sorry`-free AI-assisted "disproof" of the Collatz conjecture on **2026-07-25**; Kiran Gopinathan reduced it to a small `False` and filed the issue on **07-28**; #14577 was pushed **one hour** later and reviewed by Joachim Breitner. (The original repository, [`xrchz/collatzlean`](https://github.com/xrchz/collatzlean), is named not by the postmortem but by the arena test's `origin` field.) | 2026-07-28, `v4.32.2` |
| [#14613](https://github.com/leanprover/lean4/pull/14613) | `type_checker::is_prop` compared `whnf(infer_type(e))` against `Prop` **syntactically**. `Sort (imax 1 0)` really *is* a proposition, so proof irrelevance applies — but `is_prop` said no, and `infer_proj` skipped its `Prop` restriction, letting a `Bool` be projected out of a proof. **Live on every released toolchain** through `v4.33.0-rc1`; see §2.1. | 2026-07-31 (`master` only) |
| [#14616](https://github.com/leanprover/lean4/pull/14616) | A declaration naming one of the kernel's `_nested` auxiliary types: `restore_nested` can hand a stored constructor a type in a *different universe* than it was checked against. Notable because it **cannot be captured as an arena export test** — the exploit depends on transient `equiv_manager` state. | 2026-07-31 |
| [#14607](https://github.com/leanprover/lean4/pull/14607) | Missing `check_no_metavar_no_fvar` in `inductive.cpp`: nested inductive declarations containing fvars/mvars. | 2026-07-30 |
| [#14608](https://github.com/leanprover/lean4/pull/14608) | The kernel did not check that declarations in a `mutual` block use the same universe parameters. | 2026-07-30 |
| [#14609](https://github.com/leanprover/lean4/pull/14609) | Module system: an exported definition's axiom stub computed `isUnsafe` as `defn.safety == .unsafe`, which is **false for `.partial`** — so a `partial def` crossed a module boundary as an ordinary *safe* axiom. **Live on every released toolchain**; see §2.1. | 2026-07-30 (`master` only) |

**Only two releases in Lean 4's history were cut specifically for kernel
soundness: `v4.32.1` and `v4.32.2`, eight days apart in July 2026.**

**Every defect in the July 2026 wave is reachable only through metaprogramming** —
by handing a declaration to the kernel directly, past a frontend that would have
caught it. The postmortem states this of #14576 and of #14607–#14616; for #14484
it is this repo's own measurement
([`Reports/2026-07-29-lean-4.33-…`](Reports/2026-07-29-lean-4.33-backport-gap.md),
"Scope"), not something upstream says. It is *not* a mitigation, and the postmortem is
unusually direct about why: the elaborator is untrusted by design, an attacker
can write `.olean` files or modify memory instead, and *"soundness cannot depend
on an untrusted component refusing to build a bad term."* The two counterexamples
in the table above are the ones worth remembering for contrast — #1433 is a plain
`rfl` and #2125 is ordinary surface syntax.

Two further kernel bugs found by lean4lean verification with no demonstrated
exploit: [#10475](https://github.com/leanprover/lean4/issues/10475) (`infer_let`
ignores dependencies in a let-binding's *type*, so `Kernel.check` returns an
expression with a loose fvar) and
[#10492](https://github.com/leanprover/lean4/issues/10492). Plus
[#10577](https://github.com/leanprover/lean4/issues/10577) (uninitialized memory
in `lazy_delta_reduction_step`, found by fuzzing) and
[#8695](https://github.com/leanprover/lean4/issues/8695) (a constructor named
`I.rec` silently **overwrites** the recursor).

### 2.3 Out-of-scope by upstream policy

| Issue | Substance | Resolution |
| --- | --- | --- |
| [#13626](https://github.com/leanprover/lean4/issues/13626) | A `prelude` module defining its own `Bool` plus the free name `Lean.reduceBool` gets the kernel to accept `Eq (Lean.reduceBool t) Bool.false`. Exactly the mechanism of our `ReduceBoolFreeName.lean`, independently reported 2026-05-03. | Closed 2026-05-04 as **working-as-intended**. |

This is the authoritative upstream position on the **entire accelerator family**
in [`KernelDefects/Lean/Accelerators/`](KernelDefects/Lean/Accelerators/) — the
`Nat` accelerators, the free-name variants, `Lean.reduceBool`, and
`StringLitFabrication`. Every one is a `prelude` module, so the policy covers
them, and the family is **not** going to be fixed. `lean4lean` documents the same
assumption from the other side in
[`divergences.md`](https://github.com/digama0/lean4lean/blob/master/divergences.md).

### 2.4 Compiler / `native_decide` trust-base defects (not kernel bugs)

Each yields `False` via `native_decide`, and each is a divergence *in Lean core*
between a reference implementation and its compiled counterpart — so the bug
does not have to be yours. Coverage: **noted** for all.

| Issue | Substance | Fixed |
| --- | --- | --- |
| [#1825](https://github.com/leanprover/lean4/issues/1825) | `mpz` integer overflows | `v4.0.0` |
| [#4306](https://github.com/leanprover/lean4/issues/4306) | `UIntN.toNat` constant folding without modular reduction | 2024-05-30 |
| [#5818](https://github.com/leanprover/lean4/issues/5818) | `UInt64.modn` miscompilation | 2024-10-23 |
| [#6086](https://github.com/leanprover/lean4/issues/6086) | `Nat.ble 0 0 = false` | same day, 2024-11-15 |
| [#10213](https://github.com/leanprover/lean4/issues/10213) | `@[csimp]` ignored universe parameters — the demo overrides `Classical.choice` | 2025-09-02 |
| [#11773](https://github.com/leanprover/lean4/issues/11773) | `Array.foldlM` vs `foldlMUnsafe` disagree on an out-of-range `stop` | 2025-12-22 |
| [#8840](https://github.com/leanprover/lean4/issues/8840) | **Trust-accounting bug**: `collectAxioms` did not collect axioms referenced by *other* axioms, so a `native_decide` proof did not report `Lean.trustCompiler`. `#print axioms` was itself under-reporting the TCB. | 2025-06-17 |

Historical, and the ancestor of the whole family: the **2023 `native_decide`
leakage**. `Lean.reduceBool` ran compiled code, and compiled code could be
nondeterministic — a definition calling `IO.getRandomBytes` gave `rfl` proofs of
both `Lean.reduceBool foo = false` and `= true`, combined by `nomatch` into
`False`, with `#print axioms` reporting **nothing**. Root cause: `IO.RealWorld`
was not opaque, so several "real worlds" could coexist. Demonstrated by Mario
Carneiro; fixed by [PR #2654](https://github.com/leanprover/lean4/pull/2654) in
`v4.2.0-rc2`. `lean4checker` never accepted these proofs, having no compiled-code
support. Coverage: **noted**; the descendant mechanism is
[`ReduceBoolFreeName.lean`](KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean).

### 2.5 Hardening fixes (defensive, no published derivation of `False`)

Two waves. Coverage: **noted** for all.

**May 2026**, closed 2026-05-03/04 after a systematic audit sweep. The recurring
theme is that `lean_assert`/`assert!`/`panic!` are debug-only or non-aborting, so
every "guarded" invariant is unguarded in a release build.

| Issue | Substance |
| --- | --- |
| [#13615](https://github.com/leanprover/lean4/issues/13615) | `.olean` files lack integrity checks and bypass kernel type checking on import |
| [#13616](https://github.com/leanprover/lean4/issues/13616) | `declaration.h` getters call `get_small_value()` without an `is_small()` guard (13 sites) |
| [#13617](https://github.com/leanprover/lean4/issues/13617) | `compacted_region::read()` deserialization memory-corruption vectors |
| [#13618](https://github.com/leanprover/lean4/issues/13618) | `nparams + idx` unsigned wraparound in `reduce_proj_core` — duplicate of the #12746 family |
| [#13619](https://github.com/leanprover/lean4/issues/13619) | integer overflow in the `.olean` deserializer's byte-size functions |
| [#13620](https://github.com/leanprover/lean4/issues/13620) | `cheap_beta_reduce` unsigned underflow when `bvar_idx >= i` |

**July–August 2026**, the tail of the #14576 response. Named in the postmortem
(§6); each verified merged here on 2026-08-01. The theme has changed: these take
an invariant the kernel already relies on somewhere else and check it *locally*,
so that a future mistake nearby surfaces as an error instead of being amplified.

| PR | Substance | Merged |
| --- | --- | --- |
| [#14615](https://github.com/leanprover/lean4/pull/14615) | The inductive checker now tests a resulting universe for zero **up to normalization**, so `Sort (imax 1 0)` and `Sort 0` describe the same inductive type. The two spellings previously disagreed on whether a constructor field may carry data, on whether the recursor eliminates only into `Prop`, and on whether the type is a K-like reduction target. **Widens** what the kernel accepts and is explicitly *not* a soundness fix — every syntactic test erred in the restrictive direction. **Refinement measured here (§2.6):** restrictive *per mutual block*, not per type. `m_result_level` is the block's **first** type's spelling, so the permission a syntactic `Sort 0` earns is inherited by a later type spelled `Sort (imax 1 0)` — and that inheritance is what gets #14613's payload past a released kernel, which rejects the same type declared alone. Its actual content is a **kernel/`nanoda` divergence**: `nanoda` decides all three semantically and derives recursors rather than trusting the export, so it rejected exports the kernel accepted. **Measured here** ([`Audits/Lean/Checkers/`](Audits/Lean/Checkers/)) rather than cited: `nanoda` 0.4.10-beta rejects both the honest `Sort 0` and the laundered `Sort (imax 1 0)` spelling with the same `infer_proj prop`, while accepting a control — so the cross-check does hold on the construction §2.1/#14613 exploits. Same `imax 1 0` surface as #14613, opposite direction. | 2026-07-31 |
| [#14621](https://github.com/leanprover/lean4/pull/14621) | The kernel re-checks the declarations it adds after eliminating a nested inductive. Redundant by construction; a backstop in case the nested-inductive code is still missing a validation. §5.1 records this repo's attempt to exercise it from inside Lean, and why that cannot be done. | 2026-07-31 |
| [#14631](https://github.com/leanprover/lean4/pull/14631) | `type_checker::is_def_eq_core` and `equiv_manager::is_equiv_core` compared only the projection index and the projected expression, **ignoring `proj_sname`**. Not exploitable: `infer_proj` rejects a structure name disagreeing with the projected expression's type, and kernel-built projections always carry the right one, so two projections reaching def-eq can differ on the name only if one is ill-typed. Turns that global invariant into a local one. Two reasons it matters here — it edits the exact function analysed in [`Reports/2026-07-29-defeq-…`](Reports/2026-07-29-defeq-history-dependence.md), and it is the *same omission* as the `nanoda` bug of §3.0. | 2026-08-01 |
| [#14632](https://github.com/leanprover/lean4/pull/14632) | A five-part hardening pass. **One part is #12746**: projection indices are now rejected unless they fit the width the kernel consumes them at — the new `to_proj_idx` helper adds the `> UINT_MAX` bound the `is_small()` guard never had, in both `infer_proj` and `reduce_proj`, with a comment naming `.proj S 2^32 c` → `.proj S 0 c` as the failure mode. Also: `add_quot` now checks `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` are undeclared instead of inserting over whatever holds those names (*"which only a module replacing the prelude can arrange"* — the §2.3 precondition exactly); `reduce_proj_core` takes the structure name and refuses a constructor of any other inductive; `add_mutual` rejects a block declaring the same name twice, where the old check saw only the pre-existing environment; and the nested-restoration `lean_assert`s become kernel exceptions, since in a release build they vanish. | 2026-08-01 |
| [#14633](https://github.com/leanprover/lean4/pull/14633) | `infer_lambda` and `infer_let` now check a binder's type — and for `let`, its value — *before* adding the declaration to the local context, which is what `infer_pi` already did. *"No valid declaration changes behavior."* **Not in the postmortem**, which was published earlier the same day; found by reading the log at the pinned [`Upstream/lean4`](Upstream/lean4) commit. Adjacent to the local-context anomaly in §5.1's closing paragraph, though not the same thing: that one is about a caller-supplied `_kernel_fresh.N` fvar being captured, not about the order of checking and extending. | 2026-08-01 |

**August 2026**, alongside §2.1's #14806/#14807. One PR, and it belongs in this
section rather than that one because it changes nothing about what the kernel
accepts for well-formed input.

| PR | Substance | Merged |
| --- | --- | --- |
| [#14808](https://github.com/leanprover/lean4/pull/14808) | When the kernel generates a recursor it installs it and its computation rules with `add_core`, which **does not re-check them** — the surrounding machinery was trusted to produce something consistent. This adds a verification pass: the recursor's type is type-checked, and each computation rule is checked to be *type-preserving*, by reducing the recursor applied to each constructor one step and comparing the reduct's type against the un-reduced application's. The commit message states the reason the weaker check would not do, and it is the interesting part: checking only that a rule's right-hand side *has some type* is insufficient, because an **under-applied minor premise is still a well-typed function term** — which is exactly the shape #14806's first exploit produces. Same family as [`Audits/Lean/Nested/IllTypedStoredConstructor.lean`](Audits/Lean/Nested/IllTypedStoredConstructor.lean) and as #14621: a declaration the kernel stores unchecked because whoever produced it was trusted. `master`-only; no released toolchain has it either. | 2026-08-18 |

### 2.6 Findings originating in this repository

| Finding | Nature | Coverage |
| --- | --- | --- |
| `Nat` accelerator family (`Nat.add`, `Nat.beq`, and the nine free names under `Init.Prelude`) | Kernel normalizer extensions keyed on *names only*, tried before delta-reduction; two disagreeing reduction rules give `False`. Out of scope upstream per §2.3. | **artifact** + **report** — [`Reports/2026-07-28-…`](Reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md) |
| `StringLitFabrication` | Expanding a *string literal* makes the kernel assemble a term by name and hand it to a recursor rule **without type-checking it**, fabricating an inhabitant of `Empty`. The most severe failure mode of the family. | **artifact** |
| Comparator `accepted/` | [`leanprover/comparator`](https://github.com/leanprover/comparator) checks only that challenge and solution *agree* on kernel primitives, never that the primitives are genuine; a challenge that does not import `Init` gets no protection. | **artifact** — [`Comparator/`](KernelDefects/Lean/Comparator/) |
| Def-eq history dependence — **classified wrongly here, corrected 2026-08-18** | `equiv_manager`'s union-find turns the non-transitive def-eq relation into its transitive closure, consulted whenever two expressions share a 32-bit `Expr.hash`. Filed 2026-07-29 as **"not unsoundness"**, on the argument that every link is individually valid and that closing a semantically valid relation stays valid. Both premises are true and the conclusion is false: [#14806](https://github.com/leanprover/lean4/pull/14806) fixes this mechanism as a soundness bug with two `False`s attached. What the closure changes is not what is *stored* but the **verdict** `is_def_eq` returns, and recursor construction reads that verdict to make a structural decision, twice, assuming stability. The report's closing section searched for a `False` among the terms the cache *relates* and correctly found none — the exploits export no equation at all, they let the cache change a decision about a *declaration*. The search was aimed one level below the defect. Both files now carry the correction, and the measurement itself is unchanged: it is what §2.1's two exhibits are built on. | **artifact** + **report** — [`Reports/2026-07-29-defeq-…`](Reports/2026-07-29-defeq-history-dependence.md), superseded by [`Reports/2026-08-18-defeq-…`](Reports/2026-08-18-defeq-cache-and-stuck-sort.md) |
| `Nat.shiftLeft` kernel abort | `reduce_nat` bounds `Nat.pow`'s exponent (`ReducePowMaxExp`) and declines gracefully above it, but applies no bound to `Nat.shiftLeft`; `lean_nat_shiftl` calls `lean_internal_panic` above `UINT_MAX`. `example : (1 : Nat) <<< 4294967296 = 0 := rfl` aborts `lean` (exit 1, uncatchable) on `v4.31.0` through `v4.33.0-rc1`, under `--trust=0`, from one line of ordinary source. **Robustness, not unsoundness** — the process dies rather than continuing with a wrong value. | **report** — [`Reports/2026-07-31-kernel-shiftleft-panic.md`](Reports/2026-07-31-kernel-shiftleft-panic.md); harness [`Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean`](Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean) |
| `v4.33.0-rc1` backport gap, **twice** | The 4.33 branch was cut before #14484 and #14576 landed and neither was cherry-picked, so the release candidate accepts both proofs of `False`. Both were later cherry-picked onto `releases/v4.33.0` — and then the same thing happened again with #14613/#14615/#14616, which merged to `master` on 07-31, three days after that branch's HEAD, and are still not on it. A recurrence four days after the first was recorded as resolved. | **report** — [`Reports/2026-07-29-lean-4.33-…`](Reports/2026-07-29-lean-4.33-backport-gap.md) |
| **Mutual-block result-level laundering** | `check_inductive_types` (inductive.cpp:248) sets `m_result_level` from the **first** type of a mutual block and requires the others only to be `is_equivalent`; every downstream gate reads that one spelling. So the data-field permission that `check_constructors` grants a syntactic `Sort 0` is inherited by a type whose own sort is spelled `Sort (imax 1 0)` or `Sort (max 0 0)`, purely by declaring it *second*. Reversing the two types rejects the same block, which is what pins it on "first" rather than "some". This is the step that gets #14613's payload past a released kernel at all, and upstream's fix and regression test do not mention it: **it is unchanged on `master`**, harmless there only because #14613/#14615 made every consumer of `m_result_level` semantic in the same wave. Refines §2.5's note on #14615 — the syntactic test erred restrictively *per block*, not per type. | **artifact** + **report** — [`Universes/MutualResultLevel.lean`](KernelDefects/Lean/Universes/MutualResultLevel.lean), [`Reports/2026-08-01-imax-prop-…`](Reports/2026-08-01-imax-prop-laundering.md) |
| `Sort (max 0 0)` as a second member of the #14613 class | Upstream's commit message and its regression test `tests/elab/kernelImaxProp.lean` name only `imax 1 0`. `is_zero` is `kind() == Zero`, so the class is *every* spelling of zero that is not literally `Level.zero`; `max 0 0` gives its own axiom-free `False` by the same route. Does not affect the fix — `normalizes_to_zero` is semantic and closes the whole class at once. | **artifact** — second half of [`Universes/ImaxPropLaundering.lean`](KernelDefects/Lean/Universes/ImaxPropLaundering.lean) |
| **A module boundary loses `partial`, and `#print axioms` cannot see it** | The exported-stub defect of #14609, reproduced as a two-module Lake package: a safe `theorem Paradox : False`, `#print axioms` clean, on every released toolchain. Two things beyond the upstream fix: the audit is **blind** to it, which makes it the second Lean route invisible to `#print axioms` after `debug.skipKernelTC` (§1.2) and the first that needs no option; and `leanchecker` **rejects** it, unlike every other exhibit in [`KernelDefects/Lean/`](KernelDefects/Lean/) — because this defect is in the frontend rather than in the kernel `leanchecker` shares. Found by mining [`Reports/Counterexamples/`](Reports/Counterexamples/) — it is that book's *Privacy violation* verbatim: a property checked against a local view, and a lossy summary across a boundary that drops it. | **artifact** + **report** — [`ModuleSystem/`](KernelDefects/Lean/ModuleSystem/), [`Reports/2026-08-01-module-boundary-…`](Reports/2026-08-01-module-boundary-partial-stub.md) |
| **Correction to this file's own sweep method** | The 2026-08-01 pass scoped itself to `git diff v4.32.2..master -- src/kernel/`, on the theory that this gives the exact set of checks the shipped kernels lack. It does, and that is the flaw: #14609 is a `src/Lean/` fix, so the diff was structurally unable to see it, and §6 said two of the July wave's `False`s were unreleased when the answer is three. The corrected sweep searches the range by commit message with no path filter (§5.2). The general lesson is the one #14609 illustrates: **soundness is not a property of `src/kernel/`** — the kernel's gates were right throughout; the frontend's *summary* of a declaration was wrong. | **report** — [`Reports/2026-08-01-module-boundary-…`](Reports/2026-08-01-module-boundary-partial-stub.md) |
| **The released kernel is blind to `proj_sname` in three places, not one** | §2.5 records #14631 as turning a global invariant into a local one at `is_def_eq_core` and `equiv_manager::is_equiv_core`, and #14632 as adding the structure name to `reduce_proj_core`. All three are `master`-only, so a released kernel is blind at all three at once, and the blindness is total: `whnf (.proj T 0 (S.mk 5 true))` is `5` where `T.x : Bool`, and `.proj S 0 h =?= .proj T 0 h` is `true` both closed and open. These are two of the three primitives #14616's own commit message says its exploit is built from. What holds the line is `infer_proj`, exactly as §2.5 says — and the measurement is that nothing else does, *and that it only holds in one traversal mode*: `infer_app` (type_checker.cpp:163) infers its argument only when `infer_only` is false, and `whnf` infers in `infer_only` mode. Measured: `Kernel.check (id Nat <bad proj>)` is rejected while `Kernel.whnf` of the same term reduces to `5` without the guard ever running. So "every projection is inferred" is a property of one traversal, not of the kernel. The remaining margin is declaration *ordering*: within a checked `addDecl` the only place a release stores an unchecked term is `restore_nested`'s output (`debug.skipKernelTC` and `.olean` import are §1.2 escape hatches, not this), and a projection naming a `_nested` auxiliary cannot be written because that auxiliary's constructor is not declared while constructors are being checked. Ordering is not a soundness check, which is why #14621's re-check matters on the release line. | **artifact** — [`Audits/Lean/Projections/ProjSnameBlindness.lean`](Audits/Lean/Projections/ProjSnameBlindness.lean) |
| **Strict positivity depends on which bodies are visible** | The sharpest statement of the row below, and it needs no metaprogramming at all. Because `check_positivity` starts `t = whnf(t)`, `inductive Bad1 \| mk : IgnoreD (Bad1 → False) → Bad1` — the declared type in a **negative** position — is *accepted* when `IgnoreD`'s body is visible and *refused* when it is `opaque`, on every released toolchain. So strict positivity is a property of the declaration **plus the ambient set of unfoldable bodies**, and an abstraction boundary changes the answer. Inert (`IgnoreD X` is definitionally `True`), but it is Dolan's *A little knowledge…* — exposing an implementation should never change what typechecks — with the violation in the direction where more knowledge means a weaker check. | **artifact** — [`Audits/Lean/Positivity/VisibilityDependentPositivity.lean`](Audits/Lean/Positivity/VisibilityDependentPositivity.lean) |
| **`check_positivity`'s leading `whnf` erases occurrences it then does not check** | `check_positivity` (inductive.cpp:452) starts `t = whnf(t)` and returns at its first branch when the reduced form has no occurrence of the types being declared — but the kernel stores the **unreduced** type, and `restore_nested` rewrites `_nested` occurrences inside it. Hiding the auxiliary behind `def Ignore (_ : Prop) : Prop := True` therefore walks past the only gate on the safe path. Result: a **safe**, axiom-free module, `lean --trust=0` exit 0, `#print axioms` clean, that makes every released kernel store three constants its own `Kernel.check` rejects — `B.node`, `B.rec`, and `B.rec`'s computation rule. Not a `False`: `Ignore X` is definitionally `True` whichever argument it holds, so every use reduces past the ill-typed application. `master` rejects the declaration up front (#14616's `check_no_nested_aux`), so this is a route on the release line rather than a new `master` defect — and it is a concrete case where #14621's re-check, whose own comment calls it "not necessary", would fire. | **artifact** + **report** — [`Audits/Lean/Nested/IllTypedStoredConstructor.lean`](Audits/Lean/Nested/IllTypedStoredConstructor.lean), [`Reports/2026-08-01-positivity-whnf-…`](Reports/2026-08-01-positivity-whnf-erasure.md) |
| `is_not_zero` differential sweep | `is_not_zero` is the one level predicate the July 2026 wave did **not** convert to a semantic test, and it is read *before* the "mutual ⟹ `Prop`-only" and "more than one constructor ⟹ `Prop`-only" branches of `elim_only_at_universe_zero` — so a false positive there hands an inductive predicate a data-eliminating recursor. Fuzzed through the observable channel (declare a 2-constructor inductive at the level, read whether the recursor gained an elimination universe) against the denotational "can this level be zero?". 360 level spellings to depth 3, 91 large-eliminating: **0 unsound**. | **negative result** — [`Audits/Lean/Fuzz/IsNotZeroFuzzer.lean`](Audits/Lean/Fuzz/IsNotZeroFuzzer.lean) |

---

## 3. Lean — non-official kernels and the Arena

[`leanprover/lean-kernel-arena`](https://github.com/leanprover/lean-kernel-arena)
(results at [arena.lean-lang.org](https://arena.lean-lang.org/), maintained by
Joachim Breitner) is now **the definitive catalog of kernel attacks**: a
CI-driven differential-testing harness running a standard corpus of
`lean4export` NDJSON test cases against every registered checker. This is de
Moura's *Who Watches the Provers?* argument made operational.

Coverage: **gap** for the entire section. None of these is reproduced here, and
the whole corpus is the single largest outstanding item in this catalog.

### 3.0 The one time cross-checking nearly failed

The single most useful thing in the #14576 postmortem, and the reason §3 is worth
reading before §2. The Collatz repository did not only pass the official kernel —
**it also passed a week-old `nanoda`**, the main external checker. Two *unrelated*
bugs were required:

* the official kernel never checked the phantom parameters of a nested occurrence
  at all (#14576), and
* `nanoda` did check that spot, but **did not verify the type name in a projection
  node**.

The payload is a wrong-structure projection, so it had to sit somewhere the kernel
never inspects *and* be something the old `nanoda` would wave through. It was.
`nanoda`'s bug was reported by Jeremy Chen and fixed before the Lean bug was
reported — the fix is [`nanoda_lib`#22](https://github.com/ammkrn/nanoda_lib/pull/22),
*"more strict/nuanced handling for structure/proj interactions"*, merged
**2026-07-27**. (The postmortem says "a week before"; the merge is one day before
the 07-28 issue. The exact interval is worth pinning down, because the interval
*is* the story.) Ramana Kumar believes the timing was coincidental but cannot rule
out that the model had seen the `nanoda` report; Joachim Breitner's alternative is
that the coincidence is just what a supply of strong models looks like.

The FRO's conclusion is the honest one and worth quoting rather than paraphrasing:
checking with an independent kernel **still works**, since defeating it took two
distinct bugs in two implementations — but users who rely on it *"need current
versions of both."*

**The sharper reading, for this catalog.** The two bugs were unrelated in
provenance but not in *kind*. Both are the same omission — a projection's
structure name going unverified — in two different places. The kernel's own
remaining instance of it was closed on 2026-08-01 by #14631 (§2.5), which
compared projections for definitional equality while ignoring `proj_sname`. The
asymmetry matters and should not be smoothed over: `nanoda`'s omission was
load-bearing for its verdict, while the kernel's was not exploitable, because
`infer_proj` had already rejected mismatched names on the paths that reach it.
But the shape is the same, and the moral is that **independence of implementations
is not independence of blind spots.** A checker written against the same
specification tends to skip the same checks.

`lean4lean` is the clearest case: the postmortem states it is affected by the
#14576 kernel bug too, *because its handling of inductives is a port of the
reference implementation* — which is precisely the caveat §3.3 already quotes,
now with a concrete instance attached. Its consistency proof does
not yet cover inductive types; de Moura's expectation is that the bug would have
been found on the way to concluding that part.

Two operational consequences recorded in the postmortem:
[`comparator.live`](https://comparator.live.lean-lang.org/) now runs `nanoda` **by
default** (the standalone CLI's documented default is still `enable_nanoda: false`
— see [`Comparator/README.md`](KernelDefects/Lean/Comparator/README.md)), and
`nanoda` is tracked daily so that `lean-eval` and comparator do not drift behind
upstream fixes.

**It happened again on 2026-08-18, and this time "nearly" is the wrong word.**
§2.1's #14807 has three witnesses in the arena. On two of them cross-checking
worked exactly as designed — `rec-missing-ih` and `proj-of-stuck-prop` are
rejected by `nanoda` and by `ind-models`, and the #14806 PR says so in its own
description. On the third, `proj-of-subst-prop`, **`nanoda` accepts the bogus
proof too**, as do `nanobruijn` and `still-nanoda`. So the official kernel and
the main external checker agreed, and were both wrong.

The difference from July is worth stating precisely, because it cuts against the
comfort available last time. In July the agreement needed **two unrelated bugs**,
one in each implementation — improbable, and the postmortem could reasonably call
the defence intact. Here there is **one bug, present in both**: `is_prop`
answering a question about a term whose type does not reduce to a sort, instead
of rejecting it. That is the §3.0 moral — independence of implementations is not
independence of blind spots — with the "unrelated provenance" mitigation removed.

`lean4lean` is unaffected, and its reason is the strongest argument the project
has: its `isProp` already used `ensureSortCore`, so it had the fix before there
was a bug to fix. Note the reversal against the paragraph above, where `lean4lean`
was the *worst* case for #14576 precisely because its inductive handling is a port
of the C++. The two facts together are the actual lesson: a port inherits bugs
where it is a port, and avoids them where the target language forced the
obligation to be stated.

**The `nanoda` row is a snapshot and is already stale**, which is itself the
point: `nanoda` merged both fixes on 2026-08-18 —
[`#26`](https://github.com/ammkrn/nanoda_lib/pull/26) *"add additional checks for
underived recursors"* at 04:13 UTC, closing the `extra-rec` class, and
[`#27`](https://github.com/ammkrn/nanoda_lib/pull/27) *"is_sort guards, disable
union find eq"* at 17:58 UTC, which is #14807 and #14806 in one commit, reached
independently. Its own summary of the second is the crispest statement of #14806
in any source: the union-find is replaced by *"sorted pairs which do not try to
exploit transitivity."* So the window in which the official kernel and the main
external checker shared this blind spot was about fourteen hours; the official
kernel's half of it is still open on every release, which is the asymmetry §2.1
records.

### 3.1 The attack corpus

| Test | Mechanism | Who fell for it |
| --- | --- | --- |
| `level-imax-leq` | `leq(imax(u,v)+1, imax(u,v))` accepted when the successor offset is ignored → a universe-collapsing `down` → cast `True`↔`False` | **nanoda** |
| `nat-rec-rules` | The checker compared imported recursor rules **against themselves** (`rec_rules.iter().zip(rec_rules.iter())`) instead of independently reconstructed ones | **nanoda** |
| `level-imax-normalization` | The normalizer drops the accumulated offset when decomposing `imax u (param v)`, so `imax 0 v ≡ succ (imax 0 v)` | **lean4lean** |
| `proj-of-prop` | Typing a projection by *inferring* rather than *checking* its structure argument | **nanoda** |
| `proj-of-imax-prop` | §2.2 / #14613 | **the official kernel** — and still, at `4.32.2`: this is the one test the released official kernel fails |
| `nested-unused-param` | §2.2 / #14576. Payload is the malformed projection `C.0 (C.0 w)` applied to a `W`, disguised by the hash collision; the property under test is that the *parameter* is checked | **the official kernel** (4.28/4.29 accept) |
| `constlevels` | §2.2 / #10577 | **the official kernel** (4.28/4.29 segfault) |
| `large-elim-param` | If "is this level surely nonzero?" wrongly returns true for a *param*, `inductive MyBool.{u} : Sort u | tt | ff` gets a recursor that large-eliminates a `Prop`; proof irrelevance gives `tt = ff` | found by Anthony Wang using Aristotle |
| `ctor-num-fields` | Lie about a constructor's `numFields` so a 1-field structure looks unit-like; definitional eta then equates all inhabitants | trusted-metadata class — **artifact**, [`EscapeHatches/Lean/ArenaTrustedMetadata.lean`](EscapeHatches/Lean/ArenaTrustedMetadata.lean) §1 |
| `rec-k-lie`, `nat-rec-k-lie` | Lie about `k` (K-like reduction) on a recursor | trusted-metadata class — **artifact**, [`EscapeHatches/Lean/ArenaTrustedMetadata.lean`](EscapeHatches/Lean/ArenaTrustedMetadata.lean) §2–§3 |
| `proj-non-structure` | Project out of a 2-constructor type, hoping the checker infers from the *first* constructor | generic |
| `k-rec-conv` | Broken K-like reduction makes `fun x => x ≡ fun _ => y` | regression test for a **sokonanoda** bug |
| `bogus1` | `debug.skipKernelTC` calibration case | — |
| `rec-missing-ih` | §2.1 / #14806. The def-eq cache's transitive closure, gated on a hash collision, makes a K-like reduction fire while a recursor's minor premises are built and not while its rules are; the `step` premise then takes four arguments and its rule supplies three | **the official kernel** (4.28, 4.29.1, **4.33.0**, nightly-2026-08-01) — **artifact**, [`DefEq/EquivManagerMissingIH.lean`](KernelDefects/Lean/DefEq/EquivManagerMissingIH.lean) |
| `proj-of-stuck-prop` | §2.1 / #14806 + #14807. The same comparison decides an inductive family's result sort, so it is a `Prop` under `_kernel_fresh.0` and a stuck sort closed; the projection guard is skipped | **the official kernel** (same four) — **artifact**, [`DefEq/EquivManagerStuckSort.lean`](KernelDefects/Lean/DefEq/EquivManagerStuckSort.lean) |
| `proj-of-subst-prop` | §2.1 / #14807 alone. `P := a = b` and `Q := a = c` are definitionally equal types whose proofs behave differently under K-like reduction. **Needs no cache and no axioms** | **the official kernel** *and* **nanoda**, **nanobruijn**, **still-nanoda** — §3.0's second occurrence. **artifact**, [`DefEq/SubstStuckSort.lean`](KernelDefects/Lean/DefEq/SubstStuckSort.lean) |
| `extra-rec` | A second recursor named `rogue`, of type `False` itself, smuggled into `False`'s inductive group with no motives, minors or rules. A checker must *derive* an inductive group's recursors and reject any exported one that is not among them; registering exported recursors as given yields an inhabitant of the genuine empty type. Distinct from `nat-rec-rules`, which perturbs the rules of a legitimate recursor | **mathgraph**, **sokonanoda**, **zignodamus**, **nanoclo**, **nanobruijn**, **still-nanoda**, **nyaya** |

**Eighteen tests as of 2026-08-18**, up from fourteen on 08-01: the four new ones
are the block above, three of them landing on 08-18 as
[`lean-kernel-arena`#141](https://github.com/leanprover/lean-kernel-arena/pull/141).
Of the eighteen, **six** have caught the official kernel — `constlevels`,
`nested-unused-param`, `proj-of-imax-prop`, and now all three of the August wave.

**One claim in this section was wrong and the corpus has now refuted it.** This
file previously said #14616 "cannot be captured as an arena export test" because
its exploit depends on transient `equiv_manager` state, and generalised that to
the whole cache-dependent class. `rec-missing-ih` is exactly such an exploit and
*is* in the corpus — by **freezing the kernel's output as a static `.ndjson`**
rather than regenerating it, with the Lean reproducer kept alongside. The arena's
own note gives the reason the obvious approach fails: regenerating the export with
a fixed toolchain "would quietly produce a benign export". So the technique is
available, and #14616 remains a gap for want of someone applying it, not for want
of a way. (`extra-rec` is frozen for a different reason — it is injected with the
kernel-bypassing `Environment.lakeAdd`.)

The corpus is not only attacks. Several other outcome classes now carry weight,
and a checker's score is the sum of all of them:

| Test | Outcome | What it measures |
| --- | --- | --- |
| `nested-nonuniform-param` | **either** | §2.1 / #14582 — Arthur Adjedj's non-uniform case, raised on #14577 as not covered by that fix. `E.mk : (w : W) → L (E ⟨false⟩) → E w` puts a constant where `E`'s parameter belongs. Type-correct, so re-type-checking the nested application does not catch it; a checker must additionally verify it *is* the expected parameter. Scored `either` because it is **not a demonstrated unsoundness** — with `L` phantom, `E w` is `Unit` for every `w`; the variant where `L` really stores an `α` is already rejected by the positivity check. That is the same conclusion this repo reached independently (§5.1, last row) |
| `proof-irrel` | accept | Incompleteness: `h a ≡ h b` for `h : A → P` with `P : Prop`. A checker comparing the proofs structurally wrongly rejects |
| `level-index-out-of-order`, `sparse-name-index` | accept | Export-format robustness: `lean4export` emits internalization-table references densely and in order, but the spec only requires integers. A checker treating them as array indices fails. `nanoda` currently errors on both |
| `perf/` (`app-lam`, `grind-ring-5`, `shift-cascade`) | accept + timed | Asymptotics, not correctness. `shift-cascade` separates de Bruijn kernels with deferred shifts (O(N²) on cascading `let`s) from locally-nameless ones (O(N)) |
| `tutorial/` | mixed | **135 tests**, a full taxonomy of what a kernel must accept and reject. **43 of them are the invalid ones**, which is the figure this file previously carried — that count is unchanged; what was never stated was the 92 valid cases alongside them |

**Live roster, 2026-08-18.** **Nineteen** registered entries, up from sixteen:
`kiota` (added 08-14), `mathgraph` — "MathGraph Kernel A6" — (08-15), and
`ind-models`, Joachim Breitner's
[`lean-inductive-models`](https://github.com/leanprover/lean-kernel-arena/blob/main/checkers/ind-models.yaml)
(08-16), which is the one to note: it was registered **two days before** the
August wave landed and catches both of #14806's exploits. `nanoclo` was added
08-10. The `official` track was repointed from `4.32.2` to **`4.33.0`** on
08-10, so the scores below are no longer directly comparable to the ones beside
them.

**Live scores, 2026-08-01.** Sixteen registered entries. `zignodamus`,
`nanobruijn` and `sokonanoda` score a perfect 57/57 on rejects, as does
`official-nightly`; the released `official` `4.32.2` scores 56/57, failing
`proj-of-imax-prop` (#14613 landed after the tag). `nanoda` is at 50/50 with nine
harness errors, `lean4lean` 55/56. Note the denominator: **57 = the fourteen named
attacks + the 43 invalid `tutorial/` cases**, not the attack table alone. It also
varies per checker, because a test a checker errors out on leaves the ratio
rather than failing it — which is why `nanoda`'s 50/50 is not comparable to
`zignodamus`'s 57/57 without reading the error column beside it.

### 3.2 The `undecidability/` category — not anyone's bug

These score `either` because there is no right answer, and they are the arena's
statement of a permanent gap. From Carneiro's thesis: algorithmic conversion **is
not transitive** (`alg-conv-trans-acc`, via `Acc.rec` and proof irrelevance —
the checker would have to *invent* the middle term), and **subject reduction
fails** (`subject-reduction-redex`/`-reduct` — a term the kernel accepts reduces
to one it rejects). Our independent measurements of the same phenomena are in
[`Audits/Lean/Metatheory/`](Audits/Lean/Metatheory/).

### 3.3 The implementations

`lean4lean` (Carneiro, Lean — *"derived directly from the C++ kernel, and as such
likely shares some implementation bugs with it; it's not really an independent
implementation"*; §3.0 records the first concrete instance of that caveat biting,
#14576), `nanoda`/`nanobruijn` (Rust), `sokonanoda`, `still-nanoda`,
`zignodamus` (Zig), `nyaya` (OCaml), `rpylean` (RPython), `mini` (deliberately
naive, invites attacks), `vow-lean-kernel`, `nanoclo`, `kiota`, `mathgraph`,
`ind-models` (Breitner's `lean-inductive-models`, registered 2026-08-16; #14806's
PR records that it catches both of that bug's exploits, which is what a checker
registered two days before the wave is for), and `evmlean` — a Lean-kernel
fragment as a **Solidity smart contract**. `lean4checker` was archived 2026-03-25
and superseded by the `leanchecker` binary shipped in the toolchain since
`v4.28.0`; note it **shares Lean's own kernel** and so is not an independent
verifier. `trepplein` (Scala, Lean 3) is abandoned but historically important:
David Renshaw's 2021 fuzzing found inputs `leanchecker` rejected and `trepplein`
accepted, which is the direct intellectual ancestor of the arena.

---

## 4. Rocq / Coq

The canonical source is Rocq's own
[`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
— a 1000-line maintainer-curated ledger of every soundness bug since 8.0, with
introduced/impacted/fixed versions and risk assessments. It contains several bugs
with no GitHub issue at all. The tracker label is **`kind: inconsistency`**
("Proof of False accepted by the kernel and/or checker"), not `kind: unsoundness`.
`coq/coq` and `rocq-prover/rocq` are the same repository; issue numbers are
continuous.

Coq historically saw roughly one soundness bug per year. **Rocq 9.2.0 fixed ten
`kind: inconsistency` issues in a single release** — an unprecedented count, and
the direct output of the 2026 sweep.

### 4.1 Guard checker — by far the most productive source

| Issue | Mechanism | Affected | Fixed | Coverage |
| --- | --- | --- | --- | --- |
| [#21053](https://github.com/rocq-prover/rocq/issues/21053) | Guard vs propositional extensionality / univalence: a cast was treated as a subterm | **V6.1–9.0** | 9.0.1 | **gap** |
| [#20413](https://github.com/rocq-prover/rocq/issues/20413) | Non-structural fixpoint arguments unchecked | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#20455](https://github.com/rocq-prover/rocq/issues/20455) | `match` on `match` wrongly detected as returning a subterm | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#20555](https://github.com/rocq-prover/rocq/issues/20555) | Incorrect reduction across an inner fixpoint | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#21682](https://github.com/rocq-prover/rocq/issues/21682) | Cross-calls in nested mutual fixpoints ignored by uniform-parameter analysis | 8.20–9.1 | 9.2.0 | **artifact** — [`NestedMutualCrossCall.v`](KernelDefects/Coq/GuardChecker/NestedMutualCrossCall.v) |
| [#21683](https://github.com/rocq-prover/rocq/issues/21683) | Fixpoint passed as a higher-order argument; axiom-free Russell paradox. **A regression introduced by the fix for #20555** | 9.0.1–9.1.1 | 9.2.0 | **artifact** — [`HigherOrderFixpoint.v`](KernelDefects/Coq/GuardChecker/HigherOrderFixpoint.v) |
| [#21701](https://github.com/rocq-prover/rocq/issues/21701) | Argument-less recursive calls (`let`-bound aliases) don't restrict uniform-argument computation | 8.20–9.1 | 9.2.0 | **artifact** — [`UniformArgsLet.v`](KernelDefects/Coq/GuardChecker/UniformArgsLet.v) |
| [#21797](https://github.com/rocq-prover/rocq/issues/21797) | `find_uniform_parameters` doesn't recurse into args of non-`fix` `Rel` applications | 8.20–9.1 | 9.2.0 | **artifact** — [`UniformArgsHiddenSelfCall.v`](KernelDefects/Coq/GuardChecker/UniformArgsHiddenSelfCall.v). Completes PR #17986's set of four |
| [#21839](https://github.com/rocq-prover/rocq/issues/21839) | Reduction performed in the wrong environment; direct `Definition oops : False` | 8.16–9.2.0 | 9.2.1 / 9.3 | **artifact** + **report** — [`GuardChecker/WrongEnvReduction.v`](KernelDefects/Coq/GuardChecker/WrongEnvReduction.v), [`Reports/2026-08-01-rocq-guard-…`](Reports/2026-08-01-rocq-guard-wrong-environment.md). **LIVE on the installed 9.2.0**, and the strongest route in this catalog: the only one where **both** `Print Assumptions` *and* `coqchk` report nothing **and** the `False` escapes through a plain `Require` into a downstream file whose own audit and `coqchk` are also clean. `coqchk` misses it because at 9.2.0 it type-checks bodies with `Typeops.infer` — the kernel's own guard checker — so it is not an independent implementation of the thing that failed |
| [#22021](https://github.com/rocq-prover/rocq/issues/22021) | Lambda domains of unapplied nested fixpoints unchecked | 8.20–9.2.0 | 9.2.1 / 9.3 | **gap** |
| [#22024](https://github.com/rocq-prover/rocq/issues/22024) | Fixpoints alter their arguments' rtrees and aren't rechecked; relative inconsistency with univalence | 9.1 — **and 9.2, measured here** | **OPEN** | **artifact** — [`Paradoxes/Coq/GuardVsUnivalence.v`](Paradoxes/Coq/GuardVsUnivalence.v). Filed under `Paradoxes/` because the `False` is conditional (ground rule 1), though its subject is a defect; `KernelDefects/Coq/README.md` cross-references it. `coqchk` certifies `unsafe (co)fixpoints: <none>` on it, as it does for #21839 |

The pattern is striking and worth stating plainly: **PR
[#17986](https://github.com/rocq-prover/rocq/pull/17986) alone introduced four
separate proofs of `False`** (#21682, #21701, #21797, #22021), PR #15434
introduced three (#20413, #20455, #20555), and the *fix* for #20555 introduced
#21683. All three of our guard-checker artifacts are failures of the *same*
analysis — uniform arguments for nested mutual fixpoints — reached three
different ways, which is why they share a directory.

### 4.2 Module system

| Issue | Mechanism | Affected | Fixed | Coverage |
| --- | --- | --- | --- | --- |
| [#15838](https://github.com/rocq-prover/rocq/issues/15838) | Module subtyping allows contravariant `Prop ⊆ Type`, disrespecting squashing → Hurkens | ~7.4–8.15.0 | 8.15.1 | **gap** |
| [#18503](https://github.com/rocq-prover/rocq/issues/18503) | `Primitive` in a Module Type bypasses subtyping conversion | 8.11.0–8.18.0 | 8.19.0 | **gap** |
| [#21051](https://github.com/rocq-prover/rocq/issues/21051) | Missing substitution when strengthening functors; `Include` corrupts the delta-resolver → `true = false` | kernel 8.5–9.0.0 | 9.0.1 | **gap** |
| [#21685](https://github.com/rocq-prover/rocq/issues/21685) | Same, for **aliased** functors: a multi-step `Module Alias := M` chain corrupts the delta-resolver | kernel 8.5–9.1 | 9.2.0 | **artifact** — [`AliasChainDeltaResolver.v`](KernelDefects/Coq/ModuleSystem/AliasChainDeltaResolver.v) |
| [#21702](https://github.com/rocq-prover/rocq/issues/21702) | `check_with_def` stored the with-body's *weaker* universes → `Type@{u} → Type@{v}` with no `u ≤ v` → Girard | 8.5–9.1 | 9.2.0 | **artifact** — [`WithDefUniverses.v`](KernelDefects/Coq/ModuleSystem/WithDefUniverses.v) |
| [#21750](https://github.com/rocq-prover/rocq/issues/21750) | Subtyping ignored elimination constraints → unbox a `Box@{SProp}` → `true = false` | 9.2+rc1 | 9.2.0 | **gap** |
| [#22287](https://github.com/rocq-prover/rocq/issues/22287) | `ugraph` keeps a *copy* of the universe-checking flag; `Local Unset Universe Checking` in a module leaves it desynced on close → effective type-in-type → Hurkens, reported as **"Closed under the global context"** | master — **and 9.2, measured here** | **OPEN** (2026-07-16) | **artifact** + **report** — [`ModuleSystem/UniverseFlagDesync.v`](KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v), [`Reports/2026-08-01-rocq-universe-flag-…`](Reports/2026-08-01-rocq-universe-flag-desync.md). **Verified here** on Rocq 9.2: `coqc` exit 0, audit clean for both the `False` and a `1 = 2` derived from it, two in-file controls refused. **Contained**: `coqchk` rejects the `.vo` and a `Require` of it is rejected at the `Require` line, so what is lost is the *local* audit, not a library |
| [#12155](https://github.com/rocq-prover/rocq/issues/12155), [#16646](https://github.com/rocq-prover/rocq/issues/16646) | `Print Assumptions` under-reports inconsistent flags through `Parameter Inline` and functor application | V8.6–now / V8.11–now | **OPEN** | **noted** — [`TypingFlags.v`](EscapeHatches/Coq/TypingFlags.v) |

### 4.3 Universes, template polymorphism, sorts

Coverage: **gap** for all.

| Issue | Mechanism | Fixed |
| --- | --- | --- |
| [#9294](https://github.com/rocq-prover/rocq/issues/9294) | Template polymorphism breaks `Prop`/`Set` separation — side constraints not collected | 8.10.0 |
| [#11039](https://github.com/rocq-prover/rocq/issues/11039) | More template-poly missing constraints (same universe in params *and* constructor args) | 8.10.2 / 8.11 |
| [#3211](https://github.com/rocq-prover/rocq/issues/3211) | De Bruijn bug computing the allowed elimination principle | 2014 |
| [#8341](https://github.com/rocq-prover/rocq/issues/8341) | Universe polymorphism can capture global universes | — |
| [#15916](https://github.com/rocq-prover/rocq/issues/15916) | Variance inference for section universes ignored use in inductives | 8.16 |
| [#21694](https://github.com/rocq-prover/rocq/issues/21694) | Incorrect discharge of squashing info for a sort-polymorphic inductive in a section | 9.2.0 |
| [#21689](https://github.com/rocq-prover/rocq/issues/21689), [#21970](https://github.com/rocq-prover/rocq/issues/21970) | Double universe substitution in letins from match indices / constructor arguments | 9.2.0 / 9.2.1 |
| — | `Prop ≤ Set` conversion bug, **found by Georgi Guninski** | 8.3 / 8.2 (2010) |

### 4.4 Conversion machines (lazy / VM / native)

Coverage: **gap** for all but #21736, which now has
[`Conversion/RegisterInlineVM.v`](KernelDefects/Coq/Conversion/RegisterInlineVM.v).
The whole class has no Lean analogue, because Lean has no VM or native
conversion machine in the kernel.

| Issue | Mechanism | Fixed |
| --- | --- | --- |
| [#4157](https://github.com/rocq-prover/rocq/issues/4157) | VM constructor tag collision above 256 constructors | 8.5 |
| [#14243](https://github.com/rocq-prover/rocq/issues/14243) | native: Coq→OCaml identifier translation not bijective (`α` and `__U03b1_` collided → identified `True`/`False`) | 8.5pl2 |
| [#11043](https://github.com/rocq-prover/rocq/issues/11043) | Lazy: de Bruijn handling in lambda relevance inference (SProp) → `0 = 1` | 8.10.1 |
| [#16645](https://github.com/rocq-prover/rocq/issues/16645) | native: `Prod`/`Prod` conversion compared the **wrong components**; risk assessed "systematic" | 8.16.1 |
| [#16831](https://github.com/rocq-prover/rocq/issues/16831), [#16829](https://github.com/rocq-prover/rocq/issues/16829) | η-expansion of cofixpoints in the wrong environment; conversion compared the *mutated* primitive array | 8.16.1 |
| [#16957](https://github.com/rocq-prover/rocq/issues/16957) | Tactic code could mutate a global cache of section variables. `priority: blocker` | 8.17.0 |
| [#21690](https://github.com/rocq-prover/rocq/issues/21690) | Missing stack conversion for irrelevant-to-relevant match; with `Definitional UIP`, `0 = 1` | 9.2.0 |
| [#21736](https://github.com/rocq-prover/rocq/issues/21736) | `Register Inline` + universe polymorphism: `genlambda.ml` fails to substitute the universe instance → `vm_cast_no_check` proves `Type@{v} = Type@{u}` → Hurkens. **Affected every patch release from 8.5 to 9.1, and coqchk too** | 9.2.0 — **artifact**, [`Conversion/RegisterInlineVM.v`](KernelDefects/Coq/Conversion/RegisterInlineVM.v); rejection lands at `Qed`, where the deferred `vm_cast` is finally checked |
| [#11321](https://github.com/rocq-prover/rocq/issues/11321) | Broken long multiplication in 32-bit primint emulation, **all three machines** | 8.11.0 |
| [#12483](https://github.com/rocq-prover/rocq/issues/12483) | An **incorrect `PrimFloat.leb` axiom shipped** → `False` straight from the library. `priority: blocker` | 8.11.x |

### 4.5 Library-axiom conflicts that shipped as bugs

Coverage: **noted** for all; these are the §1.1/§1.2 items that were once
reachable without a flag.

* **Description + decidability of equality on reals vs impredicative `Set`** —
  introduced 2002-06-20, shipped in **7.3.1 and 7.4**, found by Herbelin and
  Werner, fixed 2004-10-28 **by making `Set` predicative**. This is why the flag
  exists and is off by default.
* **Guard condition vs propositional extensionality in the `Sets` library** —
  *"technically speaking from V6.1 … which was then inconsistent from the very
  beginning without we knew it"*. Fixed 2014-10-28, and a second variant survived
  to **9.0**, fixed in 9.0.1. The clearest example of an axiom that was fine and
  a kernel that had to change.
* **AC + EM vs large *singleton* elimination to `Set`** — *"not a bug but a
  change of intended model"*, impacted strictly before 8.1, fixed 2007-02-09 by
  constraining singleton elimination, found by Benjamin Werner.

### 4.6 Currently open, soundness-relevant

Coverage: **gap** for all except #22287, which now has an artifact (§4.2).
#22287, #22024 and #22352 are the ones with a known route to `False`.

**New 2026-08-18, and it is a `coqchk` bug rather than a kernel one — the first
in this file's Rocq ledger.**
[#22352](https://github.com/rocq-prover/rocq/issues/22352) (Jason Gross): with
`-bytecode-compiler yes`, `coqchk` typechecks each constant's body but takes the
VM bytecode from the `.vo`'s **separately serialised `vmlibrary` segment**, with
nothing tying the two together. Two honest compilations of a one-constant file
differing only in that constant's value have byte-identical `opaques` and
`summary` segments, so splicing one file's `library` onto the other's
`vmlibrary` gives a well-formed `.vo` that proves `False` and passes the checker
with **no axioms reported**. The reproducer needs no patched tool — stock `rocq`
and `rocqchk`, plus a Python script that rewrites the object file.
[#22353](https://github.com/rocq-prover/rocq/issues/22353) is the fix, and it
stops reading the segment entirely rather than comparing against it: stored and
recompiled bytecode legitimately differ in at least four ways (user vs canonical
names in relocations, `get_alias` collapsing, the unused-argument mask, and
inlining of `const_inline_code` bodies), so an equality-based fix false-rejects
`Module N := M.` Its incidental finding is the more alarming half: the
unused-argument **mask** is passed to `Conversion.eqappr`'s
`convert_stacks ~mask`, so a lying mask makes *ordinary* conversion skip
comparing arguments — reachable with the default `-bytecode-compiler no`, and
closed by the same PR without an exploit being built for it.

This lands squarely on §4.7's asymmetry and on §1.2's tampered-`.vo` row, and it
is the sharper form of both: not "neither system re-typechecks on import", but
"the checker *does* re-typecheck, and then runs code it did not derive from what
it checked". The Lean analogue would be `leanchecker` trusting a compiled-code
segment of an `.olean`; it has none, because the kernel's only native hook is
`Lean.reduceBool`, which `leanchecker` cannot replay at all
([`ReduceBoolFreeName.lean`](KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean)
is this repo's measurement of exactly that). Coverage: **noted** — no artifact
here, and Rocq was not otherwise re-surveyed on 08-18.

[#22287](https://github.com/rocq-prover/rocq/issues/22287) (universe-flag desync
on module close) · [#22024](https://github.com/rocq-prover/rocq/issues/22024)
(guard rtree mutation) · [#16891](https://github.com/rocq-prover/rocq/issues/16891)
(VM/native memory corruption on ill-typed terms via `exact_no_check`) ·
[#13439](https://github.com/rocq-prover/rocq/issues/13439) (VM buffer overflow) ·
[#12439](https://github.com/rocq-prover/rocq/issues/12439) (coqchk under-checks
primitive declarations) · [#12155](https://github.com/rocq-prover/rocq/issues/12155)
and [#16646](https://github.com/rocq-prover/rocq/issues/16646) (`Print
Assumptions` under-reporting) · [#21113](https://github.com/rocq-prover/rocq/issues/21113)
(`Private Inductive` check too weak) · [#21494](https://github.com/rocq-prover/rocq/issues/21494)
(kernel accepts PrimRecords with indices) · [#20016](https://github.com/rocq-prover/rocq/issues/20016)
(bad case inversion with `Set Definitional UIP`).

**Corrections to the previous survey.** Three issues this catalog previously
listed as soundness-relevant are not: [#21733](https://github.com/rocq-prover/rocq/issues/21733)
(`imitate` is unsound *in elaboration*; the kernel still rejects),
[#21497](https://github.com/rocq-prover/rocq/issues/21497) (wrong non-uniform
parameter computation breaks *eliminator generation*), and
[#22110](https://github.com/rocq-prover/rocq/issues/22110) (labelled
`kind: wish`; an incompleteness).

### 4.7 `coqchk` — measured asymmetry

Worth recording because a CI script that only checks the exit code proves less
than it appears to.

| Input `.vo` | `coqchk` |
| --- | --- |
| `Admitted` + axioms | exit 0, listed under `* Axioms:` |
| `Unset Guard Checking` | **exit 0 — accepted**, merely listed |
| `Unset Positivity Checking` | **exit 0 — accepted**, merely listed |
| `Unset Universe Checking` | **rejected** |
| `-impredicative-set` | rejected unless given the same flag |
| rewrite rules | exit 0, listed |

Its own escape hatches, from `--help`: `-admit module` (*"load module and
dependencies **without checking**"*) and `-norec module`. CompCert's actual
practice is to run `coqchk` *and separately confirm* that no guard conditions
were disabled — precisely because coqchk reports rather than rejects them.

---

## 5. Outstanding work

Ordered by value.

-1. **lean4#14616 — an axiom-free `False` on every released toolchain, with no
   artifact anywhere. Surface now mapped; four levers measured; still no safe
   payload.** The `master`-only fix (`check_no_nested_aux`, `inductive.cpp`,
   commit `35f696862c`) rejects an inductive declaration whose constructor type
   names a `_nested` auxiliary type, by `Expr.const` name or by `Expr.proj`
   structure name. The postmortem records that this one **cannot be captured as
   an arena export test** — the exploit turns on transient `equiv_manager`
   state — so the arena's checkers do not test it and nobody has published a
   reproduction.

   **That premise is now known to be too strong (2026-08-18).** `rec-missing-ih`
   is an `equiv_manager`-dependent exploit and it *is* in the corpus, by freezing
   the kernel's output as a static `.ndjson` instead of regenerating it, with the
   Lean reproducer kept beside it (§3.1). Whatever else stands in the way here,
   "cannot be captured as an export" no longer does, and the freezing technique is
   the first thing to try. Note the arena's own caveat on why the naive approach
   fails: regenerating with a fixed toolchain "would quietly produce a benign
   export", so the frozen file has to be produced on an affected toolchain — for
   #14616 that means `v4.32.2` or earlier, all of which are to hand.

   [`Audits/Lean/Nested/AuxNameReachability.lean`](Audits/Lean/Nested/AuxNameReachability.lean)
   is the reconnaissance, and it establishes four things on `v4.32.2`. The
   auxiliary name is **predictable** — `mk_unique_name` appends `_1`, `_2`, … so
   the first auxiliary for a nested `Wrap` is exactly `_nested.Wrap_1` — and a
   safe declaration naming it **is accepted**. The **checked/stored divergence is
   real and is demonstrated**: a field checked as `_nested.Wrap_1.{0} n`, whose
   type is `Prop`, is stored as `Wrap (@B n)`, whose type is `Sort u`. But the
   two levers that reach it from a *safe* declaration are closed by
   `check_positivity`, because `is_valid_ind_app` compares the occurrence against
   `m_ind_cnsts[i]` with `expr` equality, which covers **both** the arguments and
   the universe levels; the `Expr.proj` lever is closed by ordering, since
   `check_constructors` runs before `declare_constructors` and the auxiliary's
   constructor does not exist yet; and the only path that does reach the
   divergence is `isUnsafe`, which skips positivity and then loses to the safety
   gate (`invalid declaration, it uses unsafe declaration`).

   So what remains to find is a shape where the auxiliary is reached **without
   the occurrence being a positivity-checked constructor field**. Everything else
   is now instrumented. Upstream's regression test
   `tests/elab/kernelNestedAuxName.lean` gives the two shapes `master` rejects,
   and neither of them is that shape either — both are ordinary fields.

   *Update.* The two primitives upstream's own commit message says the exploit is
   built from are now measured and are exactly as advertised
   ([`Audits/Lean/Projections/ProjSnameBlindness.lean`](Audits/Lean/Projections/ProjSnameBlindness.lean)):
   a released kernel reduces a wrong-structure projection and calls two
   projections differing only in `proj_sname` definitionally equal. What separates
   them from the one place a checked `addDecl` stores an unchecked term is the
   *phase order* inside `add_inductive_fn`, plus `infer_proj`'s guard — which
   §2.6 records runs only in the `infer_only = false` traversal. A dedicated
   agent run at this composite did not complete, so this line is **unfinished
   rather than negative**; it is still the best remaining lead in this file.

0. **lean4#14582 needs an instrumented kernel build. The instrumentation is
   written and compiles; what remains is the bootstrap.**
   [`Audits/nested-instrumentation.patch`](Audits/nested-instrumentation.patch)
   applies to `src/kernel/inductive.cpp` at `v4.32.0` and dumps, under
   `LEAN_DUMP_NESTED=1`, every nested occurrence with its parameter and index
   arguments and every auxiliary type and constructor the kernel synthesises —
   exactly the artifacts that never reach the environment. Build recipe worked
   out here, on Windows with MinGW GCC 16.1 and CMake 4.3:
   `cmake -G "Unix Makefiles" .. -DUSE_MIMALLOC=OFF -DCMAKE_MAKE_PROGRAM=mingw32-make`
   (the default Ninja generator is rejected, `make` must be shimmed to
   `mingw32-make`, and the mimalloc `FetchContent` step fails). Compiling the
   kernel standalone gets 59 of 61 sources with
   `-std=c++20 -DLEAN_MULTI_THREAD -DLEAN_WINDOWS -DLEAN_WIN_STACK_SIZE=…` plus a
   hand-written `githash.h`; only `io.cpp` and `init_module.cpp` fail, needing
   libuv and ICU, and the kernel does not use either.
   **The blocker is not the kernel — it is the environment.** `lean::environment`
   has no C++-side constructor for an empty kernel environment; every constructor
   wraps an existing Lean object, and `Kernel.Environment` is built on the Lean
   side. So a standalone C++ harness cannot create anything to declare into, and
   the instrumented kernel is only useful inside a full stage0→stage1 build.
1. **lean4#14582's territory is invisible from inside Lean.** The nested-inductive auxiliary declarations where the
   defect lives never enter the environment: they are created in a temporary
   kernel environment and rewritten by `restore_nested`, so a search from inside
   Lean re-checks only the surviving recursors. This is the same property that
   made lean4#14616's exploit uncapturable as an arena export test. Black-box
   probing cannot reach it; instrumenting `replace_if_nested`/`restore_nested` in
   a source build can.
   *Update 2026-08-01.* Two things reduce the urgency without removing it. The
   arena now carries [`nested-nonuniform-param`](https://github.com/leanprover/lean-kernel-arena/blob/master/tests/nested-nonuniform-param.yaml),
   a black-box export of exactly #14582's shape, scored `either`; and its stated
   reason for that score — the storing variant *"is already rejected by the
   kernel's positivity check (\"non valid occurrence\")"* — is the same conclusion
   this repo reached independently by direct test (§5.1, last row), arrived at from
   the other side. Two independent derivations of a negative result is as close to
   confirmation as a negative result gets. The instrumentation is still what would
   settle whether an *exploitable* shape exists; upstream has meanwhile chosen the
   belt-and-braces route with #14621, which simply re-checks whatever the nested
   code emits.
2. **The Lean Kernel Arena corpus (§3).** Fourteen catalogued attacks, three of
   which the official kernel has fallen for, plus the accept-side classes
   (`proof-irrel`, the two export-robustness tests, `perf/`), the 135-test
   `tutorial/` family, and the `undecidability/` category that formalises what
   [`Audits/Lean/Metatheory/`](Audits/Lean/Metatheory/) measured independently.
   This is the single largest gap, and it is now the community's canonical
   artifact. The 08-01 pass found four tests and a whole outcome class this file
   had not recorded, plus one row for a test that does not exist — so re-reading
   the corpus directly, rather than from this summary, is part of the job.

   **Partly closed, and it corrected this catalog.**
   [`Audits/Lean/Arena/RejectCorpus.lean`](Audits/Lean/Arena/RejectCorpus.lean)
   re-runs every attack reachable from inside Lean against the official kernel:
   all rejected, messages pinned, byte-identical across seven released pins. The
   correction is to the *trusted-metadata* class above. This repository had read
   `ctor-num-fields` and `rec-k-lie` as unreachable from Lean because `addDecl`
   derives `numFields` and `k` itself and the wire format has nowhere to put a
   lie. True of `addDecl` — and false of Lean, because the arena's own tests are
   ordinary Lean modules that declare honestly and then **overwrite the stored
   `ConstantInfo`**. That is
   [`EscapeHatches/Lean/ArenaTrustedMetadata.lean`](EscapeHatches/Lean/ArenaTrustedMetadata.lean):
   three closed axiom-free `False`, filed as a hatch and not a defect because the
   kernel's every decision is correct on the input it was handed. The general
   lesson is that "the wire format cannot express the lie" is not the same claim
   as "the system cannot be told the lie".
2. **Rocq's remaining proofs of `False` (§4).** Of the 2026 sweep's eight,
   #21702, #21736, #21797 and #21839 have since been added, leaving #21690,
   #21694 and #22021; the whole pre-2026 history is still `gap`.
   #21736 is the one worth taking next-to-last rather than last: it is the only
   Rocq defect in this catalog that **`coqchk` shared**, which puts it in the
   same class as lean4#14613. Of the two OPEN ones with a route to
   `False`, **#22287 is now an artifact** (§4.2) — the first *live* Coq exhibit
   here, and the first route in this catalog reachable from nine lines of
   ordinary source with no metaprogramming at all. **#22024** (guard rtree
   mutation, relative inconsistency with univalence) is now an artifact too
   (`Paradoxes/Coq/GuardVsUnivalence.v`), so both OPEN routes are covered. The
   remaining Rocq priority is the long pre-2026 tail of §4, of which #21839 is
   now done and #21797/#21702 were staged but not landed.
3. ~~**Rocq's untracked hatches (§1.2).**~~ **All three done.** The original item
   read: *`vm_compute`/`native_compute`, `Extraction`, and `Declare ML Module` are
   the three routes `Print Assumptions` cannot see at all, and none has an
   artifact.* Each now has one —
   [`ComputeMachines.v`](EscapeHatches/Coq/ComputeMachines.v),
   [`ExtractConstant.v`](EscapeHatches/Coq/ExtractConstant.v),
   [`DeclareMLModule.v`](EscapeHatches/Coq/DeclareMLModule.v) — and two of them
   corrected this catalog rather than confirming it: §1.2's "ignores `Opaque`"
   claim about `vm_compute` was wrong, and the `Extract Constant` row understated
   the reach (an *arity* mismatch survives `coqc` too, not just a syntax error).

   The methodological lesson is worth keeping. These three are invisible to both
   `Print Assumptions` and `coqchk`, so an exhibit checked the usual way — assert
   what the audit reports — would assert nothing and pass vacuously.
   `EscapeHatches/verify.ps1` instead compiles and *runs* the extracted OCaml and
   asserts three named disagreements with the Coq theorems. An exhibit whose whole
   content is "the audit is silent" needs a second observable, or it is not an
   exhibit.
4. ~~**Univalence + UIP (§1.1).**~~ **Done, in both systems**, and the two
   statements differ in a way worth having recorded: Lean needs *one* hypothesis
   because proof irrelevance makes UIP definitional, Rocq needs *two* because it
   does not. `Paradoxes/Lean/TypeTheoryParadoxes/Univalence.lean` §1 and
   `Paradoxes/Coq/UnivalenceUIP.v` §1 machine-check the same three judgments
   succeeding and failing respectively. What remains open in §1.1 is the row
   below it: univalence + unrestricted `LEM∞`.
5. **Pair #12747 with `LevelFuzzer`.** Confirm case-by-case that the fuzzer's
   162 incompleteness cases are instances of the `imax`-to-`max` defect.
6. **Re-survey cadence.** Both trackers move faster than any static catalog —
   four of the Lean defects in §2.2 were fixed *on the day of this survey*. This
   file carries a survey date for that reason.

### 5.1 What the 2026-07-31 audit sweep ruled out

Recorded so the same ground is not re-covered. Each was a systematic search of a
Lean kernel surface against an explicit oracle; harnesses and counts are in
[`Audits/`](Audits/). All clean unless noted.

| Surface | Oracle | Result |
| --- | --- | --- |
| `Nat` accelerators at powers-of-two boundaries | compiled `Nat` | 39,510 applications, 0 divergence |
| `Level.geq` | denotational `≥` over valuations | 60,000 pairs, 0 unsound, 738 incomplete |
| Inductive field vs. struct universe admission | `m ≤ l` universally, or `l` denotationally `0` | 289 declarations, all correct |
| `nparams` in a raw `inductDecl` | parameter/index split | kernel validates it; lying is rejected |
| `Expr.proj` structure-name confusion, out-of-range index, partial constructor | `infer_proj` | all rejected |
| Subject reduction, and `e ≡ whnf e` | kernel's own `check` | 5,656 terms, 0 violations |
| `Array` `any`/`all`/`foldl`/`foldr` at out-of-range `start`/`stop` | compiled `Array` | 576 comparisons, 0 divergence |
| `UInt8`/`UInt64` arithmetic and shifts at word boundaries | compiled `UInt` | 9,582 comparisons, 0 divergence |
| `String` `get`/`next`/`prev`/`atEnd`/`extract` at invalid UTF-8 boundaries | compiled `String` | 320 comparisons, 0 divergence |
| `Nat.rec` on literals, `0` through `2^100` | expected constructor branch | 0 divergence |
| `Prop` inductives: subsingleton-elimination restriction | proof-relevance | 40 declarations, correctly restricted |
| Kernel-internal fvar leaks into inferred types | `_kernel_fresh` scan + re-check | none (i.e. #10475 is fixed) |
| Module boundary: `sorry`, private-in-public, section variables | `#print axioms`, visibility | all correctly guarded — **but the sweep did not cover `partial` across the boundary, which is not guarded at all**: see §2.1/#14609 and [`ModuleSystem/`](KernelDefects/Lean/ModuleSystem/). The row stands for what it tested; the omission is recorded here rather than silently fixed |
| `Expr.mdata` as a bypass: positivity, self-occurrence-in-index, `check_no_metavar_no_fvar` | the corresponding kernel check | every check strips `mdata`; all of `hasFVar`/`hasMVar`/`hasLooseBVars` propagate through it |
| `Nat.sqrt`, `nextPowerOfTwo`, `lcm`, `min`, `max`, `testBit` | compiled implementation | 10,638 comparisons, 0 divergence |
| Signed fixed-width arithmetic: `Int8`/`Int16`/`Int32`/`Int64`, ten ops each incl. `div`/`mod`/shifts at `minValue` | compiled implementation | 23,160 comparisons, 0 divergence |
| Unsigned `UInt16`/`UInt32` | compiled implementation | 3,940 comparisons, 0 divergence |
| `USize`/`ISize`, and word-size-dependent facts | kernel reducibility | kernel is correctly **stuck** — `System.Platform.numBits` is opaque, so even `(1 : USize) + 2 = 3` is not `rfl`-provable, and `numBits = 64` is undecidable. Sound: the theory fixes only `numBits = 32 ∨ numBits = 64` |
| Arbitrary-precision `Int`: `ediv`/`emod`/`fdiv`/`fmod`/`tdiv`/`tmod`/`bdiv`/`bmod`/`gcd` at ±2^32, ±2^64, ±2^70 | compiled implementation | 16,428 comparisons, 0 divergence |
| `BitVec` at width 8: `sdiv`/`smod`/`srem`/`udiv`/`umod`, shifts and rotates past the width, `setWidth`/`signExtend` up and down, signed and unsigned comparisons | compiled implementation | 5,070 comparisons, 0 divergence |
| **Every `@[implemented_by]` pair** in core + Batteries + Mathlib | the pair carries *no* proof obligation, so the two sides must be compared directly | 173 pairs; **166 have `unsafe` implementations** the kernel cannot reduce, and the remaining 7 bottom out in irreducible `USize` operations, so none is kernel-differentiable |
| **Every `@[csimp]` theorem** in core + Batteries + Mathlib, audited for axiom dependencies | lean4#7463 (**OPEN**) shows axioms used in a `csimp` proof are not propagated through `native_decide`, so a `csimp` lemma resting on `sorryAx` or a custom axiom would make the compiler disagree with the kernel while `#print axioms` stays clean | 181 entries; **every one rests only on `propext` / `Quot.sound` / `Classical.choice`**. #7463 is therefore a latent hole with no live instance in the ecosystem, not an exploitable one |
| `Char` and `ByteArray` — the remaining `@[extern]` families that are *kernel-reducible* (they bottom out in `UInt8`/`UInt32`, not the opaque `USize`) | compiled implementation, at the UTF-16 surrogate range, the `0x10FFFF` cap, and past `2^32`; and at out-of-range `ByteArray` indices | 315 comparisons, 0 divergence. `Char.ofNat` substitutes the default for every invalid scalar value consistently on both sides, and `toNat`/`utf8Size`/`isAlpha`/`isDigit`/`isWhitespace`/`isUpper`/`isLower` all agree |
| `Nat.repr` vs `Nat.reprFast` across both of its internal boundaries (the 128-entry memo table, and `USize.size`) | an independent decimal conversion built from `Nat.div`/`Nat.mod` | 336 comparisons, 0 divergence. `reprFast` is correct by construction: it uses `USize.ofNatLT n h` with a proof `h : n < USize.size`, and falls back to the general path above it |
| `Declaration.mutualDefnDecl` — the one declaration path never probed | kernel acceptance by safety level | firewalled by design: `add_mutual` **rejects** a block whose safety is `safe` (`declaration is not tagged as unsafe/partial`), so every kernel-level mutual block is `unsafe`/`partial` and the `infer_constant` gate stops a safe declaration depending on it. Headers are checked before any body. **Correction, measured 2026-08-01:** the same row said "#14608's same-`lparams` requirement is enforced" — it is not, on any released toolchain. That check is `master`-only, added 2026-07-30 after `v4.32.2` was tagged; a `partial` mutual block whose members are declared at different universe parameters is accepted throughout. Not a `False` on its own, since `add_mutual` still refuses a `safe` block. Harness [`Audits/Lean/Nested/MutualLevelParams.lean`](Audits/Lean/Nested/MutualLevelParams.lean) |
| `Float`: is anything *proved* about it anywhere in core or Mathlib? | IEEE-754 violates reflexivity (`NaN`) and congruence (zero vs. negative zero), so any lawfulness lemma would be false and `native_decide`-exploitable | **zero** `Lawful*` or `DecidableEq` instances mentioning `Float`/`Float32`; all 25 theorems that mention them are auto-generated structure lemmas (`.mk.inj`, `.mk.injEq`, `.sizeOf_spec`, `.ext`) or `Nonempty` instances. The "prove nothing, so nothing can be contradicted" discipline holds across the whole ecosystem |
| `Array.qsort`, `Array.insertionSort`, `List.mergeSort`, `Array.binSearch` — all with `unsafe` fast implementations | an independent insertion sort, and membership for the search | 197,604 comparisons over pseudorandom inputs at lengths 0–129, **0 divergences** |
| Large `Nat.shiftLeft` *below* the panic threshold — is `mul2k` correct at scale? | round trip through `shiftRight`, cross-check against the `Nat.pow` accelerator, popcount, and low-64-bit agreement with the compiled implementation, at shifts up to 2^24 | 95 checks, 0 divergence. This closes the `shiftLeft` finding from the other side: the value is **correct** everywhere it is computed, so the defect is purely the uncatchable abort above `UINT_MAX` and never a wrong result |
| Nested-inductive auxiliary declarations — can the missing re-check of lean4#14621 be exercised from inside Lean? | re-run `Kernel.check` on the type and value of every declaration the kernel generated for nine nested inductives, including the non-uniform shapes of #14582 | 240 surviving declarations re-checked, **0 failures** — but the test cannot reach the interesting artifacts: **zero** constants containing `_nested` persist in the environment. The auxiliary types are transient, built in a temporary kernel environment and mapped back by `restore_nested`, so only recursors, `below`/`brecOn`/`sizeOf`/`noConfusion` survive. Confirmed at the lowest level reachable from Lean: feeding a raw nested `inductDecl` to `Kernel.Environment.addDecl` and diffing the returned environment yields exactly four new constants — the type, its constructor, and the two recursors — and no `_nested` name at all |
| lean4#14582's **open question**, tested directly: `is_nested_inductive_app` scans only the first `nparams` arguments for occurrences of the types being declared, and never the indices — so can a declared type reach an index unchecked? | build the #2125 circularity through a *field's* index rather than the conclusion's: `K a b` inhabited iff `b = false`, `f a := decide (Nonempty a)`, then `E \| node : K E (f E) → E`, which would give `E` inhabited ↔ `E` empty | **rejected** — `(kernel) arg #1 of 'E.node' contains a non valid occurrence of the datatypes being declared`. The positivity checker covers the indices independently, whether or not the nested-detection saw them. Rejected both when `E` is in the index alone (nested path not taken) and when it is in the parameter *and* the index (nested path taken). Control: `E` in a phantom parameter alone is accepted, and is sound — `K E false` is isomorphic to `Unit` |

Two things did turn up, neither a `False`. `Nat.shiftLeft`'s missing magnitude
guard is §2.6. And `Kernel.check` with a caller-supplied local context whose
fvar is named `_kernel_fresh.N` lets the kernel's own generated binder **capture**
it — `fun (y : False) => x` is typed `False → False` where the context binds
`x : Nat`, while the control (`_uniq.0`) is typed correctly. It is contained:
every `add_*` path in `environment.cpp` rejects fvars in values *before*
type-checking, so it cannot reach a closed declaration, and Lean's own name
generator never produces the reserved prefix.

### 5.2 What the 2026-08-01 released-toolchain pass found and ruled out

Method, **as corrected on the same day**. The first pass ran
`git diff v4.32.2..master -- src/kernel/` against the pinned
[`Upstream/lean4`](Upstream/) at `5fa71c9141`, on the theory that this gives the
exact set of checks the shipped kernels lack. It does, and that is the flaw: a
soundness fix outside `src/kernel/` is invisible to it, and one such fix —
#14609 — is an axiom-free `False` on every release. The corrected sweep drops the
path filter and searches by commit message:

```bash
git log v4.32.2..HEAD --format="%h %s" --grep=soundness --grep=unsound     --grep="proof of false" --grep="kernel bug" --grep=inconsisten -i
```

Ten commits, classifying as:

| Class | Commits |
| --- | --- |
| **Unreleased proofs of `False`** | **#14609** (module stub, §2.1), **#14613** (`is_prop`, §2.1), **#14616** (`_nested`, §2.1) |
| Already released | #14498/#14484 (`v4.32.1`), #14577/#14576 (`v4.32.2`) |
| Widening / hardening, not soundness | #14615, #14621 |
| Tactic bugs the kernel itself caught | #14618 (`grind` closes a goal with an ill-typed term; the kernel rejects it), #13587 (`lia`/`grind` `eq_def` kernel type mismatch), #14524, #14404 |

**And that sweep is still incomplete.** It misses #14607 and #14608, whose commit
messages do not use the word — and #14608 is a check that no release enforces
(§5.1). Three enumeration methods have now each missed something: the
`src/kernel/` diff missed #14609 because that fix lives in `src/Lean/`; the
keyword search misses #14607 and #14608. The only method that misses nothing is
to take the PR numbers the postmortem itself names — #14607–#14616, #14621,
#14631, #14632, #14633 — and check each against the release tags one at a time.
That is now the recorded procedure.

Then black-box confirmation from inside Lean for each. This is a different
question from §5.1's — not "is there an undiscovered hole" but "which discovered
holes are still shipped".

| Surface | Question | Result |
| --- | --- | --- |
| The whole `src/kernel/` diff, `v4.32.2` → `master` | Which of the July-wave fixes are in no released toolchain? | Twelve files, of which **two are live proofs of `False`**: #14613 (`is_prop`) and #14616 (`_nested`). The rest are hardening (#14621, #14631, #14632's `add_quot`/`add_mutual`/`reduce_proj_core` guards, #14633's checking order) or widening (#14615). **Incomplete by construction** — the path filter hides #14609, a `src/Lean/` fix that is a third live proof of `False`; see the corrected method above |
| #14613, reachability on releases | Can the payload be declared at all, given that `check_constructors` at `v4.32.2` gates data fields on the *syntactic* `is_zero`? | **Only via a mutual block.** `Sort (imax 1 0)` alone with a `Bool` field is rejected; second in a block whose first type is `Sort 0`, accepted; reversed, rejected. This is §2.6's laundering finding and is the step that makes the exploit possible |
| Spellings of zero other than `imax 1 0` | Is the class wider than the one level upstream's test names? | Yes — `max 0 0` gives its own `False` by the identical route. `is_zero` is `kind() == Zero`, so the class is every spelling that is not literally `Level.zero` |
| Every syntactic `Prop`-hood test in `src/kernel/` on `master` | Did #14613/#14615 convert all of them? | Yes. Grepping `is_zero(` and `mk_Prop()` over `src/kernel/` leaves no site deciding `Prop`-hood: the surviving `mk_Prop()` uses build the type of `Quot`'s relation argument and the placeholder type of `local_ctx`'s dummy declaration, and the surviving `is_zero` uses are on `Nat` literals |
| `is_not_zero` — the one level predicate the wave did **not** make semantic, read *before* the "mutual" and "2+ constructors" branches of `elim_only_at_universe_zero` | Does it ever call a possibly-zero level nonzero, and so large-eliminate an inductive predicate? | 360 level spellings to depth 3, 91 large-eliminating: **0 unsound**. Harness [`Audits/Lean/Fuzz/IsNotZeroFuzzer.lean`](Audits/Lean/Fuzz/IsNotZeroFuzzer.lean) |
| `infer_proj` vs `is_non_rec_structure` | `infer_proj` checks "exactly one constructor" and the arity but **not** `nindices == 0` nor non-recursiveness, while `is_non_rec_structure` — the gate for structure eta and unit-like eta — checks both. Is the asymmetry exploitable? | **No.** `Expr.proj` is accepted on indexed and on recursive one-constructor inductives, and it ignores the indices entirely: `(p : Pin false).0 : Nat` type-checks for `inductive Pin : Bool → Type \| mk : Nat → Pin true`, even though `Pin false` is empty. That is vacuous — a one-constructor type is inhabited only at the indices its constructor produces, so the projection has no argument to be wrong about. Structure eta was separately measured as refused for the recursive shape (`q =?= Rec1.mk q.0 q.1` is `false`), which is `is_non_rec_structure` doing its job. Worth recording because the acceptance looks alarming and is not |
| `Expr.proj` index arithmetic on `master` | `reduce_proj_core` still computes `nparams + idx` in `unsigned`, and `to_proj_idx` admits up to `UINT_MAX`, so the sum can still wrap | **Source argument, not measured.** `infer_proj` iterates the constructor's Pi-telescope `idx` times and throws as soon as it runs out of binders, so `idx < nfields` on every accepted term and the sum cannot approach `UINT_MAX`. The #13618 family stays closed for the reason #12746 was, not by a bound on the sum — which means it reopens if a path ever reduces a projection that `infer_proj` did not see |
| #14616's `_nested` auxiliary environment — is the checked/stored divergence reachable from a **safe** declaration? | The auxiliaries exist only in a temporary environment; `restore_nested` rewrites the names back afterwards, so a declaration naming one is checked against one type and stored with another | **Yes, from a safe declaration.** The name is predictable (`_nested.<Host>_1`) and a safe declaration naming it is accepted. Four levers were measured: *level swap* and *parameter swap* die in `check_positivity`, since `is_valid_ind_app` compares against `m_ind_cnsts[i]` with `expr` equality (covering args **and** levels); *`Expr.proj`* dies on ordering (`check_constructors` precedes `declare_constructors`, so the auxiliary's constructor is not yet declared — the control proves the rewrite happened); *`isUnsafe`* skips positivity, reaches the divergence, and loses to the safety gate. The fifth works: **hide the occurrence from `check_positivity`'s leading `whnf`** (§2.6), and a safe module stores three ill-typed constants on every release. Still no `False` — the ill-typedness is inert. Harnesses [`AuxNameReachability.lean`](Audits/Lean/Nested/AuxNameReachability.lean), [`IllTypedStoredConstructor.lean`](Audits/Lean/Nested/IllTypedStoredConstructor.lean) |
| #14607 (`check_no_metavar_no_fvar` in `inductive.cpp`) — the **third** July fix in no release, and §2.2 lists it among the defects that yielded an axiom-free `False`. Is it reachable? | Free variables and metavariables in a nested inductive declaration | **Not by five shapes.** Tried: an fvar as a plain field type; in a nested occurrence's parameter; in a separate field beside a nested occurrence; in a **phantom** host parameter — the shape that survives into `m_aux2nested` without appearing in the auxiliary type or its constructor; and metavariables in those positions plus an index. All five rejected. The phantom one dies on a check easy to miss in the diff: `add_inductive` already ran `tc.check(nested, …)` over every stored nested occurrence. If #14607 is reachable on a release it is by some other shape |
| **Composites of the live gaps** — ten July fixes are in no release, and each is individually called "not exploitable" for a reason that assumes some *other* invariant holds. Do they compose? | Four pairings, each driven to a `False` or to a quoted guard | **No new `False`.** (C) `add_mutual` duplicate names × (E) the module stub: foreclosed because the body loop iterates the *original* member list, so `v.get_value()` and `v.get_type()` always come from the same member and the surviving constant is internally consistent (environment.cpp:250-254). (D) mismatched `lparams` × (E): foreclosed three times over — the body-loop def-eq catches the universe lie, `check_level` (type_checker.cpp:76-80) catches any later reference to the dangling atom, and the partial-safety gate quarantines the constant; (E) only stubs a **singleton** `.mutualDefnDecl [defn]` (AddDecl.lean:118) while the poisoning needs ≥2 members, so it cannot even be laundered. (A)+(B) driven directly through `Kernel.whnf`/`isDefEq`, and (A)+(B) fed from stored ill-typedness: both foreclosed by one line, `if (I_name != proj_sname(e)) throw` (type_checker.cpp:231) — with the coverage limit measured separately in §2.6 |
| Every `add_*` path, re-checked for the `_kernel_fresh` containment claim | §5.1 records the kernel's own generated binder capturing a caller-supplied `_kernel_fresh.N` fvar, and calls it contained because "every `add_*` path in `environment.cpp` rejects fvars in values *before* type-checking" | **Holds, and now verified path by path rather than asserted.** `add_definition` (both the safe and the unsafe branch), `add_theorem`, `add_opaque` and `add_mutual` each call `check_no_metavar_no_fvar` on the **value** before `checker.check`, and `check_constant_val` calls it on the **type** — so both halves are covered, and the code is byte-identical on `v4.32.2` and `master`. The claim needed checking because #14607 showed the *inductive* path had no such guard |
| `scope_rec_depth`, absent from `infer_type_core` and `whnf_core` on releases (#14633) | Does an unguarded recursion depth abort the kernel, as `Nat.shiftLeft` does? | **No, at reachable depths.** 10 000 nested applications type-check on `v4.32.2` with exit 0. `check_system` and the OS stack cope; this is not a second `INTERNAL PANIC` |
| Kernel-special-cased names, re-enumerated at the pin | Is any name the kernel hard-wires undeclared in *core*, i.e. claimable from a non-`prelude` module? | No. The list is `dontcare`, `eagerReduce`, `Bool.true`, the fourteen `Nat.*`, `String.ofList`, `Char.ofNat`, `List.cons`/`nil`, `Lean.reduceBool`/`reduceNat`, `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`, and the `_nested`/`_ind_fresh`/`_nested_fresh`/`_kernel_fresh` generator prefixes. `eagerReduce` is real (`Init/Core.lean`, `def eagerReduce {α : Sort u} (a : α) : α := a`) and only flips `m_eager_reduce`, a strategy flag; `dontcare` remains vacuous. §2.3's prelude precondition still bounds the whole family |

---

## 6. Sources

Three of these are pinned locally as submodules — see
[`Upstream/`](Upstream/) for the commits and for the mapping from each recorded
result back to the revision it was measured against. The source-level claims in
§2.1, §2.5 and §3.0 have been checked against those pins; the checks are listed
there rather than repeated here.

| Source | What it contributes |
| --- | --- |
| Rocq, [`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md) | **The single most valuable source for either system.** Maintainer-curated, since 8.0, with introduced/impacted/fixed/found-by fields. Lean has no equivalent. |
| [Lean Kernel Arena](https://arena.lean-lang.org/) + [repo](https://github.com/leanprover/lean-kernel-arena) | The attack corpus of §3 and the live differential-testing results. |
| Lean release notes, in [`leanprover/reference-manual`](https://github.com/leanprover/reference-manual) `Manual/Releases/` | The only place `v4.32.1`/`v4.32.2` are described as soundness releases. Note the notes systematically *understate* compiler-TCB unsoundness. |
| [`lean4lean`](https://github.com/digama0/lean4lean) `bugs-found.md` and `divergences.md` | Bugs found by formalization, and the standing kernel assumptions that are not bugs — including the prelude assumption underlying all of §2.3. |
| Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood) | The 2026 sweep: Opus 4.6 against both kernels, producing 7 proofs of `False` in Rocq plus 3 further bugs, 0 in the official Lean kernel with 4 other bugs, and proofs of `False` in `nanoda` (2) and `lean4lean` (1). |
| Leonardo de Moura, [*Who Watches the Provers?*](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) | The Lean FRO's position: multiple independent kernels are the defence. |
| Leonardo de Moura, [*Postmortem for Kernel Soundness Bug #14576*](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/) (2026-08-01) | The follow-up, and the source for §3.0 — the timeline, the `nanoda` half of the story, the FRO's remediation list (#14582, #14607–#14616, #14621/#14631/#14632), and the position that removing metaprogramming would be a category error. Revised by Joachim Breitner and Sebastian Ullrich. |
| Lawrence Paulson, [*Broken proofs and broken provers*](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html) | The view from outside both systems: Isabelle/HOL, HOL88, LCF, PVS. |
| [`nielsvoss/lean-pitfalls`](https://github.com/nielsvoss/lean-pitfalls) | The realistic failure modes — mis-stated theorems, `autoImplicit`, junk values — which are far commoner than any kernel bug. |
| Rocq stdlib `Logic/`: `Hurkens`, `Berardi`, `ClassicalFacts`, `Diaconescu`, `ChoiceFacts`, `Eqdep_dec` | The paradox library and the precise statements of §1.1. |
| [`rocq-archive/paradoxes`](https://github.com/rocq-archive/paradoxes) | `BuraliForti.v`, `Reynolds.v`, `Russell.v`, `Hurkens_Set.v`, `diaconescu.v` — the `gap` rows of §1.1. |
| Carneiro, *The Type Theory of Lean* (MSc thesis) and [Lean4Lean](https://arxiv.org/abs/2403.14064) | Relative consistency (ZFC + n inaccessibles, as a schema), and the acknowledged gaps in the metatheory. |

**One timeline point is worth stating plainly.** De Moura's March 2026 post
observes that Opus 4.6 *"did not manage to find a proof of false in the Lean
official kernel"*, in contrast to seven in Rocq — a fair summary of the evidence
then available. Four months later, **July 2026 produced five distinct axiom-free
proofs of `False` in the official Lean kernel** (#14484, #14576, #14613, #14616,
plus the #14609 module-system break), all found by AI-assisted auditing, all
fixed within hours to days, and one of them exploitable *through* `comparator`.
Three of the arena's independent checkers currently score a perfect 57/57 on the
attack corpus where the official kernel scores 56/57.

**"Fixed" there means fixed on `master`.** Of those five, **three** — #14609,
#14613 and #14616 — are in no released toolchain as of 2026-08-01, and each is an
axiom-free `False` against `v4.33.0-rc1`. Two now have artifacts here:
[`ModuleSystem/`](KernelDefects/Lean/ModuleSystem/) and
[`Universes/`](KernelDefects/Lean/Universes/); #14616 is still a gap (§5). The
count was two until the 08-01 sweep was re-run without a path filter — see §5.2.
Only #14484 and #14576 got their own releases. #14609, #14613, #14615 and #14616
all landed on `master` on 2026-07-30/31, after `v4.32.2` was tagged (07-28) and
after `v4.33.0-rc1` (07-15); and as of the pin, **none of them has been
cherry-picked onto `releases/v4.33.0`**, whose HEAD is still `f839b65ba4`
(#14577). That is the backport gap of
[`Reports/2026-07-29-lean-4.33-…`](Reports/2026-07-29-lean-4.33-backport-gap.md)
recurring with a second pair of fixes, four days after it was recorded as
resolved. The distinction is easy to lose when reading a tracker — `closed` looks
the same either way — and it is the difference between a bug and an exposure.

The August postmortem names the auditing. #14576 came out of an AI-assisted
"disproof" of the Collatz conjecture; #14607–#14616 came from Daniel Selsam at
OpenAI pointing a cybersecurity-specialised AI at the kernel on the FRO's behalf.
The clause worth carrying forward is the one attached to that second batch:
**all of them were caught by `nanoda`.** The differential-testing defence did its
job on every bug of the wave except the one bug it was itself blind to (§3.0).

**Updated 2026-08-18, and the update matters more than the original paragraph.**
The same reporter found two more — [#14806](https://github.com/leanprover/lean4/pull/14806)
and [#14807](https://github.com/leanprover/lean4/pull/14807) — three weeks later,
with three axiom-free `False`s between them, all live on `v4.33.0` and
`v4.34.0-rc1`. So the running total for 2026 is **seven** distinct axiom-free
proofs of `False` in the official Lean kernel, and the count of `master`-only
fixes with no release behind them is **five** (§2.1). Two clauses above need
qualifying:

* *"all of them were caught by `nanoda`"* held for July's batch and does not hold
  for August's: `nanoda` accepts `proj-of-subst-prop` (§3.0). The July agreement
  needed two unrelated bugs; this one needs one bug present in both.
* *"three of the arena's independent checkers score a perfect 57/57 where the
  official kernel scores 56/57"* was measured on 08-01 against a fourteen-attack
  corpus. The corpus is now eighteen and the `official` track is `4.33.0`; the
  official kernel fails four of them, not one.

There is no postmortem for the August pair, and as of this survey no public
discussion of them at all — not on Zulip, X or Mathstodon. The primary sources
are the two PR descriptions, which are unusually detailed and are cited directly
in [`Reports/2026-08-18-defeq-…`](Reports/2026-08-18-defeq-cache-and-stuck-sort.md).

The reasonable conclusion is not that one system is sounder than the other, nor
that the situation has deteriorated. It is that the *rate of discovery* changed
in 2026, in both systems, for the same reason — and that a static catalog is now
a snapshot. Hence the survey date, and hence §5's last item. The August pair is
the second confirmation of that in three weeks: this file was seventeen days old
and already understated the count by two.
