import Lean
/-!
# The Lean Kernel Arena reject-corpus, re-run against the official kernel from inside Lean

Category (see `../../../README.md`): **audit**. A search that comes up empty is
the result. No `sorry`, no `axiom`; every verdict is `#guard_msgs`-checked and the
file exits 0 under `lean --trust=0`.

`CATALOG.md` §3.1 tabulates the arena's named probes — fourteen when this file
was written, eighteen since 2026-08-18 — and §5 calls the corpus the single
largest Lean-side gap. An arena test is an **export** test: it
hands a checker a serialized environment, so most of the corpus is a statement
about a checker, not about a Lean source file. This file measures the part that
*is* reachable from inside Lean — the probes whose term is a `Declaration`
that can be handed to `Kernel.Environment.addDecl` — and records, with the exact
kernel messages, that `v4.32.2` rejects every one of them except the one the arena
itself scores `either`.

## Toolchain

`lean --trust=0 RejectCorpus.lean` exits **0** on all seven pins —
`v4.27.0-rc1`, `v4.30.0-rc2`, `v4.31.0`, `v4.32.0`, `v4.32.1`, `v4.32.2`,
`v4.33.0-rc1` — so every message asserted below is byte-identical across the
whole released range, including the `nested-nonuniform-param` acceptance.

Three measurement notes carried from `../../../README.md`:

* `Lean.addDecl` is **asynchronous** on `v4.32.x`, so `try`/`catch` around it
  reports kernel rejections as successes. `(← getEnv).toKernelEnv.addDecl` is the
  synchronous path and is what every probe below uses.
* Judge by exit code and by the asserted message, never by grepping for "error".
* Each probe is paired with a twin the same procedure treats differently, so an
  "accepted" or "rejected" verdict carries information.

## What is *not* here, and why

| Arena test | Reachable from inside Lean? |
| --- | --- |
| `ctor-num-fields`, `rec-k-lie`, `nat-rec-k-lie`, `nat-rec-rules` | **Yes, but not through `addDecl`** — the kernel derives `numFields`, `k` and the recursor rules and the wire format has nowhere to put a lie. They are reachable by overwriting the stored `ConstantInfo`; see `../../../EscapeHatches/Lean/ArenaTrustedMetadata.lean`, which is where they live because they are escape hatches rather than defects |
| `large-elim-param` | **No.** The term is an exported recursor for `MyBool.{u} : Sort u` that large-eliminates; the kernel synthesises recursors itself, so the only in-Lean question is whether its own `is_not_zero` ever says a possibly-zero level is nonzero. Asked and answered in `../Fuzz/IsNotZeroFuzzer.lean` — 360 spellings, 0 unsound |
| `nat-rec-rules` (as an *export*) | **No** in that form, for the same reason; the lie is expressible only post-hoc, above |
| `level-index-out-of-order`, `sparse-name-index` | **No.** These are properties of the NDJSON serialization — `lean4export` emits internalization-table references densely and in order but the spec permits any integers. There is no Lean term that expresses "referred to name #7 before defining it" |
| `perf/`, `tutorial/` | Out of scope here: timing and a 135-case accept/reject taxonomy, neither of which is an probe |
| `undecidability/` | Independently measured in `../Metatheory/` |
| `extra-rec` (added 2026-08-18) | **No.** A second recursor named `rogue`, of type `False`, inserted into `False`'s inductive group. The kernel derives an inductive group's recursors, so the wire format is again the only place the lie fits; the arena injects it with the kernel-bypassing `Environment.lakeAdd`. Same class as the `ctor-num-fields` row above |

**Four probes were added to the corpus on 2026-08-18, and three of them are
reachable from inside Lean — which is why this file's verdict is not extended to
them here.** `rec-missing-ih`, `proj-of-stuck-prop` and `proj-of-subst-prop` are
lean4#14806 and lean4#14807: the kernel *accepts* all three on every released
toolchain, so they are defects rather than negative results, and they live in
`../../../KernelDefects/Lean/DefEq/` with their own control and verify script.
The paragraph above — "the kernel rejects every reachable one" — was true of the
fourteen-probe corpus and is not true of the eighteen-probe one. See
`../../../Reports/2026-08-18-defeq-cache-and-stuck-sort.md`.
-/

open Lean Elab Command Meta

private def kprobe (tag : String) (d : Declaration) : CommandElabM Unit := liftTermElabM do
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .error e => logInfo m!"{tag}: REJECTED -- {← (e.toMessageData {}).toString}"
  | .ok _    => logInfo m!"{tag}: ACCEPTED"

/-! ## 1. `proj-of-prop` — a projection typed by inferring rather than checking

The arena's term is `Expr.proj Wrapper 0 (Wrapper.mk True.intro)`, a
`True.intro` sitting in a slot that expects a `False`. The elaborator never emits
a raw `Expr.proj` from `(…).p` syntax — it desugars to the projection *function* —
so the arena builds the declaration programmatically under `debug.skipKernelTC`
purely to get the export produced. Handed to the kernel with the option off, it is
the kernel's `infer_app` that has to object. -/

structure Wrapper : Prop where
  mk ::
  p : False

/--
info: proj-of-prop: REJECTED -- (kernel) application type mismatch
  Wrapper.mk True.intro
argument has type
  True
but function has type
  False → Wrapper
-/
#guard_msgs in
run_cmd kprobe "proj-of-prop" (.thmDecl {
  name := `P1, levelParams := [], type := mkConst ``False,
  value := .proj `Wrapper 0 (mkApp (mkConst ``Wrapper.mk) (mkConst ``True.intro)) })

/-! The twin that must be accepted: the same projection over an honest argument.
`Wrapper.mk h` really does have a `False` in the slot, so `.proj` is well typed —
and the declaration is a conditional `False`, which is what makes it safe. -/

/-- info: proj-of-prop CONTROL (honest argument): ACCEPTED -/
#guard_msgs in
run_cmd kprobe "proj-of-prop CONTROL (honest argument)" (.thmDecl {
  name := `P1c, levelParams := [],
  type := .forallE `h (mkConst ``False) (mkConst ``False) .default,
  value := .lam `h (mkConst ``False) (.proj `Wrapper 0 (mkApp (mkConst ``Wrapper.mk) (.bvar 0))) .default })

/-! ## 2. `proj-non-structure` — project out of a two-constructor type

The hope is a checker that infers the field type from the *first* constructor
without checking that the inductive has exactly one. -/

inductive Bad : Prop
  | mk1 : False → Bad
  | mk2 : True → Bad

/--
info: proj-non-structure: REJECTED -- (kernel) invalid projection
  (Bad.mk2 True.intro).1
-/
#guard_msgs in
run_cmd kprobe "proj-non-structure" (.thmDecl {
  name := `P2, levelParams := [], type := mkConst ``False,
  value := .proj `Bad 0 (mkApp (mkConst ``Bad.mk2) (mkConst ``True.intro)) })

/-! ## 3. `k-rec-conv` — broken K-like reduction makes `fun x => x ≡ fun _ => y`

A regression test for a `sokonanoda` bug. `T` is a function type whose second
argument is an equation between `fun x => x` and `fun _ => y`; `t1` eliminates it
with `Eq.rec`, `t2` ignores it. A checker whose K-like reduction fires where it
should not equates them. -/

def T : Type := (y : Nat) → @Eq (Nat → Nat) (fun x => x) (fun _ => y) → Nat
def t2 : T := fun _ _ => 0
def t1 : T := fun y h => @Eq.rec (Nat → Nat) (fun x => x) (fun _ _ => Nat) 0 (fun _ => y) h

/--
info: k-rec-conv: REJECTED -- (kernel) declaration type mismatch, 'P3' has type
  t1 = t1
but it is expected to have type
  t1 = t2
-/
#guard_msgs in
run_cmd kprobe "k-rec-conv" (.thmDecl {
  name := `P3, levelParams := [],
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``T) (mkConst ``t1) (mkConst ``t2),
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``T) (mkConst ``t1) })

/-! The twin: `t1 = t1` by `rfl` is accepted, so the rejection above is about the
two sides and not about the shape of the declaration. -/

/-- info: k-rec-conv CONTROL (t1 = t1): ACCEPTED -/
#guard_msgs in
run_cmd kprobe "k-rec-conv CONTROL (t1 = t1)" (.thmDecl {
  name := `P3c, levelParams := [],
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``T) (mkConst ``t1) (mkConst ``t1),
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``T) (mkConst ``t1) })

/-! ## 4. `bogus1` — the calibration case

Not an probe: a blatant `0 = 1` proved by `True.intro`. It exists so that a
checker which rejects nothing else is still known to reject *something*, and it is
this repository's `debug.skipKernelTC` control (`EscapeHatches/Lean/Metaprogramming.lean`)
under another name. -/

/--
info: bogus1: REJECTED -- (kernel) declaration type mismatch, 'P4' has type
  True
but it is expected to have type
  0 = 1
-/
#guard_msgs in
run_cmd kprobe "bogus1" (.thmDecl {
  name := `P4, levelParams := [],
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 1),
  value := mkConst ``True.intro })

/-! ## 5. `constlevels` — a `const` node carrying the wrong number of levels

lean4#10577: uninitialized memory in `lazy_delta_reduction_step`. The arena
records that the official kernel at 4.28/4.29 **segfaults** on this export. It is
fully reachable from inside Lean — `Expr.const` takes the level list from the
caller — and `v4.32.2` rejects all three arities with a diagnostic, in the term
position, in the value position and in the too-few direction. -/

/--
info: constlevels/too-many, in a term: REJECTED -- (kernel) incorrect number of universe levels parameters for 'Nat.zero', #0 expected, #1 provided
-/
#guard_msgs in
run_cmd kprobe "constlevels/too-many, in a term" (.thmDecl {
  name := `P5, levelParams := [], type := mkConst ``True,
  value := .app (.const `Nat.zero [.zero]) (mkConst ``True.intro) })

/--
info: constlevels/too-many, as a value: REJECTED -- (kernel) incorrect number of universe levels parameters for 'Nat', #0 expected, #1 provided
-/
#guard_msgs in
run_cmd kprobe "constlevels/too-many, as a value" (.defnDecl {
  name := `P6, levelParams := [], hints := .abbrev, safety := .safe,
  type := .sort (.succ .zero), value := .const `Nat [.zero] })

/--
info: constlevels/too-few: REJECTED -- (kernel) incorrect number of universe levels parameters for 'Eq', #1 expected, #0 provided
-/
#guard_msgs in
run_cmd kprobe "constlevels/too-few" (.defnDecl {
  name := `P7, levelParams := [], hints := .abbrev, safety := .safe,
  type := .sort (.succ .zero), value := .const `Eq [] })

/-! ## 6. `nested-nonuniform-param` — the one that is still open, and is accepted

lean4#14582, Arthur Adjedj's follow-up to #14577, **OPEN** as of 2026-08-01. The
constructor puts a *constant* where the parameter belongs:

    E.mk : (w : W) → L (E ⟨false⟩) → E w

`E ⟨false⟩` is type-correct, so re-type-checking the nested application does not
catch it; a checker must additionally verify that the argument *is* the expected
parameter. The arena scores it `either` and gives the reason: with `L` phantom,
`E w` is `Unit` for every `w`, so nothing unsound follows — and the variant where
`L` really stores an `α` is caught by the positivity check.

Both halves reproduce here, from inside Lean, on `v4.32.2`. The rejection message
for the storing variant is the same one the arena quotes. This is the third
independent derivation of that negative result: the arena's, `CATALOG.md` §5.1's
last row, and this. -/

inductive W : Type where | mk (p : Bool)
inductive Lphantom (α : Type) : Type where | mk
inductive Lstoring (α : Type) : Type where | mk (a : α)

private def mkE (name : Name) (wrapper : Name) : Declaration :=
  let Ef := mkApp (mkConst name) (mkApp (mkConst ``W.mk) (mkConst ``Bool.false))
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
              mkForall `l .default (mkApp (mkConst wrapper) Ef) (mkApp (mkConst name) (mkBVar 1))
  .inductDecl [] 1 [{ name := name, type := Et, ctors := [{ name := name ++ `mk, type := ct }] }] false

/-- info: nested-nonuniform-param (L phantom): ACCEPTED -/
#guard_msgs in
run_cmd kprobe "nested-nonuniform-param (L phantom)" (mkE `Ep ``Lphantom)

/--
info: nested-nonuniform-param CONTROL (L stores an α): REJECTED -- (kernel) arg #2 of '_nested.Lstoring_1.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
run_cmd kprobe "nested-nonuniform-param CONTROL (L stores an α)" (mkE `Es ``Lstoring)

/-! ## 7. `proof-irrel` — an *accept* test, restated without axioms

The arena states it with six axioms. It does not need them: what is under test is
only that `h a ≡ h b` when `P : Prop`, and that is stateable as a hypothesis. A
checker comparing the two proofs structurally wrongly rejects this. -/

theorem arena_proof_irrel {A : Type} {a b : A} {P : Prop} {Q : P → Prop}
    (foo : ∀ h : A → P, Q (h b)) : ∀ h : A → P, Q (h a) := foo

/-- info: 'arena_proof_irrel' does not depend on any axioms -/
#guard_msgs in #print axioms arena_proof_irrel

/-! The twin that must fail: drop `P : Prop` down to `P : Type` and there is no
proof irrelevance, so the same term is rejected. -/

/--
error: Type mismatch
  foo
has type
  ∀ (h : A → P), Q (h b)
but is expected to have type
  ∀ (h : A → P), Q (h a)
-/
#guard_msgs in
example {A : Type} {a b : A} {P : Type} {Q : P → Prop}
    (foo : ∀ h : A → P, Q (h b)) : ∀ h : A → P, Q (h a) := foo

/-! ## 8. `level-imax-leq` and `level-imax-normalization`

Both are level-arithmetic probes that caught an external checker — `nanoda` and
`lean4lean` respectively. Neither has a Lean *source* form, because a level
comparison is not a declaration; the reachable question is whether the official
kernel's own `is_equivalent` accepts the two specific pairs. `Kernel.isDefEq` on
two sorts is that question exactly.

The systematic version of this is `../Fuzz/LevelFuzzer.lean` (60,000 pairs against
a denotational oracle, 0 unsound, 738 incomplete); these two are the named
instances pinned as regression cases. -/

private def sortPair (a b : Level) : MetaM Bool := do
  match Lean.Kernel.isDefEq (← getEnv) {} (mkSort a) (mkSort b) with
  | .ok r => pure r
  | _     => pure false

/--
info: level-imax-leq          Sort (imax u v + 1) ≡ Sort (imax u v) : false
level-imax-normalization Sort (imax 0 v) ≡ Sort (imax 0 v + 1) : false
CONTROL                  Sort (max u v) ≡ Sort (max v u)      : true
-/
#guard_msgs in
run_cmd liftTermElabM do
  let u := Level.param `u
  let v := Level.param `v
  let iuv := Level.imax u v
  let i0v := Level.imax .zero v
  logInfo m!"level-imax-leq          Sort (imax u v + 1) ≡ Sort (imax u v) : {← sortPair (.succ iuv) iuv}\n\
             level-imax-normalization Sort (imax 0 v) ≡ Sort (imax 0 v + 1) : {← sortPair i0v (.succ i0v)}\n\
             CONTROL                  Sort (max u v) ≡ Sort (max v u)      : {← sortPair (.max u v) (.max v u)}"

/-! ## 9. Verdict, and the arithmetic behind it

The corpus splits cleanly on the *form the arena stores the test in*, and that
split is the right first cut at "reachable from inside Lean":

* **Ten tests have a `.lean` source** — `bogus1`, `ctor-num-fields`, `k-rec-conv`,
  `nested-nonuniform-param`, `nested-unused-param`, `proj-non-structure`,
  `proj-of-imax-prop`, `proj-of-prop`, `proof-irrel`, `rec-k-lie`. The arena
  itself builds these from inside Lean; the export is a by-product.
* **Eight are `.ndjson` only** — `constlevels`, `large-elim-param`,
  `level-imax-leq`, `level-imax-normalization`, `level-index-out-of-order`,
  `nat-rec-k-lie`, `nat-rec-rules`, `sparse-name-index`. These are hand-written
  serialized environments with no Lean source anywhere.

The second cut is the useful one, because the `.ndjson`/`.lean` split is not the
same as reachable/unreachable. Three of the eight NDJSON-only tests *are*
reachable: `constlevels` directly, as §5 shows, because `Expr.const` takes its
level list from the caller; and `nat-rec-rules`/`nat-rec-k-lie` by the same
post-hoc `ConstantInfo` overwrite the arena already uses for their `.lean`
siblings (`../../../EscapeHatches/Lean/ArenaTrustedMetadata.lean` §2–§3).

Of the fourteen named probes in `CATALOG.md` §3.1, seven have a term that is
an ordinary `Declaration` and can simply be handed to `addDecl`:

| Probe | This file | Verdict on `v4.32.2` |
| --- | --- | --- |
| `proj-of-prop` | §1 | rejected |
| `proj-non-structure` | §2 | rejected |
| `k-rec-conv` | §3 | rejected |
| `bogus1` | §4 | rejected |
| `constlevels` | §5 | rejected, three arities |
| `proj-of-imax-prop` | — | **accepted**; the one reject-test a released kernel fails (#14613), already exhibited in `../../../KernelDefects/Lean/Universes/ImaxPropLaundering.lean` |
| `nested-unused-param` | — | fixed in `v4.32.2` (#14576); rebuilding it needs the published `Expr.hash` collision constants, so it is recorded rather than re-measured |

Four more (`ctor-num-fields`, `rec-k-lie`, `nat-rec-k-lie`, `nat-rec-rules`) are
reachable only by overwriting stored metadata and live in `EscapeHatches/`. Two
(`level-imax-leq`, `level-imax-normalization`) are level comparisons rather than
declarations and are pinned as kernel queries in §8. One (`large-elim-param`)
reduces to the kernel's own `is_not_zero`, answered in `../Fuzz/IsNotZeroFuzzer.lean`.

Nothing here is a new defect. That is the result: **every arena probe whose
term the released kernel can even be handed is rejected by it, except the two
already on the books** — #14613, which has an exhibit, and #14582's
`nested-nonuniform-param`, which is accepted and is a known non-construction for the
reason §6's own control reproduces.
-/
