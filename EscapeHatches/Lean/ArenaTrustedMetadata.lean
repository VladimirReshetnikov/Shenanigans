module

public import Lean
import all Lean.Environment

/-!
# The arena's "trusted metadata" family, reached from inside Lean

Category (see `../../README.md`): **escape hatch**. Three closed, axiom-free
`theorem … : False`, each accepted by `lean --trust=0` with exit code 0 and each
reported by `#print axioms` as depending on nothing. The cost is disclosed by
neither the audit nor a `set_option`: it is a `modifyEnv` that writes a
`ConstantInfo` straight into `Environment.checked.constants`, past the kernel.

## Why this file exists

`CATALOG.md` §3.1 lists `ctor-num-fields`, `rec-k-lie`/`nat-rec-k-lie` and
`nat-rec-rules` in the Lean Kernel Arena's attack corpus and files them as a
*trusted-metadata* class: the export lies to the checker about a declaration's
derived metadata. The natural reading — and the one this repository worked from —
is that such a test cannot be built from inside Lean, because
`Kernel.Environment.addDecl` derives `numFields`, `k` and the recursor rules
itself and never takes them from the caller.

That reading is **half right, and the wrong half is load-bearing.** It is true of
`addDecl`, and §4 measures it: `Declaration.inductDecl` has no field to put the
lie in. It is false of Lean as a whole, and the arena's own sources prove it —
`tests/ctor-num-fields.lean` and `tests/rec-k-lie.lean` are ordinary Lean modules,
not hand-written NDJSON. They declare the inductive honestly, let the kernel
derive the metadata, and then **overwrite the derived `ConstantInfo` in place**.
Every subsequent declaration goes through a fully checked `addDecl` — and checks
against the corrupted environment.

So this is not `debug.skipKernelTC` (`Metaprogramming.lean`), where the kernel is
switched off. Here the kernel runs on every declaration in the file, and accepts
each one *correctly given what it was told*. What is corrupted is the premise,
not the inference. §1–§3 each show the same declaration **rejected** by the kernel
before the lie and **rejected again** after it is withdrawn, with acceptance only
in between; that is the control.

## Where it sits among the audit-blind routes

`CATALOG.md` §1.2 records two Lean routes invisible to `#print axioms`:
`debug.skipKernelTC` (needs an option) and the module-boundary `partial` stub of
#14609 (needs a module boundary and a `partial def`). This is a **third**: no
option, no `partial`, no kernel defect. Its own precondition, measured in §5, is
that `Environment`'s constructor is `private`, so the file must be a `module` that
says `import all Lean.Environment`. That is a disclosure in the *source*, and
there is no corresponding disclosure in the *audit*.

The category call is worth stating explicitly, because the audit signature here is
the one `../../README.md`'s table assigns to `KernelDefects/` — closed `False`,
"nothing at all". The tiebreaker is that table's own gloss: the third row *"is the
only one that is anybody's fault"*. This is nobody's fault. The kernel's every
decision in this file is correct on the input it was given, and the input was
falsified by a caller with legitimate write access to the environment. Ground rule
1 puts it here: a route that costs you an out-of-kernel write is a hatch, however
quiet the audit is about it.

It is not a kernel bug and is not filed as one: overwriting the environment is the
`.olean`-forgery threat model of
[lean4#13615](https://github.com/leanprover/lean4/issues/13615) executed
in-process, and the #14576 postmortem's position applies verbatim — the elaborator
is untrusted by design. The finding is about the **audit**, which reports nothing,
and about the arena classification, which this file corrects.

## Toolchain

| Toolchain | `lean --trust=0 ArenaTrustedMetadata.lean` |
| --- | --- |
| `v4.27.0-rc1` | exit 1 — **but not because the attack failed**; see below |
| `v4.30.0-rc2` | exit 0 |
| `v4.31.0` | exit 0 |
| `v4.32.0` | exit 0 |
| `v4.32.1` | exit 0 |
| `v4.32.2` (pin) | exit 0 |
| `v4.33.0-rc1` | exit 0 |

Exit 0 means every `#guard_msgs` in the file matched, including the three
`#print axioms` lines and all nine kernel-verdict probes.

`v4.27.0-rc1` refuses `#print axioms` *inside* a `module` — `cannot use #print
axioms in a module; consider … placing the command in a separate file` — and that
is the only thing it objects to. With the three audit commands deleted the same
file is exit 0 there as well, so the route is open on all seven pins and the
audit has to move to an importing module on the oldest one. §6 does that anyway,
and gets the same answer.

Re-run with `../verify.ps1` after adding `'ArenaTrustedMetadata'` to its
`$leanAccept` list.
-/

open Lean Elab Command

/-- Overwrite a `ConstantInfo` in every map the environment answers from,
including the kernel-side `checked` environment. This is the whole attack. -/
private def poison (ci : ConstantInfo) : CommandElabM Unit :=
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci } }

/-- Submit a declaration to the kernel synchronously. `addDecl` is asynchronous on
`v4.32.x`, so a `try`/`catch` around it reports kernel rejections as successes;
`(← getEnv).toKernelEnv.addDecl` is the honest measurement. -/
private def kprobe (tag : String) (d : Declaration) : CommandElabM Unit := liftTermElabM do
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .error e => logInfo m!"{tag}: REJECTED -- {← (e.toMessageData {}).toString}"
  | .ok _    => logInfo m!"{tag}: ACCEPTED"

/-! ## 1. `ctor-num-fields` — a one-field structure that claims zero fields

Definitional eta for a structure is keyed on the constructor's `numFields`. Claim
zero and the kernel treats `S` as unit-like, so `S.mk true ≡ S.mk false`. The
field is still there and still projects, so `(S.mk false).f` is `false`. -/

public structure S where
  f : Bool

private def etaThm : Declaration :=
  let Sc := mkConst ``S
  let mk (b : Name) := mkApp (mkConst ``S.mk) (mkConst b)
  .thmDecl { name := `etaProbe, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) Sc (mk ``Bool.true) (mk ``Bool.false), value := mkApp2 (mkConst ``Eq.refl [1]) Sc (mk ``Bool.true) }

/--
info: CONTROL, honest numFields: REJECTED -- (kernel) declaration type mismatch, 'etaProbe' has type
  S.mk true = S.mk true
but it is expected to have type
  S.mk true = S.mk false
-/
#guard_msgs in
run_cmd kprobe "CONTROL, honest numFields" etaThm

run_cmd do
  let .ctorInfo cv ← liftTermElabM (getConstInfo ``S.mk) | throwError "S.mk is not a constructor"
  poison (.ctorInfo { cv with numFields := 0 })

/-- info: POISONED, numFields := 0: ACCEPTED -/
#guard_msgs in
run_cmd kprobe "POISONED, numFields := 0" etaThm

public theorem h : S.mk true = S.mk false := rfl

public theorem ParadoxCtorNumFields : False :=
  show if (S.mk false).f then True else False from h ▸ trivial

/-- info: 'ParadoxCtorNumFields' does not depend on any axioms -/
#guard_msgs in #print axioms ParadoxCtorNumFields

run_cmd do
  let .ctorInfo cv ← liftTermElabM (getConstInfo ``S.mk) | throwError "S.mk is not a constructor"
  poison (.ctorInfo { cv with numFields := 1 })   -- withdraw the lie

/--
info: CONTROL, numFields restored: REJECTED -- (kernel) declaration type mismatch, 'etaProbe' has type
  S.mk true = S.mk true
but it is expected to have type
  S.mk true = S.mk false
-/
#guard_msgs in
run_cmd kprobe "CONTROL, numFields restored" etaThm

/-! ## 2. `rec-k-lie` — K-like reduction claimed for a two-constructor type

`RecursorVal.k` says the recursor may reduce without inspecting its major
premise, which is sound only for a single-constructor, field-free inductive.
Claim it for `MyBool` and `MyBool.rec a b m` reduces to `a` whatever `m` is.

The lie is then **withdrawn**, and that is what makes the exhibit closed rather
than merely misleading: `disc MyBool.tt` is `False` under honest metadata — stated
as a `rfl` before anything is touched — so once `k` is restored, the already
stored `bad : disc MyBool.tt` is a proof of `False` at face value. -/

public inductive MyBool | ff | tt

public noncomputable def disc : MyBool → Prop := fun b => MyBool.rec True False b

/-- Under honest metadata, `disc MyBool.tt` *is* `False`. -/
example : disc MyBool.tt = False := rfl

private def kThm : Declaration :=
  .thmDecl { name := `kLieProbe, levelParams := [], type := mkApp (mkConst ``disc) (mkConst ``MyBool.tt), value := mkConst ``True.intro }

/--
info: CONTROL, honest k: REJECTED -- (kernel) declaration type mismatch, 'kLieProbe' has type
  True
but it is expected to have type
  disc MyBool.tt
-/
#guard_msgs in
run_cmd kprobe "CONTROL, honest k" kThm

run_cmd do
  let .recInfo rv ← liftTermElabM (getConstInfo ``MyBool.rec) | throwError "MyBool.rec is not a recursor"
  poison (.recInfo { rv with k := true })

/-- info: POISONED, k := true: ACCEPTED -/
#guard_msgs in
run_cmd kprobe "POISONED, k := true" kThm

public theorem bad : disc MyBool.tt := True.intro

run_cmd do
  let .recInfo rv ← liftTermElabM (getConstInfo ``MyBool.rec) | throwError "MyBool.rec is not a recursor"
  poison (.recInfo { rv with k := false })   -- withdraw the lie

/--
info: CONTROL, k restored: REJECTED -- (kernel) declaration type mismatch, 'kLieProbe' has type
  True
but it is expected to have type
  disc MyBool.tt
-/
#guard_msgs in
run_cmd kprobe "CONTROL, k restored" kThm

public theorem ParadoxRecKLie : False := bad

/-- info: 'ParadoxRecKLie' does not depend on any axioms -/
#guard_msgs in #print axioms ParadoxRecKLie

/-! ## 3. `nat-rec-rules` — the recursor's computation rules, swapped

The arena exports this one as NDJSON only (`nat-rec-rules.ndjson`) and describes
it as a checker that compared imported recursor rules against themselves rather
than against independently reconstructed ones. The same lie is expressible here,
and against the official kernel: swap the two `RecursorRule.rhs` values so the
rule for `NB.tt` returns the `NB.ff` minor premise.

This is the member of the family the arena has no `.lean` source for, so §3 is new
here rather than a reproduction. -/

public inductive NB | ff | tt

public noncomputable def disc2 : NB → Prop := fun b => NB.rec True False b

example : disc2 NB.tt = False := rfl

private def rThm : Declaration :=
  .thmDecl { name := `ruleLieProbe, levelParams := [], type := mkApp (mkConst ``disc2) (mkConst ``NB.tt), value := mkConst ``True.intro }

/-- Swapping twice is the identity, so the same command both installs and
withdraws the lie. -/
private def swapRules : CommandElabM Unit := do
  let .recInfo rv ← liftTermElabM (getConstInfo ``NB.rec) | throwError "NB.rec is not a recursor"
  let [r0, r1] := rv.rules | throwError "expected exactly two computation rules"
  poison (.recInfo { rv with rules := [{ r0 with rhs := r1.rhs }, { r1 with rhs := r0.rhs }] })

/--
info: CONTROL, honest rules: REJECTED -- (kernel) declaration type mismatch, 'ruleLieProbe' has type
  True
but it is expected to have type
  disc2 NB.tt
-/
#guard_msgs in
run_cmd kprobe "CONTROL, honest rules" rThm

run_cmd swapRules

/-- info: POISONED, rules swapped: ACCEPTED -/
#guard_msgs in
run_cmd kprobe "POISONED, rules swapped" rThm

public theorem bad2 : disc2 NB.tt := True.intro

run_cmd swapRules   -- withdraw the lie

/--
info: CONTROL, rules restored: REJECTED -- (kernel) declaration type mismatch, 'ruleLieProbe' has type
  True
but it is expected to have type
  disc2 NB.tt
-/
#guard_msgs in
run_cmd kprobe "CONTROL, rules restored" rThm

public theorem ParadoxRecRules : False := bad2

/-- info: 'ParadoxRecRules' does not depend on any axioms -/
#guard_msgs in #print axioms ParadoxRecRules

/-! ## 4. The half of the premise that *is* true: `addDecl` cannot be lied to

`Declaration.inductDecl` carries `InductiveType`s whose constructors are just
`{ name, type }`. There is no `numFields` field, no `k` field and no `rules`
field anywhere in the wire format — the kernel computes all three from the
constructor telescopes. Feeding a raw `inductDecl` with a one-field constructor
therefore yields `numFields = 1` no matter what the caller wanted. -/

/-- info: kernel-derived Q.mk.numFields = 1 -/
#guard_msgs in
run_cmd liftTermElabM do
  let d : Declaration := .inductDecl [] 0
    [{ name := `Q, type := .sort 1,
       ctors := [{ name := `Q.mk, type := .forallE `f (mkConst ``Bool) (mkConst `Q) .default }] }] false
  match (← getEnv).toKernelEnv.addDecl {} d with
  | .error e => logInfo m!"raw inductDecl REJECTED: {← (e.toMessageData {}).toString}"
  | .ok kenv =>
    let some (.ctorInfo cv) := kenv.find? `Q.mk | throwError "no constructor"
    logInfo m!"kernel-derived Q.mk.numFields = {cv.numFields}"

/-! ## 5. What the route does cost, and where that cost shows

`Environment`'s constructor is `private`, so the `{ env with … }` above does not
elaborate in an ordinary file:

```
$ lean --trust=0 plain.lean
plain.lean:5:23: error: invalid {...} notation, constructor for `Environment`
  is marked as private
```

The file must therefore be a `module` and must say `import all Lean.Environment`.
That is a real precondition and it is visible to anyone reading the source — which
is exactly the property `#print axioms` does not have. The asymmetry is the point
of filing this as an escape hatch rather than a defect: **the cost is legible in
the input and invisible in the audit.**

The remedy is the same one `Metaprogramming.lean` §3 argues for: an independent
re-check of the `.olean` against a kernel that re-derives the metadata instead of
importing it. It is not available from *inside* the file — but it is available,
and §7 runs it. Each of §1–§3 exhibits the miniature of that re-check — the same
declaration, rejected by the same kernel, once the environment says what it should
have said all along.

## 6. What crosses the module boundary, measured

Two separate questions, and they have opposite answers.

**The `False` crosses.** Compiling this file to an `.olean` and importing it gives
an audit that is clean *in the importing module too* — the importer neither
imports `Lean` nor runs a metaprogram:

```
$ lean --trust=0 -o ArenaTrustedMetadata.olean ArenaTrustedMetadata.lean   # exit 0
$ cat Consumer.lean
module
public import ArenaTrustedMetadata
#print axioms ParadoxCtorNumFields
#print axioms ParadoxRecKLie
#print axioms ParadoxRecRules
$ LEAN_PATH=. lean --trust=0 Consumer.lean                                 # exit 0
'ParadoxCtorNumFields' does not depend on any axioms
'ParadoxRecKLie' does not depend on any axioms
'ParadoxRecRules' does not depend on any axioms
```

**The corruption does not — because §1–§3 withdrew it.** The importer sees honest
metadata, so it cannot repeat the trick:

```
$ cat Consumer2.lean
module
public import ArenaTrustedMetadata
example : S.mk true = S.mk false := rfl
$ LEAN_PATH=. lean --trust=0 Consumer2.lean                                # exit 1
Consumer2.lean:3:36: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  { f := true } = { f := false }
```

**Withdrawing it is not optional bookkeeping.** A file that installs the lie and
*stops* ships the corrupted `ConstantInfo` in its `.olean`, and every importer
inherits it — `S2.mk true = S2.mk false` then holds by plain `rfl` in a module
with no `import Lean`, no `import all`, and no metaprogram of its own:

```
$ cat Persist.lean
module
public import Lean
import all Lean.Environment
open Lean Elab Command
public structure S2 where
  f : Bool
run_cmd do
  let .ctorInfo cv ← liftTermElabM (getConstInfo ``S2.mk) | throwError "no"
  let ci : ConstantInfo := .ctorInfo { cv with numFields := 0 }
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci } }
public theorem h2 : S2.mk true = S2.mk false := rfl
$ cat PersistUse.lean
module
public import Persist
public theorem inherited : S2.mk true = S2.mk false := rfl
$ LEAN_PATH=. lean --trust=0 -o Persist.olean Persist.lean                 # exit 0
$ LEAN_PATH=. lean --trust=0 PersistUse.lean                               # exit 0
```

That is the sharpest form of the finding, and it is why this is filed as a hatch
rather than a curiosity: the derived metadata is **serialized**, so one dependency
can make definitional eta wrong for every module downstream of it, with nothing in
any downstream file to read. The contrast with Rocq's #22287
(`../../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v`) is exact and
inverted — there, `coqchk` rejects the `.vo` and a `Require` of it fails at the
`Require` line, so what is lost is the *local* audit and not a library. Here the
local audit is what is lost *and* the library is what carries it.

## 7. `leanchecker`'s verdict, measured

§5 called the independent re-check a remedy without running it, which left the
strongest sentence in this file resting on nothing. Run:

```
$ LEAN_PATH=. leanchecker Persist
leanchecker found a problem in Persist
uncaught exception: while replaying declaration 'h2':
(kernel) declaration type mismatch, 'h2' has type
  Eq (S2.mk Bool.true) (S2.mk Bool.true)
but it is expected to have type
  Eq (S2.mk Bool.true) (S2.mk Bool.false)                          # exit 1

$ LEAN_PATH=. leanchecker ArenaTrustedMetadata
leanchecker found a problem in ArenaTrustedMetadata
uncaught exception: while replaying declaration 'bad2': …          # exit 1
```

**`leanchecker` catches it, and it catches the serialized form too.** That is the
answer to §5's open question and it is the good news: it *replays* each
declaration into a freshly derived environment rather than trusting the imported
`ConstantInfo`, so the falsified premise never reaches the second kernel. The
`.olean` that makes eta wrong for every downstream module does not survive one
`leanchecker` run.

So this route's row in the audit-blindness table is not the frightening one:

| | `#print axioms` | `leanchecker` | escapes to a consumer |
| --- | --- | --- | --- |
| here | **silent** | **rejects** | the `False` yes, the corruption only if not withdrawn |
| #14609, `ModuleSystem/` | **silent** | rejects | yes |
| #14613, `Universes/` | **silent** | *accepts*; `nanoda` rejects | yes |

It belongs with #14609, not with #14613 — which is the one where a released
official kernel and its official second checker agree on something false, and
remains the worse finding in this repository.

Note that `leanchecker` rejects the second file *whether or not the lie was
withdrawn*: withdrawal restores the environment for later Lean elaboration, but
the `.olean` still records `bad2 : disc2 NB.tt` proved by a term whose real type
is `True`. Withdrawal buys honest metadata for importers, not a checkable
artifact. Only §1–§3's controls make the kernel itself reject, and only within
this file. -/
