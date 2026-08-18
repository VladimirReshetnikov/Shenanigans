# `rocqchk` says "Modules were successfully checked" over a proof of `False`

**Status: an audit defect, live on the current stable release, measured here on
Rocq 9.2.** Not a kernel bug: the kernel's conversion is right, and the default
`rocqchk` catches this. What fails is the checker in one of its two supported
modes — the mode that exists to make checking fast.

| Issue | Substance | State |
| --- | --- | --- |
| [rocq#22352](https://github.com/rocq-prover/rocq/issues/22352) | `rocqchk -bytecode-compiler yes` typechecks each constant's body and then performs VM conversions with bytecode read from the `.vo`'s separately serialised `vmlibrary` segment, with nothing tying the two together. | **OPEN** |
| [rocq#22353](https://github.com/rocq-prover/rocq/issues/22353) | The fix: stop reading that segment; compile the bytecode from the bodies just typechecked. | open PR |
| [rocq#22360](https://github.com/rocq-prover/rocq/issues/22360) | The same mode *rejects* any `.vo` using primitive strings — `vm_caml_prim` has 12 constructors, the validator accepts 6. | **OPEN** |
| [rocq#22362](https://github.com/rocq-prover/rocq/issues/22362) | Which libraries `rocqchk` validates depends on the **order of the `-norec` arguments**. A library named on the command line can be read with no validation at all. | **OPEN** |
| [rocq#22363](https://github.com/rocq-prover/rocq/issues/22363) | The fix for the above. | open PR |

All five were filed on 2026-08-18 by Jason Gross. Upstream reports them against
`master` (9.4+alpha) and the 9.3 development switch. **This report pins them to
9.2, the current stable release**, which upstream's issues do not state.

Artifacts:

* [`KernelDefects/Coq/Checker/`](../KernelDefects/Coq/Checker/) — the `False`,
  its downstream escape, and the control. `pwsh KernelDefects/Coq/Checker/verify.ps1`
* [`Audits/Coq/CheckerCoverage/`](../Audits/Coq/CheckerCoverage/) — the order
  dependence, and one negative result. `pwsh Audits/Coq/CheckerCoverage/verify.ps1`

The second is the first entry in this repository's `Audits/` **Rocq** column,
which [`Audits/README.md`](../Audits/README.md) had flagged as a genuine gap.

## What was measured, on Rocq 9.2 (vo_version 90299)

Two honest compilations of a four-line file differing only in one constant's
*value* have byte-identical `opaques` and `summary` segments. Splice the first's
`library` (body: `poc_evil = true`) onto the second's `vmlibrary` (bytecode:
`poc_evil = false`) and the result is a well-formed object file that lies about
what its constant computes. No patched tool is involved; the splice is 60 lines
of Python over the container layout in `lib/objFile.ml`.

A `<:` VMcast then cashes the lie, and `true = false` follows:

| Channel | Verdict |
| --- | --- |
| `rocq c Evil.v` | **exit 0** |
| `Print Assumptions boom` | **`Closed under the global context`** |
| `rocqchk -bytecode-compiler yes Evil` | **`Modules were successfully checked`**, exit 0 |
| `rocqchk Evil` (default) | `Fatal Error: Type error: ActualType`, exit 129 |
| `rocqchk` on the spliced `Defs` **alone**, either mode | accepted — correctly |
| `Downstream.v`, a plain `Require Import Evil` | **exit 0**, both its constants `Closed under the global context` |
| `rocqchk -bytecode-compiler yes Downstream` | **`Modules were successfully checked`** |
| **Control**: the same `Evil.v` over an *unspliced* `Defs.vo` | rejected — `while it is expected to have type` |

Three of those rows are worth separating out.

**The tampered file is not the file that fails.** `rocqchk` accepts the spliced
`Defs.vo` on its own in *both* modes, and it is right to: its declarations are
well typed, and only its bytecode segment lies. The unsoundness appears one
library downstream, in the file whose VMcast only typechecked because
`rocq compile` believed the bogus bytecode. Anyone checking the artefact they
were handed, rather than the whole closure, learns nothing.

**The `False` escapes through a plain `Require`.** `Downstream.v` contains no
VMcast, no flag, and no reference to the spliced file. Its own
`Print Assumptions` is clean for both of its constants, and
`rocqchk -bytecode-compiler yes` certifies it. That is the property
[`CATALOG.md`](../CATALOG.md) §4.1 uses to rank rocq#21839 as the strongest route
in the catalog.

**The control is the load-bearing part.** Over an honest `Defs.vo`, the same
`Evil.v` is rejected at exactly the VMcast:

```
The term "myeq_refl bool false" has type "myeq bool false false"
while it is expected to have type "myeq bool poc_evil false".
```

so the `False` exists only because the spliced bytecode lied, and nothing else in
the construction is doing work.

## Which category this is, and why the answer is not obvious

The repository's first ground rule is that a route is classified by *what the
audit reports*, not by how clever it is — and its second is that a `False`
needing a flag is an escape hatch even if the flag is obscure. Two things here
pull in opposite directions.

Toward **escape hatch**: the input is a hand-edited object file. §1.2 already has
a row for that — *"tampered or stale `.vo` / `.olean` → nothing; neither system
re-typechecks on import"* — and of course you can prove anything from a file you
are allowed to rewrite.

Toward **kernel defect**: the `False` itself needs no flag. `rocq c` accepts it
with defaults and `Print Assumptions` reports nothing. The flag is on the
*checker*, and it decides only whether the audit notices.

The tie-breaker is what §1.2's row actually claims, and it is now wrong in the
part that matters. That row carries the note that *Rocq hardened its `coqchk`
path in 8.19* — i.e. the catalog's position is that `coqchk` **is** the answer to
a tampered `.vo`. This exhibit is a tampered `.vo` that `coqchk` re-typechecks,
in a supported mode, and certifies. So the finding is not "you can tamper with a
`.vo`", which was known; it is that the tool whose entire purpose is to catch
that reports success on this one. It belongs in `KernelDefects/`, in a new
`Checker/` subdirectory, because the defect is in a checker rather than in the
kernel — the first *artifact* of that kind on either side of this catalog.
(Not the first such defect on record: §4.6 already noted
[rocq#12439](https://github.com/rocq-prover/rocq/issues/12439), "coqchk
under-checks primitive declarations", as a gap with no reproducer and no
demonstrated `False`.)

## Where it sits against rocq#21839

[`GuardChecker/WrongEnvReduction.v`](../KernelDefects/Coq/GuardChecker/WrongEnvReduction.v)
remains the strongest exhibit in the catalog, and this one does not displace it.
The ranking, on the repository's own scale:

| | #21839 | #22352 |
| --- | --- | --- |
| closed `False`, no flag on the source | yes | yes |
| `Print Assumptions` clean | yes | yes |
| escapes a plain `Require`, downstream audit clean | yes | yes |
| **`coqchk` misses it** | **yes, in every mode** | only with `-bytecode-compiler yes` |
| needs a hand-edited artefact | no | **yes** |

#21839 wins on both of the last two rows, and they are the two that matter most.
What #22352 adds that #21839 does not have is the *disagreement between two modes
of the same tool*: run `rocqchk` one way and it certifies a proof of `False`; run
it the other way, over the same bytes, and it rejects. No other exhibit in this
repository has that shape.

## The order dependence, and one negative result

[`Audits/Coq/CheckerCoverage/`](../Audits/Coq/CheckerCoverage/) measures two
further things about the same tool, neither of which is a `False`.

**Argument order changes what gets validated** (rocq#22362), and it reproduces on
9.2 unchanged. Two invocations differing only in the order of two `-norec`
arguments:

```
rocqchk -bytecode-compiler yes … -norec A -norec Corelib.Strings.PrimString   → exit 129
rocqchk -bytecode-compiler yes … -norec Corelib.Strings.PrimString -norec A   → exit 0
```

The mechanism, from `checker/checkLibrary.ml`: a `-norec` root interned first
pulls its dependencies in as `Dep`, and `Dep` mode reads them through
`System.marshal_in` with no `Validate.validate` at all; a later explicit `-norec`
for such a dependency finds it already in `needed` and is a no-op. The roots are
interned with `List.fold_right`, so the *last* argument is interned *first*.
The sting is in the accepting run's own output: `PrimString` still appears in the
`Checking library:` list, so nothing distinguishes "validated" from "read raw" in
what the user sees. (The failure in the first order is a separate bug, #22360 —
the `vm_caml_prim` validator accepts 6 constructors where the type has 12 — but
that bug is only the *observable*; the order dependence is what is being
measured.)

**Negative result: the recorded segment digest is not compared, in any mode.**
A `.vo` whose per-segment MD5 does not match its payload is accepted by `rocqchk`
in both `-norec` orders *and* in full-closure mode, and `rocq c` happily
`Require`s it. This is **not** unsoundness — the payload spliced in for the test
is another honest compilation, so what the checker typechecks is well typed and
it correctly says so. It is recorded because it locates the line precisely: the
digest is an accident detector, not a defence, and the only thing standing
between a hand-edited `.vo` and a bogus theorem is that `rocqchk` re-typechecks
the bodies. Which is exactly what #22352 gets around, by lying in the one segment
the re-typechecking does not derive its answers from.

## What this does not change

Nothing here is a new *kernel* defect, and the structural claim in
[`KernelDefects/README.md`](../KernelDefects/README.md) — that Rocq's soundness
risk clusters in the guard checker and the module system, neither of which Lean
has — stands. What is new is a third cluster, in the *checker*, and it is worth
noting that its Lean analogue is empty for a structural reason rather than a
lucky one: `leanchecker` shares Lean's kernel and replays declarations, and the
only compiled-code hook the Lean kernel has is `Lean.reduceBool`, which
`leanchecker` cannot replay at all — measured in
[`KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean`](../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean),
where that inability is what makes `leanchecker` *reject* an exhibit the kernel
accepts. Rocq's checker is a second implementation carrying a second copy of a
serialised artefact; Lean's is the same kernel run again. The failure mode here
needs the first arrangement.

## Reproduction notes

* Both harnesses need `rocq`, `rocqchk` and `python` on `PATH`, and build in a
  scratch directory outside the repository.
* `-bytecode-compiler yes` is **not** the default for `rocqchk`. A CI script that
  runs plain `rocqchk` is not exposed to #22352.
* Judge by exit code and by the asserted substring. `rocqchk` prints
  `Checking library: X` for a library it read without validating, so the log is
  not evidence of validation.
* Upstream places #22352 as present since 8.20 (`e6535d48bd`, which introduced
  the dedicated `vmlibrary` segment). Only 9.2 was measured here.
