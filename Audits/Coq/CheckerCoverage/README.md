# What has a green `rocqchk` actually established?

Category (see [`../../../README.md`](../../../README.md)): **audit**. No proof of
`False` is produced here. This is the first entry in this repository's Rocq
column of [`Audits/`](../../), which [`Audits/README.md`](../../README.md) had
recorded as a genuine gap.

[`CATALOG.md`](../../../CATALOG.md) §4.7 exists because *"a CI script that only
checks the exit code proves less than it appears to."* This directory asks how
much less, on the installed toolchain, and gets three answers.

```bash
pwsh Audits/Coq/CheckerCoverage/verify.ps1
```

Expected final line: `All checker-coverage measurements behaved as documented.`
Needs `rocq`, `rocqchk` and `python` on `PATH`.

## 1. Which files get validated depends on the order you name them

[rocq#22362](https://github.com/rocq-prover/rocq/issues/22362), reported
2026-08-18 and **open**. Two invocations differing **only** in the order of two
`-norec` arguments, over the same files:

```
rocqchk -bytecode-compiler yes … -norec A -norec Corelib.Strings.PrimString   → exit 129
rocqchk -bytecode-compiler yes … -norec Corelib.Strings.PrimString -norec A   → exit 0
```

From `checker/checkLibrary.ml`: a `-norec` root interned first pulls its
dependencies in as `Dep`, and `Dep` mode reads them through `System.marshal_in`
with no `Validate.validate` at all; a later explicit `-norec` for such a
dependency finds it already in `needed` and does nothing. The roots are interned
with `List.fold_right`, so the **last** argument on the command line is interned
**first**.

The part worth keeping is what the accepting run prints: `Corelib.Strings.PrimString`
still appears in its `Checking library:` list. Nothing in the output
distinguishes "validated" from "read raw", so the log is not evidence of
validation, and neither is the exit code.

(The failure in the first order is a *separate* bug,
[rocq#22360](https://github.com/rocq-prover/rocq/issues/22360) — `vm_caml_prim`
has 12 constructors and the validator accepts 6 — which is only the *observable*
here. Once [#22361](https://github.com/rocq-prover/rocq/issues/22361) lands, this
particular pair of commands stops differing; the order dependence does not.)

Reproduces on Rocq 9.2 exactly as upstream reports it on 9.4+alpha and the 9.3
development switch.

## 2. Negative result: the recorded segment digest is not compared, in any mode

A `.vo` whose per-segment MD5 does not match its contents is accepted by `rocqchk`
in **both** `-norec` orders and in full-closure mode, and `rocq c` `Require`s it
without complaint.

**This is not unsoundness**, and the harness says so in as many words. The
contents spliced in for the measurement is another *honest* compilation, so what
the checker typechecks is well typed and it is right to accept it. The digest is
an accident detector, not a safeguard.

It is recorded because it locates the line precisely, and the line is not where a
reader might assume. Nothing about a hand-edited `.vo` is caught by its checksum.
The only thing standing between one and a bogus theorem is that `rocqchk`
re-typechecks the bodies.

## 3. …which is exactly what rocq#22352 gets around

By lying in the one segment the re-typechecking does not derive its answers from.
That one **is** a proof of `False` — closed, `Print Assumptions` clean,
`rocqchk -bytecode-compiler yes` reporting `Modules were successfully checked` —
and it lives in [`KernelDefects/Coq/Checker/`](../../../KernelDefects/Coq/Checker/).
The harness here asserts that exhibit is present rather than repeating it, so the
three measurements read as one argument.

## Verified on

* The Rocq Prover 9.2 (OCaml 4.14.2) — the current stable release.
