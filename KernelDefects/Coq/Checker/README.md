# The checker certified a proof of `False`

> **Warning.** This directory contains a machine-checked proof of `False` that
> **Rocq 9.2 — the current stable release — accepts**, with
> `Print Assumptions` reporting `Closed under the global context` and
> `rocqchk -bytecode-compiler yes` reporting `Modules were successfully checked`.
> Nothing in this repository builds against it, and the harness works in a
> scratch directory outside the tree.

[rocq#22352](https://github.com/rocq-prover/rocq/issues/22352), reported
2026-08-18 by Jason Gross and **open**. `rocqchk` typechecks each constant's
body, and then — with the non-default `-bytecode-compiler yes` — performs VM
conversions using bytecode read from the `.vo`'s separately serialised
`vmlibrary` segment, with **nothing tying that segment to the bodies it just
checked**. `checker/mod_checking.ml` checks `const_body`; `const_body_code` comes
from the file, via `Environ.link_vm_library`, and is used as-is.

This is the first **artifact** in this catalog whose defect is in a *checker*
rather than in a kernel, on either side. It is not the first such defect on
record here — [`../../../CATALOG.md`](../../../CATALOG.md) §4.6 already noted
[rocq#12439](https://github.com/rocq-prover/rocq/issues/12439), "coqchk
under-checks primitive declarations", as a gap — but that one has no reproducer
here and no demonstrated `False`. Full write-up, including why it is filed here
rather than under `EscapeHatches/`:
[`Reports/2026-08-18-rocqchk-vm-bytecode.md`](../../../Reports/2026-08-18-rocqchk-vm-bytecode.md).

## The construction

Two honest compilations of [`Defs.v`](Defs.v), differing only in whether
`poc_evil` is `idb true` or `idb false`, have byte-identical `opaques` and
`summary` segments. [`splice.py`](splice.py) writes a third object file taking
the **body** from the first and the **bytecode** from the second. No patched tool
is involved anywhere; `rocq compile`'s own output is fine, and the splice is the
attack.

[`Evil.v`](Evil.v) cashes the lie with a `<:` VMcast — `poc_evil`'s body is
`true`, its bytecode says `false` — and derives `boom : False`.
[`Downstream.v`](Downstream.v) is a plain `Require Import Evil` that uses it, and
exists to establish that the `False` escapes into a consumer whose own audit is
clean.

## What each channel says, on Rocq 9.2

| Channel | Verdict |
| --- | --- |
| `rocq c Evil.v` | **exit 0** |
| `Print Assumptions boom` | **`Closed under the global context`** |
| `rocqchk -bytecode-compiler yes Evil` | **`Modules were successfully checked`** |
| `rocqchk Evil` (default) | `Fatal Error: Type error: ActualType` |
| `rocqchk` on the spliced `Defs` alone, **both** modes | accepted — correctly; only its bytecode lies |
| `rocq c Downstream.v` | **exit 0**, both constants `Closed under the global context` |
| `rocqchk -bytecode-compiler yes Downstream` | **`Modules were successfully checked`** |
| **control** — `Evil.v` over an unspliced `Defs.vo` | **rejected** |

The last row is what makes the others mean anything. It fails at exactly the
VMcast, with

```
The term "myeq_refl bool false" has type "myeq bool false false"
while it is expected to have type "myeq bool poc_evil false".
```

so nothing in the construction is doing work except the spliced bytecode.

## Contents

| File | What it is |
| --- | --- |
| [`Defs.v`](Defs.v) | The honest source both halves of the splice are compiled from. Four lines, `-noinit`, its own `bool`. |
| [`splice.py`](splice.py) | The `.vo` container surgery, with the preconditions the exhibit depends on asserted rather than assumed. |
| [`Evil.v`](Evil.v) | The VMcast and `boom : False`. |
| [`Downstream.v`](Downstream.v) | A plain `Require`, to show the escape. |
| [`verify.ps1`](verify.ps1) | Twelve assertions, including the control. |

## Reproducing

```bash
pwsh KernelDefects/Coq/Checker/verify.ps1
```

Expected final line: `The rocqchk VM-bytecode artifact behaved as documented.`
Needs `rocq`, `rocqchk` and `python` on `PATH`. It is not part of
[`../verify.ps1`](../verify.ps1)'s one-file-per-`coqc` loop, because the defect
needs a hand-spliced object file and so the artifact is a build procedure rather
than a `.v` file.

The companion measurement — that `rocqchk` validates a different set of files
depending on the order of its `-norec` arguments
([rocq#22362](https://github.com/rocq-prover/rocq/issues/22362)), and that the
recorded segment digest is not compared in any mode — is
[`Audits/Coq/CheckerCoverage/`](../../../Audits/Coq/CheckerCoverage/).

## Verified on

* The Rocq Prover 9.2 (OCaml 4.14.2), `vo_version 90299` — the current stable
  release.

Upstream reports the defect present since 8.20 (`e6535d48bd`, which introduced
the dedicated `vmlibrary` segment) and demonstrates it on 9.4+alpha; 9.2 is not
named in the issue, and is pinned here.
