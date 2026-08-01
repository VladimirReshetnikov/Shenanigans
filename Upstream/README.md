# Upstream: the sources this catalog cites, pinned

Three submodules. They are **reference material, not dependencies** — nothing in
`Paradoxes/`, `EscapeHatches/`, `KernelDefects/` or `Audits/` imports them, no
`verify.ps1` builds them, and every exhibit still resolves its own toolchain
through `elan`. Delete this directory and every claim in the repository still
verifies exactly as before.

They exist because of ground rule 4 in [`../README.md`](../README.md) — *state
the toolchain* — applied one level up. [`../CATALOG.md`](../CATALOG.md) makes
claims about specific lines of C++ (`to_proj_idx`, `equiv_manager::is_equiv_core`,
`add_quot`), about which names are in comparator's `primitiveTargets`, and about
what `nanoda` did and did not check in July 2026. A claim like that is only worth
as much as the reader's ability to check it, and checking it means having the
source at a known commit rather than at whatever `master` happens to be.

## Contents

| Path | Upstream | Pinned commit | Date | Why this commit |
| --- | --- | --- | --- | --- |
| [`lean4/`](lean4/) | [`leanprover/lean4`](https://github.com/leanprover/lean4) | `5fa71c9141` | 2026-08-01 | `master` after #14633, the newest PR §2.5 cites. Contains every fix in the July–August wave — #14615, #14621, #14631, #14632, #14633 — and *not* #14582, which is still open. |
| [`comparator/`](comparator/) | [`leanprover/comparator`](https://github.com/leanprover/comparator) | `5149123` | 2026-07-31 | `master` after `8c0e44e`, which moved `Char.ofNat`/`List`/`eagerReduce` into `primitiveTargets`. |
| [`nanoda_lib/`](nanoda_lib/) | [`ammkrn/nanoda_lib`](https://github.com/ammkrn/nanoda_lib) | `ddfac2b` | 2026-07-27 | The merge of PR #22, the projection-node fix that is half of CATALOG §3.0 — and the exact revision the [Kernel Arena](https://arena.lean-lang.org/) currently runs. |

There is no "lean4 kernel" repository: the kernel is
[`lean4/src/kernel/`](lean4/src/kernel/) — 17 `.cpp` files and 21 headers inside
the main tree — so the submodule is necessarily the whole thing. (Note this is not
the same count as CATALOG §5's "59 of 61 sources", which is about compiling the
kernel standalone and includes its `runtime/` and `util/` dependencies.)

## The pinned commit is a default, not the answer

Almost every result in this repository is pinned to a *different* revision than
the ones above, because results were measured against releases and the pins above
track the source being cited. The mapping:

| Recorded result | Measured against | Get there with |
| --- | --- | --- |
| `KernelDefects/Lean/` exhibits, `Audits/` sweeps | Lean `v4.32.0` (the `lean-toolchain` pin) | `git -C lean4 checkout v4.32.0` |
| `Reports/2026-07-29-lean-4.33-backport-gap.md` | `v4.32.0`, `v4.32.1`, `v4.32.2`, `v4.33.0-rc1` | `git -C lean4 checkout v4.33.0-rc1` |
| `Reports/2026-07-29-defeq-history-dependence.md` | `v4.32.0` and `v4.32.2` | `git -C lean4 checkout v4.32.2` |
| `KernelDefects/Lean/Comparator/README.md` verdict table | comparator `68a0641` + Lean `v4.33.0-rc1` | `git -C comparator checkout 68a0641` |
| CATALOG §3.0's "week-old `nanoda`" | the state *before* PR #22, i.e. `f58f2f6` or earlier | `git -C nanoda_lib checkout f58f2f6` |

The `lean4` submodule is a **blobless** clone (`--filter=blob:none`), so every one
of those checkouts works — the full history graph is local and file contents are
fetched on demand. A `--depth 1` clone would have been smaller and would have
broken all of it.

## Cloning

The two small ones are ordinary:

```bash
git submodule update --init Upstream/comparator Upstream/nanoda_lib
```

`lean4` is 6.2 GB packed upstream, and a plain `git submodule update --init` will
fetch all of it. Pre-clone it blobless instead — this is what was done here, and
it lands at **844 MB** (179 MB of history, the rest working tree):

```bash
git clone --filter=blob:none https://github.com/leanprover/lean4.git Upstream/lean4
```

```bash
git submodule update --init Upstream/lean4
```

The second command finds the existing clone and checks out the pinned commit. If
you do not need the Lean source at all, simply never init that submodule; nothing
in this repository will notice.

## What has already been checked against these pins

Recorded so the same verification is not repeated blindly. All at `lean4@5fa71c9`:

* `to_proj_idx` exists in `src/kernel/type_checker.cpp:229` with the
  `> std::numeric_limits<unsigned>::max()` bound, and both `infer_proj` and
  `reduce_proj` route through it — CATALOG §2.1/§2.5's claim that #14632 fixes
  #12746.
* `src/kernel/equiv_manager.cpp:103` compares `proj_sname(a) == proj_sname(b)`
  before the index and the projected expression — #14631.
* `check_uniform_params` appears **nowhere** in the tree, which is the independent
  confirmation that #14582 is still unmerged.

And one check of the pinning itself: `git -C lean4 checkout v4.32.2` succeeds from
the blobless clone and finds **zero** occurrences of `to_proj_idx`, which both
confirms that historical checkouts really do work under `--filter=blob:none` and
independently dates the #12746 fix to after `v4.32.2`.
