(** * Variance inference never looks inside a let-in in a constructor type

    rocq-prover/rocq#22383, "Incorrect variance analysis with letin in
    constructor type", filed 2026-08-20 by `SkySkimmer` and **OPEN**, with an
    unmerged fix PR.  This is the **first artifact in §4.3** of
    [`../../../CATALOG.md`](../../../CATALOG.md), which until now recorded every
    universe/variance defect as a gap.

    ** Mechanism

    *The two function names below are quoted from upstream's issue text and are
    **inspection, not measurement** — the Rocq source was not read for this
    file.  Everything stated with a verdict, an exit code or a printed message
    was run.  What is measured, and what makes the naming credible, is §1 of the
    controls file: the same inductive's non-let universe is inferred `+` and its
    let-bound universe `*`, which is exactly the behaviour a zeta-reducing walk
    would produce.*

    `inferCumulativity` decides, for each universe of a cumulative polymorphic
    inductive, whether the universe is *irrelevant* (`*`), covariant (`+`) or
    invariant (`=`).  It walks each constructor type with `whd_decompose_prod`,
    and `whd` **zeta-reduces**: `let ghost := Type@{u} in token@{u v}` weak-head
    normalises to `token@{u v}`, and the binder — with `Type@{v}` in its type
    annotation and `Type@{u}` in its body — is gone before anything is visited.
    Both universes come out `*`.  `match` does not agree: iota-reduction
    reinstates the let-binder from the *scrutinee's own* instance, so the
    pattern variable `ghost` hands back `Type@{u}` after conversion has already
    ruled that `u` may be changed at will.

    Upstream states the diagnosis in one line: *"`u` is irrelevant in `token`
    but match can get it out through the letin.  I guess infercumul should
    preserve letins instead of doing whd_decompose_prod, and treat letins as
    CONV positions?"*

    So `token@{u v}` is cast to `token@{Set u}` for free, and reading the ghost
    back out yields a term of type `Type@{u}` whose value is `Type@{u}`.  That
    is type-in-type at a single universe, and `Hurkens.TypeNeqSmallType` turns
    it into `False`.

    ** Which category

    Category **(a)** of [`../../../README.md`](../../../README.md): a closed
    proof of `False` that the kernel accepts with the audit reporting nothing.
    It is **not** an escape hatch under ground rule 2 — see the next section —
    and it is **not** conditional on definitional UIP or univalence, so it does
    not belong in [`../../../Paradoxes/`](../../../Paradoxes/) under ground
    rule 1.  Nothing here is assumed; `Hurkens` is Stdlib and is axiom-free.

    ** No flag, and no variance annotation.  This is stronger than upstream's

    Upstream's reproducer opens with `Set Universe Polymorphism` — a global
    option — and declares the variance by hand as `token@{*u v | u < v}`, which
    *asserts* the irrelevance the kernel then merely rechecks.  *That sentence
    describes #22383's issue body and is therefore **inspection, not
    measurement**: it was read, not run.  Everything after the colon was run.*
    Both spellings were measured here and neither is load-bearing:

      - the option is replaced by the per-declaration modifiers `Polymorphic`
        and `Cumulative`, which are declaration syntax, not flags;
      - the `*` annotation is **deleted**, and inference supplies `*u *v` on its
        own.  [`LetinVarianceInferenceControls.v`](LetinVarianceInferenceControls.v)
        §1 prints it.

    **This file contains no `Set` and no `Unset`, and no non-default flag is
    passed to `coqc`.**  Ground rule 2 therefore does not bite: the `False` is
    the finding, not the audit's silence — though the silence is total as well.
    Grep the file if you like; that is the point of saying it.

    ** Measured on Rocq 9.2 (current stable) and on Rocq Platform 9.0.1

    Identical on both.  No option is passed to `coqc` other than the
    `-coqlib` path the 9.0.1 binary needs to find its own library, which
    selects an installation and changes no behaviour:

      - `coqc` on this file:                 **exit 0**.
      - `Print Assumptions contradiction`:   `Closed under the global context`.
      - `Print Assumptions one_eq_two`:      `Closed under the global context`.
      - `rocqchk` on the `.vo`:              `Modules were successfully checked`,
                                             **exit 0**.
      - `rocqchk -bytecode-compiler yes`:    **exit 0**.
      - `rocqchk -o` context summary:        `* Axioms: <none>`,
                                             `* ... type-in-type: <none>`,
                                             `* ... unsafe (co)fixpoints: <none>`.

    **Every channel this repository uses to price a proof of `False` reports
    nothing**, and the independent checker certifies the library.  The `False`
    also reaches a consumer:
    [`LetinVarianceInferenceEscape.v`](LetinVarianceInferenceEscape.v) only
    `Require`s this file, is accepted, and is clean in both channels too.
    That combination — both audits silent *and* the `False` propagates — was
    previously unique to rocq#21839 in this repository; it is now shared.

    ** The control is one token

    [`LetinVarianceInferenceControls.v`](LetinVarianceInferenceControls.v) runs
    the same construction with `@{u v}` changed to `@{=u v}` — one character —
    and the cast is refused:

        The term "make_tokenA" has type "let ghost := Type in tokenA"
        while it is expected to have type "tokenA"
        (universe inconsistency: Cannot enforce Set = u).

    The kernel owns the machinery to stop this; inference just never reaches
    into the binder to ask for it.  Three further controls and an annex are in
    that file.

    ** Provenance, and a correction the write-up should carry

    [`../../../Reports/2026-08-20-rocq-august-wave.md`](../../../Reports/2026-08-20-rocq-august-wave.md)
    records the OpenAI attribution as Carlo Angiuli's inference and says the
    catalog *"should say so until someone upstream states it"*.  Someone
    upstream states it.  The last two lines of #22383's body, verbatim:

        Reported by OpenAI by email to a random core team member (not me).
        For anyone reading this, please directly open issues instead of
        emailing random people.

    rocq#22386's body names the finders differently again — "Found by an LLM and
    @dselsam" — so the two halves of Angiuli's guess are attested in two
    different issues of the same wave.  The report's "unconfirmed" is now
    resolved for this issue at least, and the maintainer-filed pattern it
    documented is explained rather than contradicted: `SkySkimmer` filed it on
    an outside reporter's behalf.

    Write-up: ../../../Reports/2026-08-20-rocq-august-wave.md *)

From Stdlib Require Import Hurkens.

(** ** The inductive.

    One constructor, no arguments after zeta-reduction — which is why an
    inductive that mentions `Type@{v}` is allowed to live in `Set` at all.  The
    variance annotation is *absent*: `Polymorphic Cumulative` asks the kernel to
    infer, and it infers `*u *v`. *)

Polymorphic Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

(** `make_token : let ghost := Type in token` — the binder that inference
    zeta-reduces away and that `match` reinstates. *)
Print token.

Polymorphic Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

(** ** The cast.

    `make_token@{u v} : token@{u v}` is handed to `read_token@{Set u}`, which
    wants a `token@{Set u}`.  Cumulativity permits it because `u` is `*`.  The
    result is declared `Type@{u}`; iota then makes its *value* `Type@{u}` too. *)

Polymorphic Definition small@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (make_token@{u v}).

(** The equation the kernel refuses when it is stated plainly — see the
    controls file, §4 — and accepts here by conversion. *)
Polymorphic Definition small_is_universe@{u v | Set < u, u < v} :
  @eq Type@{v} small@{u v} Type@{u} := eq_refl.

Definition contradiction : False :=
  TypeNeqSmallType.paradox small (eq_sym small_is_universe).

(** Expected on 9.2 and on 9.0.1: `Closed under the global context`. *)
Print Assumptions contradiction.

(** Everything follows, still with a clean audit. *)
Definition one_eq_two : 1 = 2 := match contradiction with end.
Print Assumptions one_eq_two.
