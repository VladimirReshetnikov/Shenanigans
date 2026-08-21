(** * Module subtyping zeta-reduces a constructor type; `match` does not

    rocq-prover/rocq#22387, "Incorrect module subtyping with letins in
    constructor types", filed 2026-08-20 by `SkySkimmer` and **OPEN**, with an
    unmerged fix PR.  Same day, same trigger — a `let` in a constructor type —
    as rocq#22378 and rocq#22383, and a different subsystem again: this one is
    module subtyping.

    ** Mechanism

    *The description of what module subtyping compares is upstream's, quoted
    below, and is **inspection, not measurement** — the Rocq source was not read
    for this file.  What is measured is its consequences, and controls §3 pins
    the diagnosis independently: the generated `T_rect`, which is a term
    containing a `match` and therefore compares branch *contexts*, does reject
    the pair that the constructor **type** comparison accepts.*

    A constructor's type is a telescope of declarations, some of them
    let-bindings.  Two of them:

        S.c : forall x : nat, let z := 0 in T
        A.c : let z := 0 in forall x : nat, T

    Subtyping compares the **whole constructor type** up to conversion, and
    conversion zeta-reduces: both sides become `nat -> T`, so `A <: S` is
    accepted.  `match` does not work on the whole type — it works on the
    *declaration list*, and the branch is a term in a context of two
    declarations.  Written against `S` the branch's `z` is the second
    declaration; read against `A` the second declaration is `x`.  The functor
    body is substituted, not re-elaborated, so `X.c 1`'s "always 0" silently
    becomes "the 1 the caller passed", and

        match 1 with O => True | S _ => False end

    is `False` — held by a proof term that was checked when it meant `True`.

    Upstream states it in one line: *"subtyping compares the whole constructor
    type (`forall x:nat, let z := 0 in T` vs `let z := 0 in forall x:nat, T`)
    but `match` cares about the order between letin and real argument."*

    ** Which category

    Category **(a)** of [`../../../README.md`](../../../README.md): a closed
    proof of `False` the kernel accepts.  Not conditional on definitional UIP or
    univalence, so ground rule 1 keeps it out of
    [`../../../Paradoxes/`](../../../Paradoxes/); nothing is assumed anywhere in
    the file.  See the audit table below for the one channel that prints a line,
    and [`LetinOrderSubtypingControls.v`](LetinOrderSubtypingControls.v) §5 for
    the control proving that line carries no information.

    ** No flag.  Upstream's reproducer needs one and this one does not

    Upstream opens with `Unset Elimination Schemes`.  *That clause describes
    #22387's issue body and is **inspection, not measurement** — it was read,
    not run; the rest of this section was run.*  It is load-bearing for that
    spelling: with schemes generated, `Module Applied : R := F A` is
    **rejected**, and what rejects it is not the inductive but the derived
    `T_rect`, whose *body* differs in the pattern order —

        Signature components for field T_rect do not match:
        the body of definitions differs: expected
        "... | A3.c x _ => c x ..."     (* the branch elaborated against S3 *)
        but found
        "... | A3.c _ x => c x ..."     (* the branch as A3 declares it *)

    — measured.  That is an **abridgement**, and the ellipses mark it: the
    module names are the controls file's `S3` and `A3`, and the full literal
    text of both halves — with the shorter form 9.0.1 prints — is quoted
    there, §3.

    So the elimination scheme is the only component of the signature that
    notices, and switching schemes off is what makes the construction
    reachable.  Ground rule 2 would
    then class the `False` as an escape hatch.

    **It is not one.**  `Variant` generates elimination schemes only when
    `Nonrecursive Elimination Schemes` is set, and that flag is **off by
    default**.  Replacing `Inductive` with `Variant` — one word, no option —
    gives a module type whose signature contains nothing but `T` and `c`:

        Module Type S = Sig Variant T : Set :=  c : nat -> let z := 0 in T. End

    and the construction goes through.  **This file contains no `Set` and no
    `Unset`, and no non-default flag is passed to `coqc`** — the only option
    used anywhere in this measurement is the `-coqlib` path the 9.0.1 binary
    needs to find its own library, which selects an installation and changes no
    behaviour.  That spelling is this repository's contribution; upstream's
    issue does not have it.

    ** Does declaration order matter?  Sufficient, but not necessary

    The catalog asks whether the finding is "declaration order is significant to
    `match` and invisible to whole-arity conversion".  Measured, in the controls
    file §4: **order is one sufficient trigger and it is not the only one.**
    Keep the order identical in `S` and `A` and change only the let's *body* —
    `z := 0` against `z := 1` — and the same closed `False` appears, with the
    same clean `Print Assumptions`.  Zeta erases the binder's position *and* its
    value before the comparison begins, so both are invisible.  The accurate
    statement is that everything about a let-in in a constructor type is erased
    by whole-arity conversion, while `match` depends on all of it.

    ** Measured on Rocq 9.2 (current stable) and on Rocq Platform 9.0.1

    Identical on both:

      - `coqc` on this file:                **exit 0**.
      - `Print Assumptions contradiction`:  `Closed under the global context`.
      - `Print Assumptions one_eq_two`:     `Closed under the global context`.
      - `rocqchk` on the `.vo`:             `Modules were successfully checked`,
                                            **exit 0**.
      - `rocqchk -bytecode-compiler yes`:   **exit 0**.
      - `rocqchk -o` context summary:       `* ... type-in-type: <none>`,
                                            `* ... unsafe (co)fixpoints: <none>`,
                                            and
                                            `* Axioms: <this file>.Applied.result`.

    That last line is the only mark this construction leaves anywhere, and
    **it is not a catch**: controls §5 runs an *honest* sealed functor
    application and gets the identical line, with `True` in place of `False`.
    `Module M : Sig := F A` makes every component of `M` body-less in the `.vo`,
    so `rocqchk` lists them as axioms whatever they are.  `Print Assumptions`,
    looking at the same constant, says `Closed under the global context`.  The
    two audits disagree about `Applied.result`, and neither disagreement is
    about soundness.

    ** And the sealing is what silences the checker

    [`LetinOrderSubtypingUnsealed.v`](LetinOrderSubtypingUnsealed.v) is this
    construction with the ascription deleted — `Module Applied := F A.`, the
    `False` obtained by conversion instead.  `coqc` still gives exit 0 and two
    clean `Print Assumptions` lines, and **`rocqchk` refuses it**:

        checking cst:...Applied.result
        Fatal Error: Type error: ActualType

    So `rocqchk` does re-typecheck a functor application's substituted body, and
    the substituted body here is ill-typed — the checker would have caught this
    construction outright.  What stops it is the ascription in the line below,
    which removes the body from the `.vo`.  That pairing is not in upstream's
    report either.

    ** Provenance

    #22387's body ends exactly as #22383's does — see
    [`../Universes/LetinVarianceInference.v`](../Universes/LetinVarianceInference.v)
    for the same note in full:

        Reported by OpenAI by email to a random core team member (not me).
        For anyone reading this, please directly open issues instead of
        emailing random people.

    So `SkySkimmer` filed on an outside reporter's behalf, which is what the
    2026-08-20 wave report inferred from the filing pattern and could not yet
    confirm.

    Write-up: ../../../Reports/2026-08-20-rocq-august-wave.md *)

(** ** The two modules.

    `S` is the signature the functor is written against: the real argument
    first, the let second.  `A` is the argument it is applied to: the same two
    declarations, swapped.  `Variant`, not `Inductive`, so no elimination scheme
    joins the signature — and no flag is needed to arrange that. *)

Module Type S.
  Variant T := c (x : nat) (z : nat := 0).
End S.

(** `Module Type S = Sig Variant T : Set :=  c : nat -> let z := 0 in T. End`
    — two components, `T` and `c`, and nothing else. *)
Print Module Type S.

Module A.
  Variant T := c (z : nat := 0) (x : nat).
End A.

(** ** The functor.

    Elaborated against `S`, where the branch's `z` is the let and is therefore
    `0`, so the scrutinee of the outer `match` is `0`, so `result : True` and
    `I` proves it.  Nothing here is unusual and nothing here is wrong. *)

Module F (X : S).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F.

(** ** The application.

    `A <: S` is checked by comparing constructor types up to conversion, which
    zeta-reduces both to `nat -> T`; accepted.  `F`'s body is then substituted
    and not re-checked, and in `A`'s declaration order the branch returns the
    `1` that was passed, so `result`'s type has become `False`.  The ascription
    to `R` is what states that out loud — and, per the header, what removes the
    body from the `.vo`. *)

Module Type R. Parameter result : False. End R.

Module Applied : R := F A.

Definition contradiction : False := Applied.result.

(** Expected on 9.2 and on 9.0.1: `Closed under the global context`. *)
Print Assumptions contradiction.

(** Everything follows, still with a clean audit. *)
Definition one_eq_two : 1 = 2 := match contradiction with end.
Print Assumptions one_eq_two.
