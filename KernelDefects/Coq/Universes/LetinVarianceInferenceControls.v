(** * Controls for LetinVarianceInference.v — the kernel refuses this everywhere else

    rocq#22383.  Acceptance of the exhibit means nothing unless the same
    procedure, on the same toolchain, **rejects** the neighbouring
    arrangements.  It rejects four of them, and the sharpest is one character.

    Ground rule 6.  Every message below was measured on Rocq 9.2 and again on
    Rocq Platform 9.0.1 (`coqc -coqlib C:\Rocq-Platform~9.0~2025.08\lib\coq`)
    and is **character-identical on the two** — with one measured exception,
    §5, marked again where it occurs.  The universe §5's message names is
    anonymous and file-local, so its printed index carries the file's name and
    is **not** stable across the two toolchains: with one and the same source
    file the message reads `Cannot enforce <file>.93+1 <= Set.` on 9.2 and
    `Cannot enforce <file>.97+1 <= Set.` on 9.0.1.  That is why §5 alone is
    quoted with the index redacted; the other five are quoted literally, and a
    reader who deletes a `Fail` gets exactly the text printed here.

    `coqc` does not print the text of a `Fail`, so each message here was
    captured by deleting the `Fail` and reading the resulting `Error:`;
    `rocq top` prints the same text with `The command has indeed failed with
    message:` in front of it.

    ** A note on the one `Set` in this file

    §1 turns on `Printing Universes`, because variance is not displayed
    otherwise, and turns it off again immediately.  It is a **printing** option:
    it changes what `Print` shows and nothing about what the kernel accepts.
    The exhibit itself contains no `Set` and no `Unset` at all, which is the
    claim ground rule 2 cares about, and the messages quoted below were measured
    with printing left at its default so that a reader who deletes a `Fail` gets
    exactly the text quoted.

    ** Summary of what is measured here

      §1  inference, unprompted, says `*u *v` — and says `+w` for the *same*
          inductive's non-let argument.  The let is the whole difference.
      §2  one character, `u` -> `=u`: refused.
      §3  one word, `Cumulative` deleted: refused, same message.
      §4  the equation stated plainly: refused.
      §5  the let deleted: the inductive no longer fits in `Set`.
      §6  annex — the five reduction machines split three-two on the exhibit's
          `small`, which is a second, independent symptom of the same defect. *)

From Stdlib Require Import Hurkens.

(** ** §1 — What inference says, with nothing asserted by hand

    One inductive, three universes, two constructor arguments.  `visible` is an
    ordinary argument; `hidden` is let-bound.  `u` occurs **only** in the body
    of the let-binder, `w` occurs in the type of an ordinary argument, and
    nothing is annotated.  Measured output on both toolchains:

        Inductive probe@{u w v} : Type@{v} :=
            mk : Type@{w} -> let hidden := Type@{u} in probe@{u w v}.
        (* *u +w *v |= u < v
                       w < v *)

    `+w` — visited, and correctly covariant.  `*u` — never visited, because
    `whd_decompose_prod` zeta-reduced the binder away before the walk began.
    Same declaration, same kind of occurrence, one behind a `:=` and one not.

    `Print probe` emits one further line, `Arguments mk visible%_type_scope`,
    deliberately not quoted above: it is scope bookkeeping, it says nothing
    about variance, and it is the **only** text in this file that differs
    between the two toolchains for a reason of its own — 9.0.1 prints
    `visible%type_scope`, without the underscore. *)

Set Printing Universes.

Polymorphic Cumulative Inductive probe@{u w v | u < v, w < v} : Type@{v} :=
| mk (visible : Type@{w}) (hidden : Type@{v} := Type@{u}).

Print probe.

(** And the exhibit's own inductive, with the `*` annotation deleted.  Expected:

        Inductive token0@{u v} : Set :=
            make_token0 : let ghost := Type@{u} in token0@{u v}.
        (* *u *v |= u < v *)

    Upstream wrote `token@{*u v | u < v}`.  It did not have to. *)

Polymorphic Cumulative Inductive token0@{u v | u < v} : Set :=
| make_token0 (ghost : Type@{v} := Type@{u}).

Print token0.

Unset Printing Universes.

(** ** §2 — Control 1: one character.  Declare `u` invariant.

    Everything else is the exhibit, verbatim.  The annotation is *accepted* —
    `=` is sound, so the kernel takes it — and then the cast that the exhibit
    performs for free is refused:

        The term "make_tokenA" has type "let ghost := Type in tokenA"
        while it is expected to have type "tokenA"
        (universe inconsistency: Cannot enforce Set = u).

    So the check exists and works.  The defect is that inference volunteers `*`
    where it should volunteer `=`, and nothing else in the pipeline second-
    guesses it. *)

Polymorphic Cumulative Inductive tokenA@{=u v | u < v} : Set :=
| make_tokenA (ghost : Type@{v} := Type@{u}).

Polymorphic Definition read_tokenA@{u v | u < v} (t : tokenA@{u v}) : Type@{v} :=
  match t with make_tokenA ghost => ghost end.

Fail Polymorphic Definition smallA@{u v | Set < u, u < v} : Type@{u} :=
  read_tokenA@{Set u} (make_tokenA@{u v}).

(** ** §3 — Control 2: one word.  Drop cumulativity.

    A `Polymorphic` inductive with no `Cumulative` has no variance at all, so
    instances must match exactly.  Refused, with the same message:

        The term "make_tokenB" has type "let ghost := Type in tokenB"
        while it is expected to have type "tokenB"
        (universe inconsistency: Cannot enforce Set = u).

    Together with §2 this brackets the exhibit: the construction goes through
    only when variance is inferred, and only when what inference infers is `*`. *)

Polymorphic Inductive tokenB@{u v | u < v} : Set :=
| make_tokenB (ghost : Type@{v} := Type@{u}).

Polymorphic Definition read_tokenB@{u v | u < v} (t : tokenB@{u v}) : Type@{v} :=
  match t with make_tokenB ghost => ghost end.

Fail Polymorphic Definition smallB@{u v | Set < u, u < v} : Type@{u} :=
  read_tokenB@{Set u} (make_tokenB@{u v}).

(** ** §4 — Control 3: the equation, stated plainly.

    `small` is a closed term of type `Type@{u}` that converts to `Type@{u}`.
    Write that down directly and the kernel refuses it, which is the whole of
    predicativity:

        The term "Type" has type "Type@{u+1}" while it is expected to have type
         "Type@{u}"
        (universe inconsistency: Cannot enforce u < u because u = u).

    And the paradox the exhibit calls, fed an honest small type, is refused at
    the `eq_refl`:

        The term "eq_refl" has type "Type = Type" while it is expected to have type
         "Type = Small0"
        (universe inconsistency: Cannot enforce TypeNeqSmallType.Paradox.u0 =
        Small0.u1 because Small0.u1 < Small0.u0 <= TypeNeqSmallType.Paradox.u0).

    So `Hurkens` is not doing anything improper, and the exhibit's `False` is
    not inserted by the library. *)

Fail Polymorphic Definition honest@{u} : Type@{u} := Type@{u}.

Definition Small0 : Type := Type.
Fail Definition control_false : False := TypeNeqSmallType.paradox Small0 eq_refl.

(** ** §5 — Control 4: delete the let.

    The exhibit's `ghost` is let-bound.  Make it an ordinary argument — delete
    `:= Type@{u}`, nothing else — and the declaration itself is refused, because
    an inductive with a `Type@{v}`-typed argument cannot live in `Set`:

        Universe inconsistency. Cannot enforce <file>.NN+1 <= Set.

    `<file>.NN` is redacted, and it is the one message in this file that is not
    quoted literally: the universe is anonymous and file-local, so the name
    carries this file's name and the index differs between the toolchains —
    `.93+1` on 9.2 and `.97+1` on 9.0.1 for one and the same source file,
    measured.  Everything before `Cannot enforce` and after `<= Set.` is
    verbatim, and the verdict, exit 1, is identical on both.

    That is the second thing the zeta-reduction hides.  The arity check sees a
    constructor with no arguments and lets a large inductive into `Set`; the
    same declaration without the `:=` is stopped on the spot. *)

Fail Polymorphic Cumulative Inductive tokenN@{u v | u < v} : Set :=
| make_tokenN (ghost : Type@{v}).

(** ** §6 — Annex: the reduction machines do not agree with each other

    Not a control — nothing is refused in this paragraph — but a second symptom
    of the same defect, measured, and one upstream's report does not mention.
    Iota on the exhibit's `small` has to choose whose universe instance the
    reinstated let-binder carries, and the five machines choose differently.
    Measured on 9.2 and on 9.0.1, identical on both:

        Eval cbv        in smallC.   =>   = Set    : Type
        Eval lazy       in smallC.   =>   = Type   : Type
        Eval cbn        in smallC.   =>   = Set    : Type
        Eval hnf        in smallC.   =>   = Type   : Type
        Eval vm_compute in smallC.   =>   = Set    : Type

    With `Printing Universes` on, the `lazy` and `hnf` lines read
    `= Type@{i} : Type@{i}` — the *same* index on both sides, which is the
    printer emitting type-in-type in so many words.  **The kernel's conversion
    sides with `lazy`/`hnf`**, which is what makes the exhibit work and is the
    load-bearing verdict under ground rule 5: `smallC = Type@{u}` is accepted by
    `eq_refl`, and `smallC = Set` is refused —

        The term "eq_refl" has type "smallC = smallC"
        while it is expected to have type "smallC = Set"
        (universe inconsistency: Cannot enforce Set = u).

    so the three machines that print `Set` are printing something the kernel
    will not certify.  `Eval` output is not a soundness channel and no claim in
    this repository rests on it. *)

Polymorphic Cumulative Inductive tokenC@{u v | u < v} : Set :=
| make_tokenC (ghost : Type@{v} := Type@{u}).

Polymorphic Definition read_tokenC@{u v | u < v} (t : tokenC@{u v}) : Type@{v} :=
  match t with make_tokenC ghost => ghost end.

Polymorphic Definition smallC@{u v | Set < u, u < v} : Type@{u} :=
  read_tokenC@{Set u} (make_tokenC@{u v}).

Eval cbv        in smallC.
Eval lazy       in smallC.
Eval cbn        in smallC.
Eval hnf        in smallC.
Eval vm_compute in smallC.

Polymorphic Definition smallC_is_universe@{u v | Set < u, u < v} :
  @eq Type@{v} smallC@{u v} Type@{u} := eq_refl.

Fail Polymorphic Definition smallC_is_Set@{u v | Set < u, u < v} :
  @eq Type@{v} smallC@{u v} Set := eq_refl.
