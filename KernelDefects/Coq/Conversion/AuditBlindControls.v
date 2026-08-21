(** * Controls for the 2026-08-20 wave: seven deliberately-broken twins

    Ground rule 6.  Every exhibit next door is *accepted* by `coqc` at exit 0
    with a clean `Print Assumptions`, and acceptance is evidence only if the
    same procedure, on the same toolchain, rejects a twin that differs by as
    little as possible.  Each module below is one such twin.

    **Every rejection here is asserted, not narrated.**  `Fail` succeeds only
    when the command it wraps is refused, so if any of these constructions ever
    starts being accepted this file stops compiling.  The literal messages are
    quoted in each module's comment; they were obtained by running the same
    module with the `Fail` removed, and they are reproduced verbatim.

    ** Toolchain matrix

      - The Rocq Prover 9.2 (OCaml 4.14.2), native compiler disabled:
        `coqc AuditBlindControls.v` -> **exit 0**, all seven rejected.
      - Rocq Platform 9.0.1,
        `coqc.exe -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"`:
        **exit 0**, all seven rejected.

    Six of the seven give **character-for-character the same message** on 9.0.1
    as on 9.2.  C87 is the exception and the quotation below is 9.2's: 9.0.1
    rejects the same functor application on the same field, but does not print
    the two bodies, giving only

      Error: Signature components for field T_rect do not match:
      the body of definitions differs.

    Same field, same reason, less detail.  Measured on both.

    The eighth control, for rocq#22391, lives in `AuditBlindStuckCase.v` instead:
    on 9.0.1 it aborts with an `Anomaly "in Univ.repr: Universe Var(0) undefined."`
    which `Fail` cannot catch, and this file has to stay green on both. *)

(** ** C78 — rocq#22378, and the token is `SProp`.

    The exhibit's two let-bound ghost fields live in `SProp`; here they live in
    `Prop`.  Nothing else changes.  Rejected:

      In environment
      p : pr
      The term "eq_refl" has type "fst_of p = fst_of p"
      while it is expected to have type "fst_of p = snd_of p"
      (cannot unify "fst_of p" and "snd_of p").

    So it is the irrelevance of the let-bound fields, not their presence, that
    makes `convert_under_context` push four relevance annotations onto two
    surviving binders. *)

Module C78.
  Inductive sUnit : Prop := stt.
  Inductive pr : Type := pack (x y : nat) (g1 : sUnit := stt) (g2 : sUnit := stt).
  Definition fst_of (p : pr) : nat := match p with pack x y _ _ => x end.
  Definition snd_of (p : pr) : nat := match p with pack x y _ _ => y end.
  Fail Definition collision (p : pr) : fst_of p = snd_of p := eq_refl.
End C78.

(** ** C82 — rocq#22382, and the token is the `carry` let-binder.

    The exhibit opens the inner `fix` with `(carry : nat := seed)`; here that
    binder is gone and `seed` is passed at the recursive call instead.  Same
    recursion, one binder fewer.  Rejected:

      Recursive definition of russell is ill-formed.
      In environment
      russell : nat -> Type
      n : nat
      smaller : nat
      seed := n : nat
      inner : nat -> nat -> Type
      p : nat
      m : nat
      Recursive call to russell has principal argument equal to
      "p" instead of one of the following variables: "smaller" "m".

    The guard checker is awake and says exactly the right thing; the let-binder
    is what makes `find_uniform_parameters` miscount past it. *)

Module C82.
  Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
    fix inner (p m : nat) {struct m} : Type :=
      match m with O => outer p -> False | S rest => inner seed rest end.
  Fail Fixpoint russell (n : nat) : Type :=
    match n with O => True | S smaller => relay russell n smaller smaller end.
End C82.

(** ** C83 — rocq#22383, and the token is `*` becoming `=`.

    `*u` declares `u` irrelevant to `token`'s subtyping, which is the answer
    cumulativity inference reaches on its own once `whd_decompose_prod` has
    erased the `let`.  `=u` declares it invariant, which is the right answer.
    Rejected:

      The term "make_token" has type "let ghost := Type in token"
      while it is expected to have type "token"
      (universe inconsistency: Cannot enforce Set = u).

    The message prints `let ghost := Type in token` — the very binding the
    inference had discarded. *)

Module C83.
  Polymorphic Cumulative Inductive token@{=u v | u < v} : Set :=
  | make_token (ghost : Type@{v} := Type@{u}).
  Polymorphic Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
    match t with make_token ghost => ghost end.
  Fail Polymorphic Definition small@{u v | Set < u, u < v} : Type@{u} :=
    read_token@{Set u} (make_token@{u v}).
End C83.

(** ** C86 — rocq#22386, and the token is the codomain's name.

    Both `let`s are kept, exactly as in the exhibit; only the `cofix`'s declared
    codomain is spelled `Empty` instead of `actual`.  Rejected:

      Recursive definition of recur is ill-formed.
      In environment
      actual := Empty : Type
      decoy := Stream : Type
      recur : Empty
      The codomain is "Empty"
      which should be a coinductive type.
      Recursive definition is: "wrap recur".

    The check exists and fires the moment the name is written out, which is what
    pins the defect on the environment the rectree is computed in. *)

Module C86.
  CoInductive Stream : Type := next : Stream -> Stream.
  Inductive Empty : Type := wrap : Empty -> Empty.
  Fail Definition cycle : Empty :=
    let actual := Empty in
    let decoy := Stream in
    cofix recur : Empty := wrap recur.
End C86.

(** ** C89 — rocq#22389, and the token is `cycle` becoming `f`.

    `g`'s body names the *outer* cofixpoint twice in the exhibit; here it names
    the inner block's own `f` in both positions.  Rejected:

      Recursive definition of g is ill-formed.
      In environment
      cycle : C I
      f : C I
      g : D (C I) I
      Recursive call on a non-recursive argument of constructor "f".
      Recursive definition is: "dc (C I) I f (ic f)".

    The guard is checking `g`.  It simply checks the outer name against the
    inner block's rectree, and the same occurrence under the same inductive
    constructor is refused as soon as it is spelled with a name that tree
    knows. *)

Module C89.
  Unset Elimination Schemes.
  CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
  CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
  Inductive I : Type := ic : C I -> I.
  Fail CoFixpoint cycle : C I :=
    (cofix f : C I := cc I f g
     with g : D (C I) I := dc (C I) I f (ic f)
     for f).
End C89.

(** ** C87 — rocq#22387, and the token is a whole line: `Unset Elimination Schemes`.

    The near-miss exhibit needs that line.  Without it, the same functor
    application is refused:

      Signature components for field T_rect do not match:
      the body of definitions differs: expected
      "fun (P : A.T -> Type) (c : forall x : nat, let z := 0 in P (A.c x))
         (t : A.T) => match t as t0 return P t0 with | A.c x _ => c x end"
      but found
      "fun (P : A.T -> Type) (c : let z := 0 in forall x : nat, P (A.c x))
         (t : A.T) => match t as t0 return P t0 with | A.c _ x => c x end".

    Read the field name: `T_rect`, not `T`.  The subtyping check on the
    inductive's own type passes — that is the defect — and what catches it is
    the subtyping check on the **generated eliminator**, whose body preserves
    the argument order the type had lost.  This is one of the two reasons #22387
    is not counted among the six: its safeguard is on by default and the exhibit
    has to turn it off.  The other is that `rocqchk` rejects the same
    construction outright once the module ascription is removed — see
    `AuditBlindSubtypeLetin.v`. *)

Module C87.
  Module Type S. Inductive T := c (x : nat) (z : nat := 0). End S.
  Module A. Inductive T := c (z : nat := 0) (x : nat). End A.
  Module F (X : S).
    Definition result :
      match (match X.c 1 with X.c x z => z end) with
      | O => True | S _ => False end := I.
  End F.
  Module Type R. Parameter result : False. End R.
  Fail Module Applied : R := F A.
End C87.
