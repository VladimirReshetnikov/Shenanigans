(** * Controls for LetinOrderSubtyping.v — five arrangements, three refusals

    rocq#22387.  Acceptance of the exhibit means nothing unless the same
    procedure, on the same toolchain, **rejects** the neighbouring
    arrangements, and unless the one audit line the exhibit does produce is
    shown to carry no information.  Both are done here.

    Ground rule 6.  Every message below was measured on Rocq 9.2 and again on
    Rocq Platform 9.0.1 (`coqc -coqlib C:\Rocq-Platform~9.0~2025.08\lib\coq`).
    `coqc` does not print the text of a `Fail`, so each message was captured by
    deleting the `Fail` and reading the resulting `Error:`.

    **Every verdict is the same on the two toolchains, but two of the four
    messages are not.**  §2 and §6 are character-identical.  §1 and §3 are
    shorter on 9.0.1: 9.2 prints the two differing constructor types and the two
    differing scheme bodies, and 9.0.1 prints only that they differ.  Both texts
    are quoted in place, and the shorter one is marked.  Ground rule 4 —
    a matrix, not a verdict.

    This file contains no `Set` and no `Unset`.

    ** What is measured here

      §1  the same reorder, with **ordinary arguments instead of a let**:
          refused.  This is the isolation — `:= 0` is what blinds the check.
      §2  the same modules with **no reorder at all**: the ascription refuses,
          which proves the exhibit's ascription is a real check and not a hole.
      §3  the exhibit with `Variant` changed back to **`Inductive`**: refused,
          at the generated `T_rect`'s *body*.  This is why upstream needed
          `Unset Elimination Schemes`, and why this repository's spelling does
          not.
      §4  **order is sufficient but not necessary**: same order, different let
          *body*, and the same closed `False` comes out.
      §5  an **honest** sealed functor application, to show that the exhibit's
          `* Axioms: ...Applied.result` line in `rocqchk -o` is what sealing
          always produces and not a catch.
      §6  why a reorder of two ordinary arguments of the *same* type is
          harmless even when it is accepted — the mechanism, stated as an
          experiment. *)

(** ** §1 — Control 1: the same reorder, with no let

    `S1` and `A1` declare the same two constructor arguments in opposite
    orders, exactly as the exhibit's `S` and `A` do.  The only difference from
    the exhibit is that the second declaration is an ordinary argument rather
    than a let-binding — delete `:= 0`, give it a type that makes the swap
    observable, and nothing else.  Refused, before any functor body is
    substituted:

        Signature components for field T do not match:
        types given to constructor c differ: expected "nat -> bool -> A1.T" but found
        "bool -> nat -> A1.T".

    On 9.0.1 the same rejection, with less detail printed:

        Signature components for field T do not match:
        types given to c differ.

    So constructor argument order **is** compared, and the comparison works.
    Writing `:= 0` on the second declaration turns `nat -> nat -> T` and
    `nat -> nat -> T`... into two zeta-equal telescopes whose order the
    comparison can no longer see. *)

Module Type S1.
  Variant T := c (x : nat) (z : bool).
End S1.

Module A1.
  Variant T := c (z : bool) (x : nat).
End A1.

Module F1 (X : S1).
  Definition result : True := I.
End F1.

Fail Module Applied1 := F1 A1.

(** ** §2 — Control 2: the same modules, with no reorder

    `S2` and `A2` are identical.  `F2 A2` is accepted — as it should be — and
    the ascription to a signature demanding `False` is then refused:

        Signature components for field result do not match: expected type
        "False" but found type
        "match match A2.c 1 with
               | A2.c _ z => z
               end with
         | 0 => True
         | S _ => False
         end".

    That matters because the exhibit's last step is exactly this ascription.
    Here the branch really does return the let's `0`, the outer `match` really
    is `True`, and the check says so.  The exhibit's `False` therefore comes
    from the reordering and not from a broken signature check. *)

Module Type S2.
  Variant T := c (x : nat) (z : nat := 0).
End S2.

Module A2.
  Variant T := c (x : nat) (z : nat := 0).
End A2.

Module F2 (X : S2).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F2.

Module Type R2. Parameter result : False. End R2.

Fail Module Applied2 : R2 := F2 A2.

(** ** §3 — Control 3: `Variant` back to `Inductive`, and the flag question

    This is upstream's spelling minus `Unset Elimination Schemes`, and it is
    **refused** — which is why upstream's reproducer carries that flag.  What
    refuses it is not the inductive and not the constructor: it is the
    automatically generated `T_rect`, whose *body* differs in exactly the
    pattern order the constructor type could not express.

        Signature components for field T_rect do not match:
        the body of definitions differs: expected
        "fun (P : A3.T -> Type) (c : forall x : nat, let z := 0 in P (A3.c x))
           (t : A3.T) =>
         match t as t0 return P t0 with
         | A3.c x _ => c x
         end"
        but found
        "fun (P : A3.T -> Type) (c : let z := 0 in forall x : nat, P (A3.c x))
           (t : A3.T) =>
         match t as t0 return P t0 with
         | A3.c _ x => c x
         end".

    On 9.0.1 the same rejection, with less detail printed:

        Signature components for field T_rect do not match:
        the body of definitions differs.

    Read the 9.2 text as a diagnosis of the exhibit.  The scheme is a *term* containing
    a `match`, so its comparison is a comparison of branch contexts, and branch
    contexts do keep the order.  The constructor **type** is compared up to
    conversion, and conversion does not.  The kernel already holds the
    information needed to reject `A3 <: S3`; it just never asks for it in the
    place that decides subtyping.

    `Variant` differs from `Inductive` only in that it generates elimination
    schemes when `Nonrecursive Elimination Schemes` is set, and that flag is
    **off by default**.  So the exhibit's signature has no scheme, nothing
    notices, and no flag was needed to arrange it — the difference between
    upstream's escape-hatch spelling and this repository's flag-free one is one
    word. *)

Module Type S3.
  Inductive T := c (x : nat) (z : nat := 0).
End S3.

Module A3.
  Inductive T := c (z : nat := 0) (x : nat).
End A3.

Module F3 (X : S3).
  Definition result : True := I.
End F3.

Fail Module Applied3 := F3 A3.

(** ** §4 — Probe: does declaration ORDER matter?  Sufficient, not necessary

    `S4` and `A4` declare their two arguments in the **same** order.  The only
    difference is the let's *body*: `z := 0` in the signature, `z := 1` in the
    module.  Whole-arity conversion zeta-reduces both to `nat -> T` and never
    looks at either value, so `A4 <: S4` is accepted; `match` reinstates `A4`'s
    binder, the branch returns `1`, and the outer `match` is `False` again.

    **Accepted, with `Closed under the global context`.**

    So the catalog's question — "is the finding that declaration order is
    significant to `match` but invisible to whole-arity conversion?" — has the
    answer: order is *one* sufficient trigger, and it is not necessary.  The
    binder's position and the binder's body are erased by the same zeta, and
    `match` depends on both.  Upstream's reproducer varies the position; this
    one varies the value; the defect is that neither survives the comparison. *)

Module Type S4.
  Variant T := c (x : nat) (z : nat := 0).
End S4.

Module A4.
  Variant T := c (x : nat) (z : nat := 1).
End A4.

Module F4 (X : S4).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F4.

Module Type R4. Parameter result : False. End R4.

Module Applied4 : R4 := F4 A4.

Definition order_is_not_necessary : False := Applied4.result.

(** `Closed under the global context` *)
Print Assumptions order_is_not_necessary.

(** ** §5 — Control 4: the `rocqchk -o` axiom line is not a catch

    `rocqchk -o` on the exhibit prints

        * Axioms:
            LetinOrderSubtyping.Applied.result

    A reader could take that for the checker noticing something.  It is not.
    `Module M : Sig := F A` writes `M`'s components into the `.vo` with **no
    bodies**, so `rocqchk` has nothing to re-check and lists them as axioms
    whatever they are.  Below is the same shape with `True` where the exhibit
    has `False` and nothing whatsoever wrong with it.  Measured on this file's
    `.vo`, on both toolchains:

        * Axioms:
            LetinOrderSubtypingControls.Applied5.result
            LetinOrderSubtypingControls.Applied4.result

    `Applied5` is honest.  Same line, same shape, no defect.  The line reports
    sealing, not assumption.

    Meanwhile `Print Assumptions` — looking at the very same constant — says
    `Closed under the global context`, in §4 above and here.  The two audits
    disagree about what `Applied.result` is, and neither disagreement is about
    soundness. *)

Module Type S5.
  Variant T := c (x : nat) (z : nat := 0).
End S5.

Module A5.
  Variant T := c (x : nat) (z : nat := 0).
End A5.

Module F5 (X : S5).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F5.

Module Type R5. Parameter result : True. End R5.

Module Applied5 : R5 := F5 A5.

Definition honest_sealed : True := Applied5.result.

(** `Closed under the global context` — as for §4's `False`. *)
Print Assumptions honest_sealed.

(** ** §6 — Probe: why the let is load-bearing, and not just "an argument"

    §1 showed a reorder of two ordinary arguments being *caught*, because their
    types differed.  Give them the **same** type and the reorder is not caught —
    and it is also harmless, which is the point.

    `S6` and `A6` both declare `c` with two `nat` arguments, swapped.  Both
    constructor types are `nat -> nat -> T`, so subtyping accepts; there is
    genuinely nothing to reject.  The functor must now write `X.c 1 0`, and
    under `A6` that application is reordered along with the declaration, so the
    branch returns `0` and `result` stays `True`.  The ascription to `False` is
    refused:

        Signature components for field result do not match: expected type
        "False" but found type
        "match match A6.c 1 0 with
               | A6.c _ z => z
               end with
         | 0 => True
         | S _ => False
         end".

    **A let-binding is never supplied at the application site.**  That is the
    whole asymmetry: move an ordinary argument and the caller's argument moves
    with it, so the two displacements cancel; move a let and only the *reading*
    moves, and the mismatch is left standing.  It is not "order is compared
    loosely" — it is that a let-in occupies a position in the declaration list
    while contributing nothing to the arity that conversion compares. *)

Module Type S6.
  Variant T := c (x : nat) (z : nat).
End S6.

Module A6.
  Variant T := c (z : nat) (x : nat).
End A6.

Module F6 (X : S6).
  Definition result :
    match (match X.c 1 0 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F6.

Module Type R6. Parameter result : False. End R6.

Fail Module Applied6 : R6 := F6 A6.
