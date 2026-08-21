(** * rocq#22387 with the seal removed — and now `rocqchk` refuses it

    [LetinOrderSubtyping.v] ends with `Module Applied : R := F A.`, ascribing
    the applied functor to a signature that declares `result : False`.  This
    file is the same construction with that ascription **deleted**: the module
    is applied plainly, and the `False` is obtained by conversion, because
    `match 1 with O => True | S _ => False end` *is* `False`.

    Nothing else changes.  One line, and the audit surface changes shape.

    ** Measured, on Rocq 9.2 and on Rocq Platform 9.0.1

      - `coqc` on this file:                **exit 0**.
      - `Print Assumptions contradiction`:  `Closed under the global context`.
      - `Print Assumptions one_eq_two`:     `Closed under the global context`.
      - `rocqchk` on the `.vo`:             **rejected**, exit 129 —

            checking module: <file>.Applied
            checking cst:<file>.Applied.result
            Fatal Error: Type error: ActualType

      - `rocqchk -bytecode-compiler yes`:   rejected the same way, exit 129.

    ** What the pair establishes

    `rocqchk` **does** re-typecheck the substituted body of a functor
    application, and the substituted body of this one is ill-typed — the proof
    term `I` is checked against a type that has become `False`.  So the
    independent checker owns a working safeguard against rocq#22387, and it
    fires here.

    In [LetinOrderSubtyping.v] it does not fire, and the reason is not that the
    construction is different — it is the same construction — but that
    `Module M : Sig := F A` writes `M`'s components into the `.vo` **without
    bodies**.  There is then nothing for `rocqchk` to re-check; it lists
    `Applied.result` under `* Axioms:` and reports
    `Modules were successfully checked` at exit 0.  Controls §5 shows an honest
    sealed functor application producing the identical `* Axioms:` line, so that
    line does not distinguish the two.

    **Sealing a module removes the only check that would have caught this.**
    That is a statement about rocq#22387 that upstream's report does not make,
    and it is measured here in the difference between two files that differ by
    one ascription.

    ** Where this sits among the module-system exhibits

      - [UniverseFlagDesync.v] (rocq#22287): `coqc` accepts, `rocqchk` rejects,
        and a `Require` of the `.vo` is rejected at the `Require` line.
      - [GuardFlagThroughFunctor.v] (rocq#22366): `coqc` accepts, `rocqchk`
        rejects with `IllFormedRecBody`.
      - **this file** (rocq#22387, unsealed): `coqc` accepts, `rocqchk` rejects
        with `ActualType`.
      - [LetinOrderSubtyping.v] (rocq#22387, sealed): `coqc` accepts and
        `rocqchk` accepts.

    Same defect, last two rows, and the ascription is the whole difference.

    ** This file is EXPECTED TO BE ACCEPTED BY `coqc` AND REJECTED BY `rocqchk`.
    A `coqc` failure here is a regression; a `rocqchk` exit 0 here would mean
    the checker had lost its re-check of functor bodies. *)

Module Type S.
  Variant T := c (x : nat) (z : nat := 0).
End S.

Module A.
  Variant T := c (z : nat := 0) (x : nat).
End A.

Module F (X : S).
  Definition result :
    match (match X.c 1 with X.c x z => z end) with
    | O => True | S _ => False end := I.
End F.

(** No ascription.  `Applied.result`'s type is the substituted `match`, which
    converts to `False` — so the coercion below needs no signature to state it. *)
Module Applied := F A.

Definition contradiction : False := Applied.result.

(** `Closed under the global context` *)
Print Assumptions contradiction.

Definition one_eq_two : 1 = 2 := match contradiction with end.

(** `Closed under the global context` *)
Print Assumptions one_eq_two.
