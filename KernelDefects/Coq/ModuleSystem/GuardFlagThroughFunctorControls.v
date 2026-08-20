(** * Controls for GuardFlagThroughFunctor.v — the audit works either side of one token

    rocq#22366.  Acceptance of the exhibit means nothing unless the same audit,
    on the same toolchain, correctly names the flag in the neighbouring
    arrangements.  It does, twice.

    ** Control 1 — direct use, no functor

    The honest route of ../../../EscapeHatches/Coq/TypingFlags.v §1.  Expected:

        Axioms:
        loopD is assumed to be guarded.

    ** Control 2 — the same functor, WITHOUT `Parameter Inline`

    Everything else is identical to the exhibit: the same module type, the same
    functor, the same `Unset Guard Checking` around the application, the same
    non-terminating fixpoint supplied as the argument.  Expected:

        Axioms:
        X2.T is assumed to be guarded.

    So the flag survives a functor application on its own.  What loses it is
    `Inline` — one token — and that isolation is this repository's measurement
    rather than upstream's. *)

(** ** Control 1 *)

Unset Guard Checking.
Fixpoint loopD (n:nat) : False := loopD (S n).
Set Guard Checking.

Definition boomD : False := loopD 0.
Print Assumptions boomD.

(** ** Control 2 *)

Module Type set2.
  Parameter T : (nat -> False).
End set2.

Module F2(S:set2).
  Definition loop : nat -> False := S.T.
End F2.

Module X2.
  Local Unset Guard Checking.
  Fixpoint T (n:nat) : False := T (S n).
End X2.

Unset Guard Checking.
Module M2 := F2 X2.
Set Guard Checking.

Definition boom2 : False := M2.loop 0.
Print Assumptions boom2.
