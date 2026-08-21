(** * The extension: it is not only axioms

    `Print Assumptions` walks the same reachable set to report `bypass_check`
    typing flags, so a flag-carrying constant reachable ONLY through a type is
    dropped too.  Here the guard-checking flag vanishes.

    Compare GuardViaBody.v, which is the same flag on the same constant in the
    body position and reports it.  Same file pair, same flag, two answers. *)

Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n.
Set Guard Checking.

Definition tyG := (fun _ : False => nat) (loop 0).
Definition viaType : tyG := 0.

(** Expected on 9.2.0: `Closed under the global context` — the flag is gone. *)
Print Assumptions viaType.
