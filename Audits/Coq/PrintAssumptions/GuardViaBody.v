(** * Control for GuardViaType.v — the same flag, reachable from the body *)

Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n.
Set Guard Checking.

Definition viaBody : nat := match loop 0 return nat with end.

(** Expected: `Axioms: loop is assumed to be guarded.` *)
Print Assumptions viaBody.
