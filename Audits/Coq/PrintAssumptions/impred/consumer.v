(** * rocq#22164 — half two: compiled WITHOUT the flag, and the audit is silent

    The .vo this `Require`s was built with `-impredicative-set`.  In a
    predicative session `Print Assumptions` says nothing about it — and says
    nothing about a fresh constant built on top of it either.  Recompile THIS
    file with the flag, against the SAME .vo, and both answers change to
    `Theory: Set is impredicative`.

    So the audit's answer is a function of the reader's flags rather than of the
    artifact being audited.  Upstream classifies this `kind: enhancement` +
    `part: printer` rather than `kind: inconsistency`, and the fix (merged
    2026-07-15) is a flag that is OFF by default — so even 9.3+rc1's default
    `Print Assumptions` still has the blind spot. *)

Require Import prereq.

(** Predicative session: `Closed under the global context`.
    Impredicative session, same .vo: `Theory: Set is impredicative`. *)
Print Assumptions impred_def.

Definition uses_it : impred_def := fun X x => x.

(** Same again for a constant defined here. *)
Print Assumptions uses_it.

(** Control, and it is not vacuous: recompiling this file with
    `-impredicative-set` makes the `Fail` itself fail. *)
Fail Definition local_attempt : Set := forall X : Set, X -> X.
