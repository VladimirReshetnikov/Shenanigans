(** * rocq#21825 — `Print Assumptions` does not traverse the type of a definition

    Live on every released Coq/Rocq up to and including 9.2.0.  Fixed by
    PR #21825 (Jason Gross, merged 2026-03-26) from a branch point past the
    V9.2.0 tag, so the fix is carried only by the V9.3+rc1 prerelease.

    `foo`'s TYPE mentions the axiom; its body does not.  The control `bodydep`
    is the same axiom in the body position, and is reported correctly — which is
    what makes the first answer a defect rather than a policy. *)

Axiom ax : nat.
Definition ty := (fun _ : nat => nat) ax.
Definition foo : ty := 0.

(** Expected on 9.2.0: `Closed under the global context` — the defect. *)
Print Assumptions foo.

(** ** Control: the same axiom, reachable from the body. *)

Axiom ax3 : nat.
Definition bodydep : nat := ax3.

(** Expected: `Axioms: ax3 : nat`. *)
Print Assumptions bodydep.
