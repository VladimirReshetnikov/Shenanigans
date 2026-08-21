(** * Control for the `Require` channel: an audit that DOES speak across it

    Not a defect, and not a proof of `False`.  This file exists so that
    `AuditBlindSextet.v`'s six silent `Print Assumptions` lines mean something.

    ** Why it is needed

    The claim being made next door is that six proofs of `False` from the
    2026-08-20 wave cross a plain `Require` and leave the consumer's audit clean.
    A clean audit is only evidence if a dirty one would have shown.  So this file
    declares an ordinary constant whose cost `Print Assumptions` is *supposed* to
    report, and the consumer reports it — through exactly the same `Require`, in
    exactly the same command.

    ** Why definitional UIP, specifically

    Because it is the cost that two of the nine issues of that morning actually
    carry.  rocq#22376 and rocq#22380 both derive `False`, both with `coqc`
    exit 0, and `Print Assumptions contradiction` says
    `seq relies on definitional UIP.` on each.  That is ground rule 1 working:
    the `False` is conditional, the condition is in the audit, and the class
    belongs in `Paradoxes/` rather than here.  The same reporting machinery, on
    the same day, is what stays silent on the other six.

    ** Measured on Rocq 9.2

      - `coqc AuditBlindUipControl.v`     exit 0
      - `Print Assumptions reported`      `Axioms:` / `seq relies on definitional UIP.`
      - downstream, after a plain `Require`:
                                          `AuditBlindUipControl.seq relies on
                                           definitional UIP.`
      - `rocqchk -o`                      `* Axioms: <none>`

    The last line is worth keeping.  `rocqchk`'s context summary has **no
    definitional-UIP row at all**: it reports axioms, type-in-type, unsafe
    (co)fixpoints and assumed positivity, and definitional UIP is none of those.
    So on this file the two audits disagree in the *opposite* direction from
    rocq#22387 — `Print Assumptions` names a cost that `rocqchk -o` does not
    know how to name.  Measured, not inferred: run the two commands. *)

Set Definitional UIP.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

Definition transport {A : Type} (P : A -> Type) {x y : A} (e : seq x y)
  : P x -> P y :=
  match e in seq _ y return P x -> P y with srefl _ => fun v => v end.

Definition reported : nat -> nat :=
  transport (fun _ => nat -> nat) (srefl 0) (fun n => n).

(** Expected: [Axioms:] / [seq relies on definitional UIP.] *)
Print Assumptions reported.
