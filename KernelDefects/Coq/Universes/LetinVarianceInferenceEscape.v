(** * The escape half of rocq#22383

    [LetinVarianceInference.v] is accepted with a clean [Print Assumptions] AND
    a clean [rocqchk], in both of `rocqchk`'s conversion modes.  This file asks
    the question that decides how bad that is: does the [False] reach a
    consumer?

    **It does.**  This file is ordinary Rocq — no flag, no attribute, no module,
    no tactic, no universe annotation — that merely [Require]s the exhibit.  It
    is EXPECTED TO BE ACCEPTED, and every channel is clean here too.

    ** Measured, on Rocq 9.2 and on Rocq Platform 9.0.1

      - `coqc` on this file:                 **exit 0**.
      - `Print Assumptions escaped`:         `Closed under the global context`.
      - `Print Assumptions two_plus_two`:    `Closed under the global context`.
      - `rocqchk` on the `.vo`:              exit 0, and `rocqchk -o` reports
                                             `* Axioms: <none>`,
                                             `* ... type-in-type: <none>`,
                                             `* ... unsafe (co)fixpoints: <none>`.

    ** Why that matters here specifically

    Contrast [../ModuleSystem/UniverseFlagDesync.v] (rocq#22287), where the
    inconsistency is written into the `.vo`'s universe graph and a [Require] of
    it is rejected **at the [Require] line** — there, the damage is confined to
    the file that caused it.  Contrast also
    [../ModuleSystem/LetinOrderSubtypingUnsealed.v] (rocq#22387), where `coqc`
    accepts but `rocqchk` refuses the `.vo` outright.

    Here there is nothing for a consumer or for the checker to trip over,
    because **the term really is well typed under the universe graph the
    exhibit shipped**.  Variance inference wrote a wrong graph, and every
    subsequent check is faithful to it.  That is the difference between a defect
    the toolchain contains and one it propagates. *)

Require Import LetinVarianceInference.

Definition escaped : False := contradiction.

(** `Closed under the global context` *)
Print Assumptions escaped.

Definition two_plus_two : 2 + 2 = 5 := match escaped return 2 + 2 = 5 with end.

(** `Closed under the global context` *)
Print Assumptions two_plus_two.
