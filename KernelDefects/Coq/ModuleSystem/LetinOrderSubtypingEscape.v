(** * The escape half of rocq#22387

    [LetinOrderSubtyping.v] is accepted with a clean [Print Assumptions] and an
    exit-0 [rocqchk] in both conversion modes.  This file asks the question that
    decides how bad that is: does the [False] reach a consumer?

    **It does.**  This file is ordinary Rocq — no flag, no module, no functor,
    no tactic — that merely [Require]s the exhibit.  It is EXPECTED TO BE
    ACCEPTED.

    ** Measured, on Rocq 9.2 and on Rocq Platform 9.0.1

      - `coqc` on this file:                **exit 0**.
      - `Print Assumptions escaped`:        `Closed under the global context`.
      - `Print Assumptions two_plus_two`:   `Closed under the global context`.
      - `rocqchk` on the `.vo`:             exit 0, both conversion modes.
      - `rocqchk -o`:                       `* ... type-in-type: <none>`,
                                            `* ... unsafe (co)fixpoints: <none>`,
                                            and the exhibit's inherited
                                            `* Axioms: ...Applied.result`,
                                            which controls §5 shows an honest
                                            sealed module produces too.

    ** What that adds to the exhibit

    Contrast [UniverseFlagDesyncImport.v] (rocq#22287), which is **rejected at
    the [Require] line** because the inconsistency lives in the `.vo`'s universe
    graph.  Contrast [LetinOrderSubtypingUnsealed.v], the same construction
    unsealed, whose `.vo` `rocqchk` refuses outright.

    Here neither happens.  The `.vo` the exhibit produced contains a sealed
    module whose `result` component is *declared* to have type `False`, and a
    consumer that believes the signature — which is the only thing a consumer
    ever gets — inherits the `False` with a clean audit of its own.  This is a
    library that can be misstated, not merely a file that lies about itself. *)

Require Import LetinOrderSubtyping.

Definition escaped : False := contradiction.

(** `Closed under the global context` *)
Print Assumptions escaped.

Definition two_plus_two : 2 + 2 = 5 := match escaped return 2 + 2 = 5 with end.

(** `Closed under the global context` *)
Print Assumptions two_plus_two.
