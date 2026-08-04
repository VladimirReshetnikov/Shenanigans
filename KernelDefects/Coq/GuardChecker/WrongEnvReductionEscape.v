(** * The escape half of rocq#21839

    [WrongEnvReduction.v] is accepted with a clean [Print Assumptions] AND a
    clean [coqchk].  This file asks the question that decides how bad that is:
    does the [False] reach a consumer?

    **It does.**  This file is ordinary Rocq — no flag, no module, no tactic —
    that merely [Require]s the exhibit.  It is EXPECTED TO BE ACCEPTED, and both
    its own [Print Assumptions] lines and [coqchk] on its [.vo] are clean.

    That is the difference from ../ModuleSystem/UniverseFlagDesync.v, where the
    inconsistency is written into the [.vo]'s universe graph and a [Require] of
    it is rejected at the [Require] line.  Here the term is *well typed* — only
    its guardedness was decided wrongly — so there is nothing in the [.vo] for a
    consumer, or for [coqchk], to trip over.

    Together the two files establish the claim that makes rocq#21839 the
    strongest route in this repository: it is the only one where BOTH channels
    this catalog uses to price a proof of [False] report nothing, AND the [False]
    propagates. *)

Require Import WrongEnvReduction.

Definition escaped : False := oops.

(** [Closed under the global context] *)
Print Assumptions escaped.

Definition anything : 2 + 2 = 5 := match escaped return 2 + 2 = 5 with end.

(** [Closed under the global context] *)
Print Assumptions anything.
