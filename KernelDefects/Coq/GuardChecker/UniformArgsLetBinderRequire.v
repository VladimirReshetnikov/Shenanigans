(** * The escape half of rocq#22382

    ./UniformArgsLetBinder.v is accepted with a clean [Print Assumptions] and a
    clean [rocqchk].  This file asks the question that decides how much that
    costs: does the [False] reach a consumer?

    **It does.**  This file is ordinary Rocq -- no flag, no module, no tactic,
    no attribute -- that merely [Require]s the exhibit.  It is EXPECTED TO BE
    **ACCEPTED**, exit code 0, and both its own [Print Assumptions] lines and
    [rocqchk] on its .vo are clean.

    That is the ./WrongEnvReduction.v / ./WrongEnvReductionEscape.v shape and
    not the ../ModuleSystem/UniverseFlagDesync.v one.  There the inconsistency
    is written into the .vo's universe graph and a [Require] of it is refused at
    the [Require] line; here the imported terms are *well typed* and only their
    guardedness was decided wrongly, so there is nothing for a consumer -- or
    for the independent checker, which re-runs the same guard checker -- to trip
    over.

    Measured on The Rocq Prover 9.2 (OCaml 4.14.2):

      coqc   this file                exit 0    three clean audits
      rocqchk (default)               exit 0    Modules were successfully checked
      rocqchk -bytecode-compiler yes  exit 0    Modules were successfully checked
      rocqchk -o                      * Axioms: <none>
                                      * ... type-in-type: <none>
                                      * ... unsafe (co)fixpoints: <none>

    and on The Rocq Prover 9.0.1 (Rocq Platform 9.0~2025.08):

      coqc   this file                exit 0    three clean audits
      coqchk                          exit 0    Modules were successfully checked

    Both constructions escape, which matters because they are triggered
    differently: [escaped] comes from the [let] in the binder prefix and
    [escaped_beta] from the hidden beta-redex. *)

Require Import UniformArgsLetBinder.

Definition escaped : False := contradiction.

(** [Closed under the global context] *)
Print Assumptions escaped.

Definition escaped_beta : False := contradiction_beta.

(** [Closed under the global context] *)
Print Assumptions escaped_beta.

Definition anything : 2 + 2 = 5 := match escaped return 2 + 2 = 5 with end.

(** [Closed under the global context] *)
Print Assumptions anything.
