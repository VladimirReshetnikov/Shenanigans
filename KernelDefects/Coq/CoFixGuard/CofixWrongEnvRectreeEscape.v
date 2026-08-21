(** * The escape half of rocq#22386

    CofixWrongEnvRectree.v is accepted with a clean [Print Assumptions] AND a
    clean [rocqchk], in both the default and the [-bytecode-compiler yes] lane,
    on 9.2 and on 9.0.1.  This file asks the question that decides how much that
    costs: **does the [False] reach a consumer?**

    **It does.**  What follows is ordinary Rocq — no flag, no module, no tactic,
    no [cofix] of its own — that merely [Require]s the exhibit.  THIS FILE IS
    EXPECTED TO BE **ACCEPTED**, exit 0, and both of its own [Print Assumptions]
    lines and [rocqchk] on its own [.vo] are clean.

    Measured, on both installed toolchains:

    | Channel                            | 9.2 | 9.0.1 Platform |
    | ---------------------------------- | --- | -------------- |
    | [coqc] on this file                | exit 0 | exit 0 |
    | [Print Assumptions escaped]        | Closed under the global context | same |
    | [Print Assumptions downstream_one_eq_two]     | Closed under the global context | same |
    | [rocqchk] on this [.vo], default   | exit 0, [Modules were successfully checked] | same |
    | [rocqchk -bytecode-compiler yes]   | exit 0 | exit 0 |
    | [rocqchk -o]: Axioms               | [<none>] | [<none>] |
    | [rocqchk -o]: type-in-type         | [<none>] | [<none>] |
    | [rocqchk -o]: unsafe (co)fixpoints | [<none>] | [<none>] |

    That is the difference from ../ModuleSystem/UniverseFlagDesync.v, where the
    inconsistency is written into the [.vo]'s universe graph and a [Require] of
    it is rejected at the [Require] line, and from
    ../ModuleSystem/GuardFlagThroughFunctor.v, where [rocqchk] refuses with
    [IllFormedRecBody].  Here the term is *well typed* — the kernel read the
    wrong recursive tree, so only its guardedness was decided wrongly — and
    there is nothing in the [.vo] for a consumer, or for the checker, to trip
    over.

    Together with the exhibit this establishes that rocq#22386 belongs in the
    same class as rocq#21839 (../GuardChecker/WrongEnvReduction.v): **both**
    audit channels this catalog uses to price a proof of [False] report nothing,
    **and** the [False] propagates through a plain [Require] into downstream
    code whose own audit is also clean.  Before 2026-08-20 that class had one
    member. *)

Require Import CofixWrongEnvRectree.

Definition escaped : False := contradiction.

(** [Closed under the global context] *)
Print Assumptions escaped.

Definition downstream_one_eq_two : 1 = 2 := match escaped return 1 = 2 with end.

(** [Closed under the global context] *)
Print Assumptions downstream_one_eq_two.
