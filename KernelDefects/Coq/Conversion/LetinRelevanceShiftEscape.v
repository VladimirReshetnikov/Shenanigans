(** * The escape half of rocq#22378

    LetinRelevanceShift.v is accepted with a clean `Print Assumptions` AND a
    clean `rocqchk`, in both of the checker's bytecode modes, on both installed
    releases.  This file asks the question that decides how much that costs:
    does the `False` reach a consumer?

    **It does.**  This file is ordinary Rocq -- no flag, no `SProp`, no local
    definition in any constructor, no tactic -- that merely `Require`s the
    exhibit.  It is EXPECTED TO BE ACCEPTED, exit 0, and all three of its
    `Print Assumptions` lines report `Closed under the global context`.

    That is the same answer as ../GuardChecker/WrongEnvReductionEscape.v
    (rocq#21839) and the opposite of ../ModuleSystem/UniverseFlagDesyncImport.v
    (rocq#22287), where the `Require` itself is refused.  The distinction is
    what is wrong with the object file.  Under #22287 the inconsistency is
    written into the `.vo`'s universe graph, so a consumer re-checks it and
    trips.  Here every term in the `.vo` is well typed and every universe
    constraint in it is satisfiable; the only thing that was wrong happened
    inside a conversion test that finished, returned `true`, and left no trace.
    There is nothing for a consumer to trip over.

    Section 3 is the sharper half of the escape.  `collision` is exported as an
    ordinary lemma, so a downstream file can instantiate it at numbers the
    exhibit never mentions and get a fresh false equation without deriving it
    from `False` first.  The construction does not have to be re-run, and the
    consumer does not have to contain a single one of the features that make it
    work. *)

Require Import LetinRelevanceShift.

(** ** 1. The `False` itself crosses the module boundary. *)

Definition escaped : False := contradiction.

(** Expected: `Closed under the global context`. *)
Print Assumptions escaped.

(** ** 2. And so does everything downstream of it. *)

Definition derived_one_eq_two : 1 = 2 :=
  match escaped return 1 = 2 with end.

(** Expected: `Closed under the global context`. *)
Print Assumptions derived_one_eq_two.

(** ** 3. The consumer can also mint new false equations of its own.

    No `False` is used here.  `collision` is the exhibit's exported conversion
    lemma; applying it to a pair the exhibit never built gives `7 = 9` directly.
    This is why the exhibit is not self-contained: what escapes is not a single
    wrong constant but a general equality between the two projections of a type
    any consumer can now instantiate for itself. *)

Definition fresh_equation : 7 = 9 := collision (pack 7 9).

(** Expected: `Closed under the global context`. *)
Print Assumptions fresh_equation.
