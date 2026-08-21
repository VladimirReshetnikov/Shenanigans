(** * The [False] escapes through a plain [Require], and the consumer's audit is clean too

    rocq#22352, second half.  This file does nothing but [Require Import Evil]
    and use what is there.  It contains no VMcast, no flag, and no reference to
    the spliced object file — its only relationship to the hand-editing is that one
    of its transitive dependencies was built against it.

    Measured on Rocq 9.2:

      - [rocq c Downstream.v]:               exit 0.
      - [Print Assumptions consequence]:     "Closed under the global context".
      - [Print Assumptions anything]:        "Closed under the global context".
      - [rocqchk -bytecode-compiler yes]:    "Modules were successfully checked".
      - [rocqchk] (default):                 [Fatal Error: Type error: ActualType],
                                             reported against [Evil.evil_false] —
                                             i.e. the consumer is rejected for
                                             something in its dependency, which is
                                             the correct behaviour.

    This is the property CATALOG.md §4.1 uses to rank rocq#21839 as the strongest
    route in the catalog: a closed [False], a clean [Print Assumptions], and an
    escape through a plain [Require] into a downstream file whose own audit is
    also clean.  This exhibit has all three — with one qualification that #21839
    does not have, and it is the whole difference between them: [rocqchk] in its
    DEFAULT mode catches this, and catches nothing in #21839.

    So the honest ranking is: #21839 remains the strongest, because no channel
    catches it.  This one is second, and is the only exhibit here where the two
    modes of the same tool disagree with each other. *)

Require Import Evil.

Definition consequence : False := boom.

Definition anything (P : Prop) : P := False_ind P consequence.
