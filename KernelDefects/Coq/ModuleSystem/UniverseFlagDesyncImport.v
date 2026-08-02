(** * The containment half of rocq-prover/rocq#22287

    [UniverseFlagDesync.v] compiles with exit 0 and a clean [Print Assumptions].
    This file asks the question that decides how bad that is: does the [False] it
    produced *escape* into a consumer?

    It does not.  The inconsistency is written into the .vo's universe graph, and
    a [Require] re-checks it, so this file is **rejected at the [Require] line**:

        Error: Universe inconsistency. Cannot enforce UniverseFlagDesync.NN =
        Hurkens.TypeNeqSmallType.Paradox.u0 because UniverseFlagDesync.NN <
        UniverseFlagDesync.MM <= Hurkens.TypeNeqSmallType.Paradox.u0.

    That is the important difference from this repository's Lean module-boundary
    exhibit (../../Lean/ModuleSystem/), where the [False] does reach ordinary
    downstream code with a clean audit of its own.  Here the damage is confined
    to the file that caused it — which is precisely why the finding is that the
    *local* audit lies, not that a library can be poisoned.

    Expected: **rejected**, at the [Require Import] itself.

    Requires [UniverseFlagDesync.vo] to have been built first; ../verify.ps1
    orders the two cases so that it has. *)

Require Import UniverseFlagDesync.

(** Unreachable: the [Require] above already failed. *)
Definition imported : False := desync_false.
Print Assumptions imported.
