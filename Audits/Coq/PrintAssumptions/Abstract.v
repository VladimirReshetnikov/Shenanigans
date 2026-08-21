(** * rocq#20550 — `abstract` side-effect constants lose the local typing flags

    Labelled `kind: inconsistency` upstream, closed 2026-04-24 with the fix on
    master / v9.3 / V9.3+rc1 only, so **live on 9.2.0**.  Absent from
    `dev/doc/critical-bugs.md` and, before this file, from CATALOG.md.

    `abstract` generates its side-effect constant with the GLOBAL typing flags
    rather than the declaration's local ones, so the flag record the declaration
    carries is not recorded on the constant that actually holds the proof.

    `bar` and `foo` state the same thing and are proved by the same tactic under
    the same disabled check.  The only difference is `abstract`. *)

Ltac the_tac := unshelve eexists;[exact_no_check Set | reflexivity].

Unset Universe Checking.
#[bypass_check(universes=no)] Lemma bar : exists T:Set, Set = T.
Proof. abstract the_tac. Qed.
Set Universe Checking.

(** Expected on 9.2.0: `Closed under the global context` — the defect. *)
Print Assumptions bar.

(** ** Control: the same lemma without `abstract`. *)

#[bypass_check(universes)] Lemma foo : exists T:Set, Set = T.
Proof. the_tac. Qed.

(** Expected: `foo relies on an unsafe hierarchy.` *)
Print Assumptions foo.

(** Worth stating and NOT overclaiming: `exists T:Set, Set = T` is refutable, so
    `bar` is an inconsistent statement carrying a clean audit.  That is one
    Set-level Hurkens instance away from a closed `False` with a clean audit —
    but `Stdlib.Logic.Hurkens.TypeNeqSmallType.paradox` is monomorphic at fixed
    universes and does not instantiate to `Set`, so that step is not built here
    and this file does not claim it. *)
