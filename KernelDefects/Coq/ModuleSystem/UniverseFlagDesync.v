(** * Universe checking stays off after the module that turned it off closes

    rocq-prover/rocq#22287, reported 2026-07-16 and **OPEN**.  [ugraph] keeps a
    *copy* of the universe-checking flag, so [Local Unset Universe Checking]
    inside a [Module] leaves it desynced when the module closes.  Universe
    checking is then effectively off outside any flag scope, [Type] is an element
    of itself, and Hurkens' paradox goes through — with [Print Assumptions]
    reporting [Closed under the global context].

    CATALOG.md §4.2 and §4.6 record this as a **gap** with no artifact, and give
    the affected version as [master].  This file is the artifact, and it
    establishes that **Rocq 9.2 is affected too**.

    It is also the first exhibit in this directory that must be *accepted*.  The
    other three are fixed upstream and are kept as regression witnesses that must
    be rejected; this one is open, so acceptance is the finding.

    ** What is and is not contained

    Three separate things catch it, and one does not:

      - [coqc] on this file:            exit 0.  Not caught.
      - [Print Assumptions]:            "Closed under the global context".
                                        **Not caught** — the flag is not in scope
                                        where it looks, so there is nothing to
                                        report.
      - [coqchk] on the .vo:            [Fatal Error: Universe inconsistency].
      - [Require Import] of the .vo:    rejected at the [Require] itself, with
                                        [Universe inconsistency. Cannot enforce
                                        ... because ... < ... <= ...].

    So the inconsistency really is written into the .vo's universe graph, and
    both the independent checker and any consumer re-check it.  What the bug
    costs is the *local* audit: inside this file the signature is clean, and a CI
    that runs [coqc] and greps [Print Assumptions] passes.  Compare
    ../../../EscapeHatches/Coq/TypingFlags.v §3, where the same paradox is
    obtained honestly and [Print Assumptions] says
    [universe_false relies on an unsafe hierarchy].  The flag is the difference
    between a reported cost and an unreported one. *)

From Stdlib Require Import Hurkens.

(** ** Control 1 — with the flag genuinely on, the paradox is refused. *)

Definition Small0 : Type := Type.
Fail Definition control_false : False := TypeNeqSmallType.paradox Small0 eq_refl.

(** ** Control 2 — a module that does not touch the flag changes nothing. *)

Module Plain.
  Definition inside : Type := Type.
End Plain.

Definition Small1 : Type := Type.
Fail Definition after_plain_module : False := TypeNeqSmallType.paradox Small1 eq_refl.

(** ** The exhibit — [Local Unset Universe Checking] inside a module that closes.

    Note [Local]: the flag is scoped to [M], and [M] ends before the paradox is
    stated.  No flag is in scope below this point. *)

Module M.
  Local Unset Universe Checking.
  Definition inside : Type := Type.
End M.

Definition Small2 : Type := Type.
Definition desync_false : False := TypeNeqSmallType.paradox Small2 eq_refl.

(** [Closed under the global context]

    That is the whole finding.  The same declaration was refused twice above,
    and the only thing that changed is that a module which switched the flag off
    has been closed. *)
Print Assumptions desync_false.

(** ** Everything follows, still with a clean audit. *)

Definition one_eq_two : 1 = 2 := match desync_false with end.
Print Assumptions one_eq_two.
