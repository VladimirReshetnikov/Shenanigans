(** * rocq#21839 -- guard checker reduces in the wrong environment

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit code 0, with a clean audit.
    It is the second live exhibit in this directory, after
    ../ModuleSystem/UniverseFlagDesync.v.

    Category (per ../../README.md): IMPLEMENTATION DEFECT (live on the installed
    toolchain).  Closed [False], no flag, no axiom, and the audit reports
    nothing.

    CATALOG.md §4.1 lists rocq#21839 as **gap**, affected 8.16-9.2.0, fixed in
    9.2.1/9.3.  The installed toolchain is 9.2.**0** ([coq-core.9.2.0] in the
    opam switch), which is inside the affected range -- so unlike the other
    guard-checker files here, this one is not a regression witness.  It is a
    proof of [False] that the machine running verify.ps1 accepts today.

    ** The defect

    [subterm_specif] in [kernel/inductive.ml] must sometimes reduce a term to
    decide whether it is a structural subterm of the recursive argument.  It
    passed the **wrong environment** to that reduction, so the local [let]
    bindings visible at the reduction site were not the ones in scope at the
    term.  The inner fixpoint below is built by [ltac:(fix rec' 1; exact g)] and
    then cast to [unit -> unit]; when the guard checker reduces the application
    [(fix rec' ...) x] under the mistaken environment it concludes that the
    result is a subterm of [x], and the outer [rec] is accepted with a recursive
    call on a value that is not smaller.  [rec] therefore does not terminate,
    and its declared return type is [False].

    Upstream: <https://github.com/rocq-prover/rocq/issues/21839>
      "Incorrect environment passed to reduction during guard checking",
      fixed by <https://github.com/rocq-prover/rocq/pull/21845>, milestone 9.2.1.
      The issue text is a direct [Definition oops : False] -- no tactic, no
      paradox encoding, no library.

    ** Measured, on this machine

      The Rocq Prover 9.2 (coq-core 9.2.0, OCaml 4.14.2)
        coqc   this file          exit 0     Closed under the global context
        coqchk the .vo            exit 0     * Axioms: <none>
      The Rocq Prover 9.0.1 (Rocq Platform 9.0~2025.08)
        coqc   this file          exit 0     Closed under the global context
        coqchk the .vo            exit 0     * Axioms: <none>

    Both channels this repository uses to price a proof of [False] report
    nothing, on both installed toolchains.  Contrast ../ModuleSystem/
    UniverseFlagDesync.v, where [coqchk] does catch it -- there the
    inconsistency is written into the .vo's universe graph, and here there is
    nothing wrong with the *term*: it is well typed, and only its guardedness is
    a lie.  [coqchk] re-runs the same guard checker, so it inherits the same
    bug.  That makes this the more dangerous of the two shapes.

    A [Require] of the resulting .vo is likewise clean; the [False] escapes into
    downstream code, which the universe-flag desync does not do. *)

(** ** Control 1 -- delete the ltac-built inner fixpoint.

    Exactly the same term with [(ltac:(fix rec' 1; exact g) :> unit -> unit) x]
    replaced by [g x].  [g] is the same let-bound identity, so the two terms are
    convertible; only the syntactic shape the guard checker walks has changed.
    REFUSED:

      Recursive definition of rec is ill-formed.
      Recursive call to rec has principal argument equal to
      "g x" instead of "f". *)
Fail Definition control_no_inner_fix : False :=
  (fix rec (x : unit) : False :=
  let f (b : False) := match b with end in
  let g x := x in
  f (rec (g x))) tt.

(** ** Control 2 -- keep the inner fixpoint, feed it a constant.

    [(fix rec' ...) tt] instead of [(fix rec' ...) x].  Nothing else changes.
    REFUSED:

      Recursive definition of rec is ill-formed.
      Recursive call to rec has principal argument equal to
      "(fix rec' (H : unit) : unit := g H) tt" instead of "f". *)
Fail Definition control_constant_arg : False :=
  (fix rec (x : unit) : False :=
  let f (b : False) := match b with end in
  let g x := x in
  f (rec ((ltac:(fix rec' 1; exact g) :> unit -> unit) tt))) tt.

(** ** The exhibit.

    The difference from Control 1 is the interposed fixpoint; the difference
    from Control 2 is the single character [x] in place of [tt]. *)
Definition oops : False :=
  (fix rec (x : unit) : False :=
  let f (b : False) := match b with end in
  let g x := x in
  f (rec ((ltac:(fix rec' 1; exact g) :> unit -> unit) x))) tt.

(** [Closed under the global context] *)
Print Assumptions oops.

(** ** The bug does not depend on [g] being the identity.

    Upstream's reproducer uses [let g x := x].  Replacing it by the constant
    function [fun _ => tt] -- so that the inner fixpoint is not even extensionally
    the identity -- is accepted just the same.  Recorded because upstream's text
    and the fix's regression test name only the identity shape. *)
Definition oops_const : False :=
  (fix rec (x : unit) : False :=
  let f (b : False) := match b with end in
  let g (_ : unit) := tt in
  f (rec ((ltac:(fix rec' 1; exact g) :> unit -> unit) x))) tt.

Print Assumptions oops_const.

(** ** Everything follows, still with a clean audit. *)

Definition one_eq_two : 1 = 2 := match oops return 1 = 2 with end.
Print Assumptions one_eq_two.
