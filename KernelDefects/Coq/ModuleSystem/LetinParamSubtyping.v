(** * Module subtyping ignores let-in PARAMETERS, not just their order

    Category (see ../../README.md): kernel defect.  Closed [False], no flag, no
    axiom, [Print Assumptions] reports [Closed under the global context].

    Upstream: a comment by Gaëtan Gilbert (SkySkimmer) on
    https://github.com/rocq-prover/rocq/issues/22387, posted 2026-08-20:
    https://github.com/rocq-prover/rocq/issues/22387#issuecomment-5357992278
    The script below is his, verbatim, so this file can be diffed against the
    comment -- ground rule 7's first exception, the same treatment
    ../Checker/Evil.v gets.

    DISTINCT FROM [LetinOrderSubtyping.v], which is #22387's issue BODY.  That
    one is about the ORDER in which let-in fields are declared.  This one is
    about let-in **parameters** of the inductive (and constructor-argument
    defaults referring to them) not being compared at all: a functor compiled
    against a signature whose parameter is [n := 0] accepts an argument module
    whose parameter is [n := 1], and both [eq_refl]s typecheck.

    TWO THINGS MAKE IT WORTH ITS OWN FILE.

    (1) The reporter states it is NOT caught by the fix for #22387,
        https://github.com/rocq-prover/rocq/pull/22394, "at least in its current
        state 09dbcf35aece789d9cc66063a3124a44790057a8".  That PR was still OPEN
        when this file was written (2026-08-21).

    (2) [rocqchk] **catches this one**, and does not catch its sibling.  Measured
        here on 9.2.0:

          rocq c T.v          -> exit 0, Print Assumptions: Closed under the
                                 global context
          rocqchk -R . "" T   -> Fatal Error: Type error: ActualType, exit 129,
                                 while checking cst:T.A.getm_spec

        The sibling [LetinOrderSubtyping.v] is accepted by [rocqchk].  So this
        directory now holds two module-subtyping routes to [False] that differ
        precisely in whether the independent checker sees through them, which is
        the column ../../../CATALOG.md section 4.7 is a table of. *)

Module Type M. Inductive I (n := 0) := C (m:=n). End M.

Module F (X:M).
  Definition getm x := match x with X.C _ m => m end.
  Definition getm_spec : getm X.C = 0 := eq_refl.
End F.

Module MI. Inductive I (n:=1) := C (m:=n). End MI.

Module A := F MI.

Definition getm_spec2 : A.getm MI.C = 1 := eq_refl.

Lemma bad : False.
Proof.
  pose proof A.getm_spec.
  pose proof getm_spec2.
  discriminate.
Qed.

Print Assumptions bad.
