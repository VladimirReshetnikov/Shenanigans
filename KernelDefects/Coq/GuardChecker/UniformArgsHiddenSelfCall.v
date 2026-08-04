(** * rocq#21797 -- guard checker: a self-call hidden inside a non-fix application

    THIS FILE IS EXPECTED TO BE REJECTED.  It is a regression witness, not a
    build target.  On an affected Rocq it compiles and yields an axiom-free
    [False]; on a fixed one the guard checker rejects [F2].

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    The defect: [find_uniform_parameters] computes which of a fixpoint's
    arguments stay constant across recursive calls, and it did not recurse into
    the *arguments* of an application whose head is a plain [Rel] rather than a
    [fix].  Here the recursive call to [F2] sits inside the body of an inner
    [fix G], and [G] is applied to [n'] -- so the self-call is reachable but the
    uniform-parameter analysis never looked where it was.  [F2] is then accepted
    with [a] taken as uniform, and [F2 2] reduces to [S (F2 2)].

    This is the third of the four proofs of [False] that PR #17986 introduced by
    itself, and the third failure of the *same* analysis -- uniform arguments for
    nested mutual fixpoints -- reached a third way.  Its two siblings are already
    here: ./NestedMutualCrossCall.v (#21682, cross-calls) and ./UniformArgsLet.v
    (#21701, let-bound aliases).  Reading the three together is the point of
    keeping all of them: the bug is one analysis, not three.

    Upstream: <https://github.com/rocq-prover/rocq/issues/21797>
      affected 8.20-9.1, fixed in 9.2.0.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2):

      REJECTED at [F2], exit code 1, with

        Recursive definition of F2 is ill-formed.
        Recursive call to F2 has principal argument equal to
        "a" instead of one of the following variables: "n'" "m".

    The message names [a] -- the argument the analysis wrongly believed uniform
    -- which is why it is the needle ../verify.ps1 asserts. *)

Fixpoint F2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    (fix G (a : nat) (f : nat -> nat -> nat) (m : nat) {struct m} : nat :=
      match m with
      | 0 => S (F2 a)
      | S m' => f (G n f m') m'
      end) n' (fun x _ => x) n'
  end.

Lemma F2_loop : F2 2 = S (F2 2).
Proof.
remember 0 as n.
set (v := F2 (S (S n))) at 2.
remember v as ans; unfold v in *; clearbody v.
cbn.
set (n0 := n) at 3.
replace n0 with 0.
f_equal.
now symmetry.
Qed.

Lemma no_fixpoint_succ : forall n : nat, n <> S n.
Proof.
  induction n; discriminate + (intro H; apply IHn; now injection H).
Qed.

Theorem inconsistency : False.
Proof.
  exact (no_fixpoint_succ _ F2_loop).
Qed.

Print Assumptions inconsistency.
