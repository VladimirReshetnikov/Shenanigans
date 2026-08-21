(** * Controls for UniformArgsLetBinder.v -- the same procedure refuses each twin

    rocq#22382.  THIS FILE IS EXPECTED TO BE **REJECTED**, exit code 1, at
    section 5.  That is the point of it.

    Acceptance of ./UniformArgsLetBinder.v means nothing unless a
    deliberately-reduced twin of each construction -- differing by the trigger
    and by nothing else -- is refused by the same [coqc] on the same toolchain.
    Five twins are below, and all five are refused, on Rocq 9.2 and on Rocq
    9.0.1 alike.

    ** Why the file is arranged this way

    [coqc] does not echo the message of a command wrapped in [Fail]; measured,
    on 9.2, with [-verbose] and without.  So sections 1-4 wrap their twins in
    [Fail], which machine-checks the *verdict* -- if any twin were accepted the
    [Fail] would raise "The command has not failed!" and this file would stop
    there with a different message -- and section 5 runs the primary twin again
    **unwrapped**, so the literal text reaches the transcript and a harness can
    assert on it.

    ** The trigger, isolated

    In each pair the exhibit and the twin denote the same function.  What is
    removed is the binder that is not an argument:

      exhibit section 1   fix inner (carry : nat := seed) (p m : nat) {struct m}
      twin section 1      fix inner (p m : nat) {struct m}, with [carry]
                          replaced by [seed] at its one use
                          -- one [let] binder, zeta-reduced by hand

      exhibit section 2   exact ((fun (carry p m : nat) => ...) seed)
      twin section 2      exact (fun (p m : nat) => ...), with [carry] replaced
                          by [seed] at its one use
                          -- one beta-redex, contracted by hand

      exhibit section 3   exact ((fun (p : nat) (q r : nat) => ... rec p r' ...) 1)
      twin section 3      exact (fun (q r : nat) => ... rec 1 r' ...)
                          -- the same redex, upstream's own, contracted by hand

    Section 2's twin runs the identical tactic script -- [fix inner 2] then
    [exact] -- so the refusal cannot be attributed to the use of a tactic to
    build the term.  Within that construction, it is attributable to the redex
    alone.

    ** The two twins of section 4, and why they are the sharpest ones here

    Section 4 is not a reduced twin.  It is the exhibit's own sections 2 and 3
    **as they print**, re-parsed as ordinary [fix] term syntax -- the redex kept,
    the tactic's eta-expansion written out by hand:

      exhibit section 2   ltac:(fix inner 2; exact ((fun carry p m => ...) seed))
                          stores, verbatim from [Print relay_beta],
                            fix inner (H H0 : nat) {struct H0} : Type :=
                              (fun carry p m : nat => ...) seed H H0
      twin section 4a     that same block, written as a [fix] term

      exhibit section 3   the same, for upstream's second reproducer
      twin section 4b     [fix rec (q r : nat) {struct r} := (fun p q r => ...) 1 q r]

    Both are REFUSED, on both toolchains.  The exhibits are accepted.  So the
    trigger of sections 2 and 3 is not "a beta-redex in the body" as such: it is
    a redex the checker does not treat as one, and only the term the [fix]
    tactic builds puts one there.  The refusals say as much in their own
    environments -- [carry := seed], [p0 := p], [m0 := m] for 4a, and
    [p := 1], [q0 := q], [r0 := r] for 4b, i.e. the checker contracted the redex
    into let-bindings and then answered correctly.  Section 1 uses no tactic and
    is untouched by this.

    What separates the two application nodes is invisible to [Print] and to
    [Set Printing All] (measured: the pair prints identically up to binder
    names), and nothing here claims to have measured what it is.

    ** The literal messages, measured on The Rocq Prover 9.2 (OCaml 4.14.2) and
       identical on 9.0.1 (Rocq Platform 9.0~2025.08), each from an unwrapped
       run, exit code 1

    Section 1 and section 2 (only the identifiers differ):

        Recursive definition of russell_zeta is ill-formed.
        In environment
        russell_zeta : nat -> Type
        n : nat
        smaller : nat
        seed := n : nat
        inner : nat -> nat -> Type
        p : nat
        m : nat
        Recursive call to russell_zeta has principal argument equal to
        "p" instead of one of the following variables: "smaller"
        "m".

    Section 3:

        Recursive definition of error_beta_reduced is ill-formed.
        In environment
        error_beta_reduced : nat -> nat
        n : nat
        n' : nat
        rec : nat -> nat -> nat
        q : nat
        r : nat
        Recursive call to error_beta_reduced has principal argument equal to
        "q" instead of "n'".

    (Written with upstream's [#[refine]] attribute instead, the same twin is
    refused by [Guarded] with the same last two lines, under the heading
    [As a fixpoint decreasing on the 1st argument of error_beta_reduced:].)

    Section 4a -- note the three let-bindings the checker introduced, which are
    the redex it contracted:

        Recursive definition of russell_beta_printed is ill-formed.
        In environment
        russell_beta_printed : nat -> Type
        n : nat
        smaller : nat
        seed := n : nat
        inner : nat -> nat -> Type
        p : nat
        m : nat
        carry := seed : nat
        p0 := p : nat
        m0 := m : nat
        Recursive call to russell_beta_printed has principal argument equal to
        "p0" instead of one of the following variables: "smaller"
        "m" "m0".

    Section 4b:

        Recursive definition of error_printed is ill-formed.
        In environment
        error_printed : nat -> nat
        n : nat
        n' : nat
        rec : nat -> nat -> nat
        q : nat
        r : nat
        p := 1 : nat
        q0 := q : nat
        r0 := r : nat
        Recursive call to error_printed has principal argument equal to
        "q0" instead of "n'".

    Read those against the defect: with the extra binder gone, the traversal's
    baseline is right, [p] is correctly found non-uniform, and the checker
    names [p] as the argument that is not a subterm of [smaller].  With the
    binder present the very same checker says nothing at all. *)

(** ** 1.  The [let] binder, zeta-reduced by hand *)

Definition relay_zeta (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner seed rest
    end.

Fail Fixpoint russell_zeta (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay_zeta russell_zeta n smaller smaller
  end.

(** ** 2.  The hidden beta-redex, contracted by hand

    Same tactic script as section 2 of the exhibit, one redex shorter. *)

Definition relay_beta_reduced (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  ltac:(fix inner 2;
        exact (fun (p m : nat) =>
                  match m return Type with
                  | O => outer p -> False
                  | S rest => inner seed rest
                  end)).

Fail Fixpoint russell_beta_reduced (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay_beta_reduced russell_beta_reduced n smaller smaller
  end.

(** ** 3.  Upstream's second reproducer, contracted by hand

    [(fun (p : nat) (q r : nat) => ... rec p r' ...) 1] with [p] substituted
    away.  Written in the same attribute-free transcription as section 3 of the
    exhibit, so that this file runs on 9.0.1 too -- see there for why.
    Upstream's own [test-suite/bugs/bug_22382.v] checks the *uncontracted* term
    the same way, with [Fail Guarded.], against a fixed kernel; here the kernel
    is not fixed, and it is the contraction that makes the difference. *)

Fail Fixpoint error_beta_reduced (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      (ltac:(fix rec 2;
             exact (fun (q r : nat) =>
                      match r with 0 => 1 + error_beta_reduced q | S r' => rec 1 r' end))
       : nat -> nat -> nat) n' 1
  end.

(** ** 4.  The exhibit's own sections 2 and 3, as they print, re-parsed

    Nothing is reduced here.  4a is the term [Print relay_beta] displays for
    section 2 of the exhibit, transcribed into [fix] term syntax with the
    tactic's eta-expansion written out; 4b is the same for section 3, which is
    upstream's second reproducer.  The redex is still there in both.  Both are
    refused, and the exhibits are accepted, so the [fix] tactic is doing
    something to the application node that the parser does not do -- see the
    header. *)

(** *** 4a *)

Definition relay_beta_printed (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (p m : nat) {struct m} : Type :=
    (fun (carry p m : nat) =>
       match m return Type with
       | O => outer p -> False
       | S rest => inner carry rest
       end) seed p m.

Fail Fixpoint russell_beta_printed (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay_beta_printed russell_beta_printed n smaller smaller
  end.

(** *** 4b *)

Fail Fixpoint error_printed (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      (fix rec (q r : nat) {struct r} : nat :=
         (fun (p : nat) (q r : nat) =>
            match r with 0 => 1 + error_printed q | S r' => rec p r' end) 1 q r) n' 1
  end.

(** ** 5.  The primary twin again, unwrapped

    Section 1 with the [Fail] removed, so that the rejection is visible rather
    than merely counted.  **This is where the file stops, with exit code 1.** *)

Fixpoint russell_zeta (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay_zeta russell_zeta n smaller smaller
  end.

(** Unreachable. *)
