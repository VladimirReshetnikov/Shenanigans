(** * rocq#22382 -- the uniform-argument finder counts binders that are not arguments

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit code 0, with a clean audit.
    It is the fifth defect of PR #17986's uniform-argument analysis -- the
    fourth with an artifact here, after ./NestedMutualCrossCall.v (#21682),
    ./UniformArgsLet.v (#21701) and ./UniformArgsHiddenSelfCall.v (#21797); the
    remaining one, #22021, has no known route to a [False] and is a gap in
    CATALOG.md 4.1 -- and it is the second exhibit in this directory that is
    LIVE on the installed toolchain, after ./WrongEnvReduction.v (rocq#21839).

    Category (per ../../README.md): IMPLEMENTATION DEFECT, live.  Closed
    [False], no flag, no axiom, no [Set] and no [Unset], and every audit channel
    reports nothing -- including [rocqchk].

    Upstream: <https://github.com/rocq-prover/rocq/issues/22382>
      "Guard checker uniform arguments finder doesn't count the right
      arguments", filed 2026-08-20T13:04:18Z by yannl35133, labels
      [kind: inconsistency] and [part: fixpoints], **OPEN**.  Its body reads
      "Found by an LLM and @dselsam ; feel free to open these issues directly."
      and states the defect in one line: "find_uniform_parameters starts
      counting arguments at the first binders, irrespective of whether these
      binder really are lambdas."  Fix PR
      <https://github.com/rocq-prover/rocq/pull/22384>, "Only count uniform
      arguments that correponds to lambdas" (sic), opened nine minutes later and
      **open and unmerged**; base branch master.

    ** The mechanism, and the exact line

    [find_uniform_parameters] decides how many leading arguments of a nested
    fixpoint are passed through unchanged by every recursive call.  Uniform
    arguments keep the subterm spec they had in the enclosing context, so a
    wrong answer here lets a growing argument inherit a decreasing one's status.

    Its correctness rests on one de Bruijn invariant: **the first [k] binders
    traversed downwards from the top of a body are exactly the fixpoint's
    arguments, in order.**  That is what makes the parameter test

        | Rel m when Int.equal m (k - j) ->
          (* a reference to the j-th parameter *)

    ([kernel/inductive.ml] line 1305 at V9.2.0) mean what its comment says, and
    what makes the recursive-reference test [if n > k && n <= k + nbodies]
    (line 1301) find the mutual names.  The traversal is started at

        Array.fold_left_i (fun i -> aux i 0) min_indx bodies      (line 1316)

    -- baseline zero -- and descends with [fold_constr_with_binders succ]
    (line 1314), which increments the depth for *every* binder it passes under.
    A [LetIn] is a binder.  The head of a beta-redex is a binder.  Neither is an
    argument of the fixpoint.  So if a body does not begin with exactly the
    right number of literal [Lambda] nodes, every index inside it is read one or
    more binders off, and the analysis answers a question about the wrong
    variables.

    PR #22384 changes exactly that: it hands [find_uniform_parameters] the
    environment, peels the argument prefix with a [whd_all]-based
    [whd_decompose_lambda_n_assum] -- which reduces lets and beta-redexes away --
    and starts the fold at [List.length ctx] instead of [0], so that, in its
    author's words, "the first binders in the environment really correspond to
    the arguments of the fixpoint (instead of let-ins or hidden beta-redexes)".

    ** How this differs from rocq#21701, its nearest neighbour

    Both say "let" and "find_uniform_parameters", and they are not the same
    defect.  Two pieces of evidence: they sit in different halves of the same
    function, and the 9.2.0 kernel -- which carries #21701's fix -- accepts this
    file.

      - **#21701** (./UniformArgsLet.v) is a [let]-bound *alias for the
        recursive function*, inside the fixpoint's **body**:
        [let h := g in h (S p) m'].  The recursive reference then appears in
        [Rel] position with an *empty* argument list, and V9.1.0's

            List.fold_left_i (fun j nuniformparams a -> ...
              min j nuniformparams) 0 nuniformparams l

        ([kernel/inductive.ml] V9.1.0 lines 1258-1265) folded over that empty
        list and returned [nuniformparams] unchanged, so an argument-less call
        restricted nothing.  PR #21684 (merged 2026-03-04, closing #21682,
        #21683 and #21701) replaced the fold with
        [List.fold_left_until ... Stop j] (V9.2.0 lines 1302-1311), which
        returns [0] on the empty list.  The [let] is in the BODY, the repair is
        in the RESULT of the argument scan, and the *count* of binders was never
        in question.

      - **#22382** is a [let] in the fixpoint's **binder prefix**:
        [fix inner (carry : nat := seed) (p m : nat) {struct m}].  Nothing is
        aliased and no call is argument-less -- [inner carry rest] carries both
        its arguments.  What moves is the **de Bruijn baseline**: the body is
        [let carry := seed in fun p m => ...], the traversal counts [carry] as
        argument 0, and [p] and [m] shift to 1 and 2.  At the call site the
        checker matches the argument [carry] against the slot it believes holds
        argument 0, and reports one uniform parameter where the true answer is
        zero -- [inner carry rest] is [inner (p := carry) (m := rest)], and [p]
        does not survive the call.  The line at fault is 1316, the baseline;
        #21701's was 1258-1265, the scan.  #21684 did not touch line 1316, and
        neither did any of the other three fixes -- section 5 below.

    ** Measured, on this machine

      The Rocq Prover 9.2 (OCaml 4.14.2), the installed stable release
        coqc   this file                exit 0   Closed under the global context
                                                 on all four audited constants
        rocqchk (default)               exit 0   Modules were successfully checked
        rocqchk -bytecode-compiler yes  exit 0   Modules were successfully checked
        rocqchk -o                      * Axioms: <none>
                                        * ... type-in-type: <none>
                                        * ... unsafe (co)fixpoints: <none>
        plain Require downstream        exit 0, three clean audits
                                        (./UniformArgsLetBinderRequire.v)
      The Rocq Prover 9.0.1 (Rocq Platform 9.0~2025.08)
        coqc   this file                exit 0   Closed under the global context
                                                 on all four audited constants
        coqchk (default)                exit 0   Modules were successfully checked
        coqchk -bytecode-compiler yes   exit 0   Modules were successfully checked
        coqchk -o                       * Axioms: <none>
                                        * ... type-in-type: <none>
                                        * ... unsafe (co)fixpoints: <none>
        plain Require downstream        exit 0, three clean audits

    Section 3 of this file is a transcription rather than upstream's exact text,
    and section 3 says why: 9.0.1's parser refuses the [#[refine]] attribute on
    [Fixpoint].  Sections 1 and 2 are unaffected and compile on both releases
    exactly as written.

    **Affected range**: 8.20 to master, by inspection -- the line at fault
    (section 5) is byte-identical from V8.20.0 through V9.3+rc1, and PR #22384,
    the first change to it, is unmerged.  9.2 and 9.0.1 are the two points on
    that range that were *run*; the rest is reading the released sources, and is
    marked as such.

    So this is the ./WrongEnvReduction.v shape and not the
    ../ModuleSystem/UniverseFlagDesync.v shape: the terms are well typed, only
    their guardedness was decided wrongly, and there is nothing in the .vo for
    an independent checker or for a consumer to trip over.  [rocqchk] re-runs
    the kernel's own guard checker, so it inherits the same answer.

    ** The controls

    ./UniformArgsLetBinderControls.v is EXPECTED TO BE REJECTED and carries the
    deliberately-reduced twin of each construction below, plus a fourth and a
    fifth: what section 2 and section 3 *print*, re-parsed as ordinary term
    syntax.  Each twin differs from its exhibit by the trigger and by nothing
    else, and the same [coqc] refuses all five, on both toolchains, with the
    literal messages quoted there.  The last two are the ones that say how fine
    the trigger of section 2 is -- see section 2 below.

    ** Provenance of the pieces

    Section 1 is upstream's first reproducer, verbatim.  Section 3 is upstream's
    second reproducer, transcribed to drop an attribute 9.0.1 cannot parse and
    otherwise unchanged; upstream leaves that one at [Fail Guarded.] and
    [Abort.] in [test-suite/bugs/bug_22382.v] and does not carry it to a
    [False].  Section 2 is this repository's contribution: it transplants the
    second reproducer's trigger -- a hidden beta-redex where the argument prefix
    should be -- into the first reproducer's Russell shape, and closes it.
    Section 3 records, measured, what blocks the direct route.

    Section 1 is the load-bearing one.  It is plain term syntax, it uses no
    tactic, and its twin is refused for the reason the issue gives.  Sections 2
    and 3 are built with the [fix] tactic, and section 2 records what was
    measured about how much that matters. *)

(** ** 1.  The [let] in the binder prefix -- upstream's first reproducer

    [relay] is accepted on its own and is not the defect.  The wrong decision is
    taken while checking [russell], where [relay] unfolds and the guard checker
    meets

        fix inner := let carry := seed in fun p m => ...

    applied to [smaller smaller].  [p] is reported uniform.  It is not: the
    recursive call passes [carry], which is [seed], which is [n]. *)

Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (carry : nat := seed) (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner carry rest
    end.

Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay russell n smaller smaller
  end.

(** [russell 2] is now convertible to [russell 2 -> False]: Russell's paradox,
    with the kernel supplying the fixed point. *)

Definition diagonal (x : russell 2) : False := x x.
Definition contradiction : False := diagonal diagonal.

(** [Closed under the global context] *)
Print Assumptions contradiction.

(** ** 2.  The same defect reached through a hidden beta-redex

    Same skeleton, with the [let] binder replaced by the other way of putting a
    binder where an argument should be.  What gets stored is this -- measured,
    [Print relay_beta] on the compiled file, verbatim:

        fix inner (H H0 : nat) {struct H0} : Type :=
          (fun carry p m : nat =>
           match m with
           | 0 => outer p -> False
           | S rest => inner carry rest
           end) seed H H0

    [inner] has two binders, and the first three binders the traversal meets on
    its way down into that body are [carry], [p] and [m] -- one more than there
    are arguments, and the first of them is not an argument at all.  A [fix]
    *term* cannot be written this way directly, because term syntax requires the
    body to have the fix's return type rather than to be a function of the
    remaining arguments, so the term is built with the [fix] tactic -- as
    upstream's own second reproducer is.  Nothing is switched off by that: the
    completed term is guard-checked at [Defined] like any other, and section 2
    of ./UniformArgsLetBinderControls.v runs the same tactic script on the twin
    with the redex contracted and is refused.

    ** The tactic is load-bearing, and [Print] is not a faithful transcription

    This is measured, and it sharpens what section 2's trigger actually is.
    Take the block printed above, re-parse it as ordinary [fix] term syntax --
    same binders, same redex, same recursive call, only the eta-expansion now
    written out by hand -- and the same [coqc] REFUSES it, on 9.2 and on 9.0.1.
    Upstream's own second reproducer, transcribed to term syntax the same way,
    is refused too.  Both refusals carry the same tell: the environment in the
    message shows [carry := seed], [p0 := p], [m0 := m] (and [p := 1],
    [q0 := q], [r0 := r] for upstream's), i.e. the checker contracted the redex
    into let-bindings and then answered correctly.  On the term the tactic
    builds it does not.  Section 4 of ./UniformArgsLetBinderControls.v ships
    both twins with their literal messages.

    So the trigger here is finer than "a beta-redex in the body": it is a redex
    the checker does not recognise as one, and the [fix] tactic is what puts one
    there.  The two terms print identically under [Print] and under
    [Set Printing All], up to binder names (measured), so whatever separates
    them is invisible at that level; this file does not claim to have measured
    what it is, and section 5 does not rest on it.  Section 1 -- plain term
    syntax, no tactic anywhere -- is unaffected by all of this and is the
    construction to read first. *)

Definition relay_beta (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  ltac:(fix inner 2;
        exact ((fun (carry p m : nat) =>
                  match m return Type with
                  | O => outer p -> False
                  | S rest => inner carry rest
                  end) seed)).

Fixpoint russell_beta (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay_beta russell_beta n smaller smaller
  end.

Definition diagonal_beta (x : russell_beta 2) : False := x x.
Definition contradiction_beta : False := diagonal_beta diagonal_beta.

(** [Closed under the global context] *)
Print Assumptions contradiction_beta.

(** ** 3.  Upstream's second reproducer

    The redex is [(fun (p : nat) (q r : nat) => ...) 1] and the fixpoint [rec]
    has two arguments, so again three lambdas for two slots.  [error] is
    accepted, and [Print Assumptions] reports nothing about a [nat -> nat] whose
    recursion does not terminate: [error 1] reduces to [1 + error 1].

    **The transcription, and why.**  Upstream writes this one as

        #[refine]
        Fixpoint error (n : nat) : nat :=
          match n with 0 => 0 | S n' => _ n' 1 end.
        Proof.
          fix rec 2.
          exact ((fun (p : nat) (q r : nat) =>
                    match r with 0 => 1 + error q | S r' => rec p r' end) 1).
        Defined.

    That form is accepted on 9.2 with the same clean [Print Assumptions]
    (measured), but Rocq 9.0.1 refuses it before the kernel ever sees it:
    [Error: This command does not support this attribute: refine.] -- a parser
    limitation of that release, not a guard verdict.  So what ships below is the
    attribute-free transcription: the same tactic script under [ltac:], with a
    type ascription in place of the hole.  The ascription survives as a [Cast]
    node, which is the only difference between the two terms; both are accepted
    on 9.2 and the transcription is accepted on 9.0.1 as well.

    Upstream stops at this reproducer -- [test-suite/bugs/bug_22382.v] ends it
    with [Fail Guarded.] and [Abort.] and does not derive anything from it.
    **Measured here, and this is why the direct route stops too**: the cycle
    [error 1 = S (error 1)] holds but is not reachable by conversion.  Every
    route tried aborts with [Error: Stack overflow.] on 9.2 --

        Definition L : error 1 = S (error 1) := eq_refl.        (elaboration)
        Lemma L : ... Proof. apply eq_refl. Qed.                (elaboration)
        Lemma L : ... Proof. exact_no_check (@eq_refl nat (error 1)). Qed.
                                                               (the kernel, at Qed)
        Eval cbn in (error 1).                                  (reduction)

    -- the unfolding of [error] on one side and the folded constant on the other
    never meet syntactically, and both sides regenerate the cycle at every step.
    Section 2 is the answer to that: the same trigger at the level of *types*,
    where the fixed point is reached in one step and no numeric cycle has to be
    traversed. *)

Fixpoint error (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      (ltac:(fix rec 2;
             exact ((fun (p : nat) (q r : nat) =>
                       match r with 0 => 1 + error q | S r' => rec p r' end) 1))
       : nat -> nat -> nat) n' 1
  end.

(** [Closed under the global context] -- for a [nat -> nat] that does not
    terminate on any positive input. *)
Print Assumptions error.

(** ** 4.  What a closed [False] is worth downstream *)

Definition one_eq_two : 1 = 2 := match contradiction return 1 = 2 with end.

(** [Closed under the global context] *)
Print Assumptions one_eq_two.

(** ** 5.  A fifth INDEPENDENT defect of PR #17986, not a regression

    CATALOG.md 4.1 records that PR #17986 introduced four guard-checker defects
    by itself (#21682, #21701, #21797, #22021), and that the *fix* for #20555
    introduced #21683 -- so the question has to be asked of any fifth.
    **This one is independent, and the evidence is that the line at fault has
    never been edited.**

    [find_uniform_parameters] does not exist at V8.19.0 (checked: no occurrence
    in [kernel/inductive.ml]).  PR #17986, "Extrude uniform parameters of inner
    fixpoints in guard condition check (grant #16040)", merged 2024-05-07 by
    herbelin, adds the function and, in the same hunk, the line

        Array.fold_left_i (fun i -> aux i 0) min_indx bodies

    That line then reads byte-for-byte identically at V8.20.0 (line 1153),
    V9.0.1 (1227), V9.1.0 (1270) and V9.2.0 (1316), and at V9.3+rc1 it reads
    [Array.fold_left (aux 0) min_indx bodies] (line 1425) -- the unused body
    index [i] was dropped, the baseline [0] was not.  PR #21684, the single PR
    that closed #21682, #21683 and #21701, rewrites the [Rel] branch and
    [filter_fix_stack_domain] and leaves the baseline alone; the #21797 fix adds
    the [List.fold_left fold nuniformparams l] recursion into the arguments of a
    [Rel] application (V9.2.0 lines 1298-1299) and leaves the baseline alone.
    PR #22384 is the first change to it in two years and three months.

    (Those five line numbers are inspection of the released sources, not
    execution.  Everything under "Measured" above was run.  Two of the five were
    re-checked against sources present on this machine -- the opam switch keeps
    [rocq-core.9.2.0] and [rocq-core.9.1.1] under [.opam-switch/sources] -- and
    both match exactly: [kernel/inductive.ml] line 1316 at 9.2.0 and line 1270
    at 9.1.1 are the same [Array.fold_left_i (fun i -> aux i 0) min_indx bodies],
    the [Rel] branch runs 1297-1313 at 9.2.0 with the parameter test at 1305 and
    the [List.fold_left fold nuniformparams l] recursion at 1298-1299, and
    9.1.1's pre-#21684 [List.fold_left_i ... min j nuniformparams] sits at
    1258-1265.  8.20.0, 9.0.1 and 9.3+rc1 have no sources on this machine and
    remain reading only, as does the absence of the function at V8.19.0.)

    So the entry for CATALOG.md 4.1 is: **a fifth independent defect of PR
    #17986's uniform-argument analysis, latent since 2024-05-07 and live on
    every release that carries the analysis** -- not a regression in the shape
    of #21683.  Reading it beside ./NestedMutualCrossCall.v (#21682,
    cross-calls), ./UniformArgsLet.v (#21701, argument-less calls) and
    ./UniformArgsHiddenSelfCall.v (#21797, calls under a non-[fix] head) is the
    reason for keeping all four: those three are about *where the traversal
    looks*, and this one is about *where it starts*. *)
