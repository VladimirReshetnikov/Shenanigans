(** * The guard checker refutes univalence: a transport is treated as a subterm

    rocq-prover/rocq#22024, filed 2026-05-13 by Yann Leray and **OPEN**.
    CATALOG.md §4.1 and §4.6 record it as a **gap** with no artifact, and give
    the affected version as 9.1.  This file is the artifact, and it establishes
    that **Rocq 9.2 is affected too**.

    Category (per ../../README.md): PARADOX.  The [False] is conditional, the
    cost is a hypothesis in the statement, and the audit is clean.  Ground rule 1
    is what decides it against KernelDefects/, and it decides it in as many words:
    "a False that needs an assumption is a paradox even if the assumption looks
    plausible."  There is no honest way to file this anywhere else -- KernelDefects/
    requires a *closed* False with a silent audit, and no closed False exists here;
    the closed variant carries two [Parameter]s and [Print Assumptions] duly names
    them, which would make it an EscapeHatches/ exhibit and would misdescribe it.

    ** Read this first: this file is unlike the rest of Paradoxes/

    Every other exhibit under Paradoxes/ states a permanent fact about type
    theory: the hypothesis really is contradictory, and no implementation will
    ever make [Hurkens.TypeNeqSmallType.paradox] go away.  This one is the
    opposite.  The hypothesis here is

        e  : Boxed = Boxed :> Type
        e1 : rew [fun T => T] e in nobox = bbox (wrap (box nobox))

    -- "there is a path from [Boxed] to itself whose transport sends [nobox] to
    [bbox (wrap (box nobox))]" -- and that is a *consequence of univalence*, not
    a contradiction.  The two named elements of [Boxed] are distinct, and the
    transposition swapping them is an equivalence; univalence turns it into such
    a path.  §5 below derives exactly that -- [swap], [swap_invol] and
    [swap_nontrivial] are the whole construction -- so the composite theorem is
    literally [Univalence -> False].

    Rocq + univalence is believed consistent (the simplicial model).  So the
    implication this file proves is **not** a theorem of type theory -- it is a
    defect, exhibited in the only shape a defect of this kind can take.  Which
    means the file's expected future state is REJECTION: when #22024 is fixed,
    [Fixpoint loop] in §2 stops being accepted and this file stops compiling.
    That failure is the intended signal, and ../verify.ps1 should be read
    accordingly -- it is the one case there whose flip to FAIL is good news.

    ** The mechanism

    The guard checker represents recursive-argument structure as *recursive
    trees* (rtrees).  A dependent [match] restricts how much of that structure
    may flow out of it, in [kernel/inductive.ml]'s [restrict_spec]; Yann Leray's
    summary is that "fixpoints on inductive with arguments may mess with these
    arguments rectree-wise while still being accepted", and Thomas Lamiaux
    localises the fault to [restrict_spec]'s [Ind] branch.  His pointer is
    lines 1190-1193 of rocq-prover/rocq@4a3c7952a6 (master, where the branch has
    been factored out as [Subterm.prune_path]); in the tree this file was
    measured against, tag [V9.2.0], the same branch is [kernel/inductive.ml]
    lines 1050-1059, inlined:

        | Ind i ->
          if has_constant_parameters env absctxlen (List.length arctx) i args
          then spec
          else begin match spec with
          | Dead_code -> spec
          | Subterm (l, st, tree) ->
            let recargs = get_recargs_approx cache ?evars env tree i args in
            let tree = inter_wf_paths tree recargs in
            Subterm (l, st, tree)
          | _ -> assert false
          end

    That attribution is a citation plus a re-pin, not a measurement.  What *is*
    measured here is the behaviour, in §3.

    Concretely: [rew [Box] e in y], which is [match e in _ = T return Box T with
    eq_refl => y end], keeps [y]'s subterm rtree.  §3's control shows this in one
    token -- [rew [Box] e in y] is accepted as a decreasing argument and
    [rew [Box] e in wrap y] is refused -- so the transport is not being ignored,
    it is being treated as *subterm-preserving*.  Since [e] is a path from
    [Boxed] to itself and not [eq_refl], it is nothing of the kind.

    ** Nothing contains it

    Measured on Rocq 9.2 against the closed variant of this file (the one in the
    issue, with [e] and [e1] as [Parameter]s -- not reproduced here, because
    ground rule 2 forbids a new axiom in Paradoxes/):

      - [coqc]:                 exit 0.
      - [Print Assumptions f]:  lists [e] and [e1], and nothing else.  Honest,
                                and useless: a reader who checks the audit sees
                                two consequences of univalence and concludes the
                                proof is fine.
      - [coqchk -o]:            exit 0, "Modules were successfully checked",
                                and in its own summary:
                                  * Constants/Inductives relying on unsafe
                                    (co)fixpoints: <none>
                                which is the independent checker positively
                                certifying the very thing that is false.
      - [Require Import] of it: accepted, [f : False] usable downstream.

    Contrast ../../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v, the
    other live Rocq exhibit here: there [coqchk] rejects the .vo and a [Require]
    of it is refused, so only the local audit is lost.  Here nothing is lost
    because nothing notices.  [coqchk] is not an independent checker of this:
    at [V9.2.0] there is no [checker/inductive.ml], and [checker/mod_checking.ml]
    checks a constant body by calling [Typeops.infer] -- the kernel's own
    typechecker, hence the kernel's own guard checker.  CATALOG §4.7's table
    gains a row from that: a .vo built with the guard checker *off* is at least
    listed by [coqchk], while a .vo built with the guard checker *on and wrong*
    is reported as clean.

    ** Triage hazard, worth stating plainly

    The reproducer in the body of issue #22024 is **REJECTED** by Rocq 9.2:

      Recursive definition of loop is ill-formed.
      In environment
      ... [17 lines of environment elided] ...
      Recursive call to loop has principal argument equal to
      "x2" instead of "n".

    Its author says so himself in the first comment ("I got a bit blinded by
    this success and didn't test on master").  Anyone triaging #22024 by pasting
    the issue body into 9.2 concludes it is fixed.  It is not; the working shape
    is the one in that comment, and it is what §2 reproduces.  The difference is
    that the host type must be *nested* -- see §3's third control, which is the
    issue-body shape rewritten against this file's [weird], and is refused for
    exactly that reason.

    ** Toolchain

    | Rocq     | [Fixpoint loop] (§2)   | Source                              |
    | -------- | ---------------------- | ----------------------------------- |
    | 9.2      | **accepted**, exit 0   | measured here, OCaml 4.14.2         |
    | 9.1      | accepted               | upstream report; not reproduced here|
    | master   | accepted               | upstream comment 2026-05-13; ditto  |

    Only 9.2 is installed, so the other two rows are cited, not measured.  The
    issue-body shape (§3, [loop_flat]) is measured rejected on 9.2 and reported
    accepted on 9.1, which is the only version-discriminating fact this machine
    can establish.
*)

Import EqNotations.

(** ** 1. Two inductives, the second nested in the first

    [Boxed] stores a [Box Boxed].  The nesting is load-bearing: it is what gives
    a [Box]-typed value a subterm rtree in the first place. *)

Inductive Box {A} := box (x : A) | wrap (y : Box).
Arguments Box : clear implicits.
Scheme All for Box.

Inductive Boxed := bbox (x : Box Boxed) | nobox.

(** ** 2. The two fixpoints the guard checker accepts

    [weird] walks a [Box A], transporting along [e] at every [wrap]. *)

Fixpoint weird {A B} (f : A -> B) (e : A = A :> Type) (x : Box A) {struct x} : B :=
  match x with
  | box x => f x
  | wrap y => weird f e (rew [Box] e in y)
  end.

(** [loop] recurses through [weird].  Its own recursive call is [loop e], handed
    to [weird] as a function argument; the checker admits it because [weird]'s
    rtree says [f] is applied to a subterm of the third argument, and the third
    argument is [n], a genuine subterm of [x].  What that rtree does not record
    is that the value [f] receives has been transported along [e] first. *)

Fixpoint loop (e : Boxed = Boxed :> Type) (x : Boxed) {struct x} : Boxed :=
  match x with
  | nobox => nobox
  | bbox n => bbox (box (weird (loop e) e n))
  end.

(** Two fixpoints are not actually required, despite the issue title.  Inlining
    [weird] as an anonymous [fix] inside [loop] is accepted identically, which
    locates the defect in the [match]-on-[eq] rather than in any handoff between
    two declarations. *)

Fixpoint loop_inlined (e : Boxed = Boxed :> Type) (x : Boxed) {struct x} : Boxed :=
  match x with
  | nobox => nobox
  | bbox n =>
      bbox (box ((fix rec (b : Box Boxed) {struct b} : Boxed :=
                    match b with
                    | box z => loop_inlined e z
                    | wrap y => rec (rew [Box] e in y)
                    end) n))
  end.

(** ** 3. Controls -- three deliberately-broken twins, all refused

    Ground rule 6: acceptance means nothing without a control.  Each of these
    differs from something accepted above by one token, and each is refused by
    the same [coqc] invocation that accepts §2.  [Fail] is silent in batch mode,
    so the assertion is carried by this file's exit code; the verbatim messages
    below were captured by compiling each one standalone.

    Control 1.  [rew [Box] e in y] is a legal decreasing argument (§2);
    [rew [Box] e in wrap y] is not.  So the transport is not skipped over -- it
    is treated as *preserving* the subterm rtree of its argument.  That single
    token is the whole defect.

      Recursive call to weird_control has principal argument equal to
      "rew [Box] e in wrap y" instead of "y". *)

Fail Fixpoint weird_control {A B} (f : A -> B) (e : A = A :> Type) (x : Box A)
  {struct x} : B :=
  match x with
  | box x => f x
  | wrap y => weird_control f e (rew [Box] e in wrap y)
  end.

(** Control 2.  [loop] is not simply trusting [weird] blindly: hand [weird] a
    non-subterm and the call is refused, and the message names the exact set of
    variables that would have been acceptable -- [n] among them, which is why §2
    passes.

      Recursive call to loop_control has principal argument equal to
      "x2" instead of one of the following variables: "n"
      "x1". *)

Fail Fixpoint loop_control (e : Boxed = Boxed :> Type) (x : Boxed)
  {struct x} : Boxed :=
  match x with
  | nobox => nobox
  | bbox n => bbox (box (weird (loop_control e) e (wrap n)))
  end.

(** Control 3.  The same shape at a NON-nested host.  This is the reproducer in
    the body of issue #22024, and it is the reason a 9.2 user reads that issue
    as fixed.  Without nesting there is no [Box]-typed subterm to pass, so the
    [Box] has to be constructed -- and then the checker does trace through the
    transport and does refuse.

      Recursive call to loop_flat has principal argument equal to
      "x2" instead of "n". *)

Fail Fixpoint loop_flat (e : nat = nat :> Type) (x : nat) {struct x} : nat :=
  match x with
  | O => 1
  | S n => S (weird (loop_flat e) e (wrap (box n)))
  end.

(** ** 4. The conditional [False]

    [loop] is not terminating: at [bbox (wrap (box nobox))] it transports its way
    back to its own argument.  Rocq accepted it anyway, so its equation holds,
    and the equation says a [Boxed] equals a proper subterm of itself. *)

Lemma loop_unrolls
  (e : Boxed = Boxed :> Type)
  (e1 : rew [fun T => T] e in nobox = bbox (wrap (box nobox))) :
  loop e (bbox (wrap (box nobox))) = bbox (box (loop e (bbox (wrap (box nobox))))).
Proof.
  unfold loop at 1.
  f_equal. f_equal.
  unfold weird.
  change (fix loop (e0 : Boxed = Boxed) (x : Boxed) := _) with loop.
  replace (rew [Box] e in box nobox) with (box (rew [fun T => T] e in nobox)).
  { rewrite e1. reflexivity. }
  clear e1. now destruct e.
Qed.

Theorem guard_vs_transport
  (e : Boxed = Boxed :> Type)
  (e1 : rew [fun T => T] e in nobox = bbox (wrap (box nobox))) : False.
Proof.
  assert (forall n, n <> bbox (box n)) as H.
  { induction n; try discriminate. destruct H; try discriminate. intros [=]. auto. }
  eapply H, loop_unrolls, e1.
Qed.

(** [Closed under the global context] -- no [sorry], no axiom, no flag. *)
Print Assumptions guard_vs_transport.

(** ** 5. Discharging the hypothesis from univalence

    §4's hypothesis is not something type theory withholds; univalence supplies
    it.  The weakest form needed is that a quasi-inverse pair yields a path whose
    transport *is* the function -- a direct consequence of
    [isequiv (idtoeqv : A = B -> A <~> B)]. *)

Definition Univalence_transport : Prop :=
  forall (A B : Type) (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) ->
    (forall b, f (g b) = b) ->
    exists p : A = B, forall a, rew [fun T => T] p in a = f a.

(** Sanity check, so that the hypothesis is not being refuted for a trivial
    reason: its identity instance is provable outright. *)

Lemma Univalence_transport_at_identity (A : Type) :
  exists p : A = A, forall a, rew [fun T => T] p in a = a.
Proof. exists eq_refl. reflexivity. Qed.

(** The equivalence used below is the transposition of [nobox] and
    [bbox (wrap (box nobox))]. *)

Definition swap (x : Boxed) : Boxed :=
  match x with
  | nobox => bbox (wrap (box nobox))
  | bbox (wrap (box nobox)) => nobox
  | y => y
  end.

Lemma swap_invol : forall x, swap (swap x) = x.
Proof.
  intros [b|]; [ | reflexivity ].
  destruct b as [z|w]; [ reflexivity | ].
  destruct w as [z|w']; [ | reflexivity ].
  destruct z as [b'|]; reflexivity.
Qed.

(** And it is not the identity -- otherwise §5 would be vacuous. *)

Lemma swap_nontrivial : swap nobox <> nobox.
Proof. discriminate. Qed.

(** The composite.  This is the sense in which #22024 is a *relative*
    inconsistency: the guard checker, as shipped in Rocq 9.2, refutes a
    principle that Rocq's own metatheory says is consistent with it. *)

Theorem univalence_refuted : Univalence_transport -> False.
Proof.
  intros ua.
  destruct (ua Boxed Boxed swap swap swap_invol swap_invol) as [p Hp].
  exact (guard_vs_transport p (Hp nobox)).
Qed.

(** [Closed under the global context] *)
Print Assumptions univalence_refuted.
