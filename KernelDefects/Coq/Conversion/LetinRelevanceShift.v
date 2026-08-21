(** * Two `SProp` local definitions in a constructor type make its `nat`
      arguments interchangeable

    rocq-prover/rocq#22378, "Incorrect conversion with letins in constructor
    type", opened 2026-08-20T12:47:24Z by `SkySkimmer`, **OPEN**, sole label
    `kind: inconsistency`.  The fix, PR
    <https://github.com/rocq-prover/rocq/pull/22379> -- "Prune context
    annotations to remove local defs when they are substituted" -- is **open and
    unmerged**, based on `master`, milestone 9.3.0.

    THIS FILE IS EXPECTED TO BE **ACCEPTED**: exit code 0, with a clean audit on
    every channel this repository measures.

    Category, per ../../README.md: **(a) a closed proof of `False` that the
    kernel accepts with the audit reporting nothing.**  No flag, no axiom, no
    `Definitional UIP`, no module system, no tactic beyond `eq_refl`, no library
    past `Init`, and no `Require` of anything -- fifteen lines of ordinary
    source.  This is an implementation defect, and it is **live on both
    installed toolchains**.

    ** Provenance

    The issue body names its source, and the naming is why this file exists
    rather than a link:

      "Reported by OpenAI by email to a random core team member (not me).  For
      anyone reading this, please directly open issues instead of emailing
      random people."

    Nine `kind: inconsistency` issues were filed against Rocq in fifty-five
    minutes on 2026-08-20; this is the first of them.

    ** Mechanism -- upstream's words, not this repository's

    The issue quotes the reporter's own diagnosis under the heading "The AI
    said":

      "The constructor has two real `nat` arguments followed by two local
      definitions whose type lies in `SProp`.  In `kernel/conversion.ml`,
      `convert_under_context` uses `esubst_of_context` to substitute away those
      local definitions.  It therefore lifts the conversion context by two
      surviving arguments.  But it pushes the relevance annotations of all four
      original binders.  Consequently, the two remaining `nat` variables are
      looked up at positions marked irrelevant.

      The kernel then accepts `left p = right p` using `eq_refl`.  Instantiating
      `p` with `pack 0 1` gives `0 = 1`, from which an ordinary dependent match
      constructs `False`."

    That paragraph is a claim about OCaml source.  **This repository has not read
    `kernel/conversion.ml`** -- no Rocq sources are installed on this machine --
    and asserts nothing about its text.  Every claim below is behavioural and was
    run.

    ** The law, measured

    Write `n` for the number of real arguments a constructor takes and `k` for
    the number of trailing local definitions whose type lies in `SProp`.  Two
    branch bodies that project the `i`-th and the `j`-th real argument out of a
    *stuck* match are accepted as convertible **exactly when both `i` and `j`
    lie in the innermost `k`** -- when both arguments sit at a de Bruijn slot
    that the shifted relevance array marks irrelevant.  Measured, in
    LetinRelevanceShiftControls.v:

      - `n = 2, k = 1` -- refused.  One local definition is not enough.
      - `n = 2, k = 2` -- accepted.  This file, section 1.
      - `n = 3, k = 2` -- the *inner* pair is accepted and the *outer* pair is
        refused, in one file, one binder position apart.  That is the sharpest
        statement of the window, and upstream's report does not contain it.
      - `n = 3, k = 3` -- all three arguments collapse together, so one
        `eq_refl` per pair yields `0 = 1`, `1 = 2` **and** `0 = 2`, all three of
        them stated in section 2 below.

    Both sides must be inside the window: projecting an argument in the window
    against the literal `0` is refused, which is what distinguishes "these
    positions are read as irrelevant" from "these indices are misaligned".

    ** Audit surface, measured

      The Rocq Prover 9.2 (OCaml 4.14.2), current stable release
        coqc on this file                     exit 0
        Print Assumptions contradiction       Closed under the global context
        Print Assumptions zero_eq_two         Closed under the global context
        rocqchk (default)                     exit 0, Modules were successfully
                                              checked
        rocqchk -bytecode-compiler yes        exit 0, Modules were successfully
                                              checked
        rocqchk -o                            * Axioms: <none>
                                              * ... type-in-type: <none>
                                              * ... unsafe (co)fixpoints: <none>
        plain Require downstream              exit 0, clean -- see
                                              LetinRelevanceShiftEscape.v
      The Rocq Prover 9.0.1 (Rocq Platform 9.0~2025.08)
        coqc on this file                     exit 0
        Print Assumptions                     Closed under the global context
        coqchk (default)                      exit 0, Modules were successfully
                                              checked
        coqchk -bytecode-compiler yes         exit 0, Modules were successfully
                                              checked

    Nothing reports anything, anywhere, on either release.  That places this with
    ../GuardChecker/WrongEnvReduction.v (rocq#21839) rather than with
    ../ModuleSystem/UniverseFlagDesync.v (rocq#22287), where `coqchk` does catch
    it: there is nothing wrong with the stored *term*, so there is nothing for a
    second reader to trip over.  Same shape, different subsystem.

    ** The one channel that disagrees is inside `coqc`

    `exact_no_check` sends the cast to the lazy machine and it is accepted.
    `vm_cast_no_check` sends the identical cast to the VM and it is **refused**,
    with the kernel's own type-mismatch message, quoted verbatim there.  (Naming
    the OCaml exception behind that message would be an inspection claim, and
    none is made here: what was measured is the printed text.)  Two conversion
    machines in one kernel, one file, one term, opposite verdicts -- and the VM
    is the one that is right.  That is control 11 of
    LetinRelevanceShiftControls.v, and it is the exact mirror image of
    RegisterInlineVM.v (rocq#21736), the other artifact in CATALOG.md section
    4.4, where the VM was the machine that was wrong and the lazy one that was
    right.

    The disagreement does **not** reach `rocqchk -bytecode-compiler yes`: that
    flag governs how the checker reduces, not which machine decides this
    conversion, and the checker accepts in both modes.  Measured, not inferred.

    The native lane is not measured.  The native compiler is disabled in this
    switch, so `native_compute` silently falls back to the VM and a
    `native_cast_no_check` verdict here would be a VM verdict wearing another
    name. *)

(** ** 1. The construction, as upstream states it

    Reproduced from the issue body with its own identifiers.  `left` and `right`
    shadow the constructors of `sumbool`; that is upstream's choice and it is
    kept so that this file and the issue can be diffed line for line. *)

Inductive sUnit : SProp := stt.

Inductive pair_with_lets : Type :=
| pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).

Definition left (p : pair_with_lets) : nat :=
  match p with pack x y ghost1 ghost2 => x end.

Definition right (p : pair_with_lets) : nat :=
  match p with pack x y ghost1 ghost2 => y end.

(** The scrutinee is the bound variable `p`, so the match is stuck and the two
    branch bodies are compared under the constructor's context.  That single
    line is the defect; everything after it is bookkeeping. *)

Definition collision (p : pair_with_lets) : left p = right p := eq_refl.

Definition zero_eq_one : O = S O := collision (pack O (S O)).

Definition contradiction : False :=
  match zero_eq_one in (_ = n)
    return (match n with O => True | S _ => False end)
  with
  | eq_refl => I
  end.

(** Expected: `Closed under the global context`. *)
Print Assumptions contradiction.

(** ** 2. Sharpened -- three arguments collapse at once

    Upstream's numbers are `0` and `1`.  With a third real argument and a third
    `SProp` local definition the window covers all three, so one `eq_refl`
    identifies every projection with every other, and the reachable equations
    include `0 = 2` -- which no instantiation of section 1 gives, because
    section 1's constructor holds only two numbers. *)

Inductive triple_with_lets : Type :=
| pack3 (x y z : nat) (g1 : sUnit := stt) (g2 : sUnit := stt) (g3 : sUnit := stt).

Definition fst3 (t : triple_with_lets) : nat := match t with pack3 x y z => x end.
Definition snd3 (t : triple_with_lets) : nat := match t with pack3 x y z => y end.
Definition thd3 (t : triple_with_lets) : nat := match t with pack3 x y z => z end.

Definition collide12 (t : triple_with_lets) : fst3 t = snd3 t := eq_refl.
Definition collide13 (t : triple_with_lets) : fst3 t = thd3 t := eq_refl.
Definition collide23 (t : triple_with_lets) : snd3 t = thd3 t := eq_refl.

Definition witness : triple_with_lets := pack3 O (S O) (S (S O)).

Definition zero_eq_one' : O = S O       := collide12 witness.
Definition zero_eq_two  : O = S (S O)   := collide13 witness.
Definition one_eq_two   : S O = S (S O) := collide23 witness.

(** Expected: `Closed under the global context`. *)
Print Assumptions zero_eq_two.
