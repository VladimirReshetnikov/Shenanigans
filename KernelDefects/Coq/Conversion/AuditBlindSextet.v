(** * Six new peers for rocq#21839 — the falsification of CATALOG.md §4.1

    ** What this file is for

    `CATALOG.md` §4.1 says of rocq#21839 that it is

      "the strongest route in this catalog: the only one where **both**
       `Print Assumptions` *and* `coqchk` report nothing **and** the `False`
       escapes through a plain `Require` into a downstream file whose own audit
       and `coqchk` are also clean."

    `README.md` repeats it.  **The word "only" is now false, and this file is the
    measurement that makes it false.**  It is a single downstream consumer.  It
    `Require`s six proofs of `False` from the 2026-08-20 Rocq wave, derives
    `1 = 2` from each, and prints `Print Assumptions` for all six.  On Rocq 9.2
    every one of those lines reads `Closed under the global context`, `rocqchk`
    certifies this file in both of its modes, and `rocqchk -o` reports
    `* Axioms: <none>`.

    §4.1's *ranking* survives — nothing here is stronger than rocq#21839 — but
    its uniqueness does not.  #21839 now has six peers, all filed within
    fifty-five minutes of one another, and all open with unmerged fixes.

    ** The wave, and the census

    On 2026-08-20, between 12:31 and 13:26 UTC, `rocq-prover/rocq` received nine
    `kind: inconsistency` issues, filed by maintainers `SkySkimmer` (six) and
    `yannl35133` (three) on behalf of an outside reporter the bodies name:
    #22378 says *"Reported by OpenAI by email to a random core team member"*;
    #22386 says *"Found by an LLM and @dselsam"*.  All nine were run here against
    five requirements — a closed `False`; no flag; `Print Assumptions` silent;
    `rocqchk` silent in **both** modes; and survival of a plain `Require`.
    **Six pass all five.**

    | Issue  | closed False | flag-free | Print Assumptions | rocqchk, both modes | survives Require | verdict |
    | ------ | ------------ | --------- | ----------------- | ------------------- | ---------------- | ------- |
    | #22376 | conditional  | no, `Set Definitional UIP` | **names it** | silent | yes, and names it | Paradoxes/ |
    | #22378 | yes          | yes       | silent            | silent              | yes              | **peer** |
    | #22380 | conditional  | no, `Set Definitional UIP` | **names it** | silent | yes, and names it | Paradoxes/ |
    | #22382 | yes          | yes       | silent            | silent              | yes              | **peer** |
    | #22383 | yes          | yes       | silent            | silent              | yes              | **peer** |
    | #22386 | yes          | yes       | silent            | silent              | yes              | **peer** |
    | #22387 | yes          | **no**, `Unset Elimination Schemes` | silent | silent *only while sealed* | yes | near miss |
    | #22389 | yes          | yes       | silent            | silent              | yes              | **peer** |
    | #22391 | yes          | yes       | silent            | silent              | yes              | **peer**, 9.2 only, and see the caveat below |

    Everything in that table was run, not read off an issue body.

    ** One caveat on #22391, recorded here so the table is not read too fast

    #22391 meets all five requirements — measured, and the `1 = 2` below is
    built from it like the other five.  But it is the one witness whose
    `collision` cannot be put in front of the kernel by ordinary means: on 9.2
    both `exact` and a plain term-mode `Definition` abort with
    `Anomaly "Universe Var(0) undefined."` at exit 1, and only `exact_no_check`,
    which declines the *tactic-level* retypecheck and switches nothing off in
    the kernel, gets the term to `Defined.` — where the kernel accepts it and
    where `rocqchk` afterwards re-checks it by name
    (`checking cst:AuditBlindStuckCase.collision`) and certifies it.  So the
    acceptance is the kernel's own on two independent implementations, which is
    what category (a) asks for and what the five requirements test.  It is still
    more ceremony than rocq#21839 needs — that one is a bare
    `Definition oops : False` — and than the other five need.  `#22391` is a peer
    on the audit channels and not on the effort.  Full measurement in
    `AuditBlindStuckCase.v`.

    The three that do not qualify each fail for a different reason, and each
    reason is a separate fact worth keeping:

      - **#22376 and #22380** derive `False` only under `Set Definitional UIP`,
        and `Print Assumptions contradiction` says so on both:
        `seq relies on definitional UIP.`  It says so downstream too, through a
        plain `Require`: `U376.seq relies on definitional UIP.`  That is ground
        rule 1 working as designed — the `False` is conditional, the condition is
        in the audit, and the class belongs in `Paradoxes/` rather than in
        `KernelDefects/`.  Upstream conjectures on #22380 that *"there should be
        an inconsistency without UIP too"*, since the missing substitution also
        affects the predicate and the branches and not only `CaseInvert`; that
        conjecture is **untested here** and is the obvious next probe.  Note that
        rocq#22391, which *is* counted, is the same missing composition at a
        different site and needs no UIP — so the conjecture is at least not
        idle.
      - **#22387** fails twice.  It needs `Unset Elimination Schemes` — delete
        that line and the subtyping check on the *generated* `T_rect` refuses the
        functor application.  And its `rocqchk` silence is bought by the seal:
        `Module Applied : R := F A` stores `Applied`'s components with no bodies,
        so the checker has nothing to re-check and lists `Applied.result` under
        `* Axioms:` — a line an honest sealed module produces identically,
        measured.  Remove the ascription and keep everything else, and `rocqchk`
        **rejects** the `.vo` with `Fatal Error: Type error: ActualType` at exit
        129 in both modes.  So the independent checker owns a working safeguard
        against #22387; rocq#21839 has none anywhere.  All of this is measured in
        `AuditBlindSubtypeLetin.v`, which is kept in this directory precisely so
        that the count of six is checkable rather than asserted, and agrees with
        the module-system treatment in
        ../ModuleSystem/LetinOrderSubtypingUnsealed.v.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), native compiler disabled

      - `coqc AuditBlindSextet.v`            exit 0
      - six `Print Assumptions` lines        `Closed under the global context`
      - the seventh, the control             `AuditBlindUipControl.seq relies on
                                              definitional UIP.`
      - `rocqchk AuditBlindSextet`           `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`     `Modules were successfully checked`, exit 0
      - `rocqchk -o`                         `* Axioms: <none>`
                                             `* Constants/Inductives relying on
                                                type-in-type: <none>`
                                             `* Constants/Inductives relying on
                                                unsafe (co)fixpoints: <none>`

    ** On Rocq Platform 9.0.1 the count is five, not six

    Driven as `coqc.exe -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"`.  Five of
    the six behave identically, on a five-way consumer built exactly the same
    way: `coqc` exit 0, five `Closed under the global context` lines, the control
    still reporting `AuditBlindUipControl.seq relies on definitional UIP.`,
    `coqchk` and `coqchk -bytecode-compiler yes` both
    `Modules were successfully checked` at exit 0, and `coqchk -o` reporting
    `* Axioms: <none>`.

    rocq#22391 does not run there at all: it aborts with
    `Anomaly "in Univ.repr: Universe Var(0) undefined."` at exit 129, and so does
    rocq#22380, the other member of its uncomposed-universe-substitution family.
    As far as these two installed toolchains can say, that family is a **9.2
    regression**, narrowly: one release earlier the same input crashed where
    9.2's *kernel* now accepts it.  9.2's *elaborator* still aborts with the
    same anomaly on the neighbouring routes, so what moved between the releases
    is the kernel's verdict, not the whole delayed-substitution path going
    quiet.  Both halves measured; see `AuditBlindStuckCase.v`.

    ** The control, and why it is inside this file rather than beside it

    Six silent audits are evidence only if a seventh would have spoken.
    `AuditBlindUipControl.v` is `Require`d here alongside the six and reports
    `AuditBlindUipControl.seq relies on definitional UIP.` — same command, same
    `Require` boundary, same run, same `Print Assumptions`.  The channel is open;
    the six simply have nothing to put through it.  Per-defect one-token controls
    are in `AuditBlindControls.v`; rocq#22391's is inside
    `AuditBlindStuckCase.v`, because on 9.0.1 it aborts with an anomaly and
    `Fail` cannot catch those.

    ** A method note, because it cost time (ground rule 5)

    Two of the six have non-normalising witnesses, and writing the derivation as
    `match X.contradiction with end` makes the elaborator infer the return
    clause, which reduces the witness and does not come back:
    `AuditBlindUniformArgs` and `AuditBlindNestedCofix` both ran past 40 s and
    were killed, while the other four returned at once.
    `False_ind (1 = 2) X.contradiction` — or an explicitly annotated
    `match ... return 1 = 2 with end` — never reduces the witness and returns
    immediately.  A harness that judged by wall clock would have scored those two
    as "rejected".  Judge by exit code and by the audit.

    Write-up: ../../../Reports/2026-08-20-rocq-august-wave.md *)

Require AuditBlindLetinConv.
Require AuditBlindUniformArgs.
Require AuditBlindCumulLetin.
Require AuditBlindCofixEnv.
Require AuditBlindNestedCofix.
Require AuditBlindStuckCase.
Require AuditBlindUipControl.

(** ** An ordinary falsehood from each of the six. *)

(** rocq#22378 — conversion mislays the relevance of let-bound constructor fields. *)
Definition one_eq_two_22378 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindLetinConv.contradiction.

(** rocq#22382 — the guard checker's uniform-argument finder counts a `let`. *)
Definition one_eq_two_22382 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindUniformArgs.contradiction.

(** rocq#22383 — variance inference erases a let-bound constructor field. *)
Definition one_eq_two_22383 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindCumulLetin.contradiction.

(** rocq#22386 — a cofixpoint's rectree is computed in the wrong environment. *)
Definition one_eq_two_22386 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindCofixEnv.contradiction.

(** rocq#22389 — nested mutual cofixpoints share one ambient rectree. *)
Definition one_eq_two_22389 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindNestedCofix.contradiction.

(** rocq#22391 — stuck-case conversion rebuilds a `let` at an uncomposed instance. *)
Definition one_eq_two_22391 : 1 = 2 :=
  False_ind (1 = 2) AuditBlindStuckCase.contradiction.

(** ** Six audits, and every one of them silent.

    Expected, all six: [Closed under the global context]. *)

Print Assumptions one_eq_two_22378.
Print Assumptions one_eq_two_22382.
Print Assumptions one_eq_two_22383.
Print Assumptions one_eq_two_22386.
Print Assumptions one_eq_two_22389.
Print Assumptions one_eq_two_22391.

(** ** The control: the same channel, in the same file, carrying something.

    Expected: [Axioms:] then
    [AuditBlindUipControl.seq relies on definitional UIP.] *)

Definition control_downstream : nat -> nat := AuditBlindUipControl.reported.

Print Assumptions control_downstream.
