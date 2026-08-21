(** * rocq#22391 — stuck-case conversion rebuilds a `let` at an uncomposed instance

    rocq-prover/rocq#22391, filed 2026-08-20 13:26 UTC by `SkySkimmer`, **OPEN**,
    fix PR unmerged.  Last of the nine filed that morning, and reported the same
    way as #22378 and #22383 — *"Reported by OpenAI by email to a random core team
    member"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    Upstream quotes the reporting agent:

      "In `convert_stacks`, the code correctly composes delayed universe
       substitutions when comparing the two case instances.  It then passes the
       original, uncomposed instances to `convert_return_clause` and
       `convert_branches`.  Those helpers reconstruct local definitions from the
       inductive declaration at the wrong universe.  A permutation of the
       surrounding abstract universe slots consequently makes the two unequal
       readers appear convertible."

    `token` is **NonCumulative**, so this is not #22383's variance path: nothing
    here depends on subtyping.  Two readers of the same let-bound constructor
    field stay stuck on the same variable `t`; the kernel compares them, rebuilds
    `ghost := Type@{u}` with the wrong instance, and calls them equal.  `collision`
    is then accepted — that acceptance *is* the defect — and its `Print
    Assumptions` is already `Closed under the global context`.

    ** The permutation is what the construction needs, and 9.2 is what it needs

    `read_token@{hi top}` occupies abstract slots 1 and 2 of a three-slot binder
    `@{lo hi top}`.  With the uncomposed instance the reconstruction reads slots
    0 and 1 instead, so the let comes back as `Type@{lo}` — which is exactly what
    the other reader returns.  Line up the reader with slots 0 and 1 and the
    kernel gets it right; that is the control below.

    The final three lines instantiate at **monomorphic** universes.  That is not
    decoration: inside a polymorphic binder the elaborator refuses to convert
    `read_token@{hi top} make_token@{hi top}` with `Type@{hi}` (measured), so the
    two honest reductions are taken at concrete levels and composed with
    `eq_trans`.  Neither `lhs` nor `rhs` is a defect — each is checked normally.
    Only `inst` carries the wrong equation.

    ** `exact_no_check` is load-bearing here, and this is the one place in the
       census where the route to the kernel is not the ordinary one

    Stated plainly, because the rest of the file would otherwise imply that
    `coqc` accepts `collision` the way it accepts the other five witnesses.  It
    does not.  On 9.2 **every route that asks the elaborator to perform this
    conversion aborts**, and both were measured:

      - `exact` in place of `exact_no_check`, exhibit only:
          `Error: Conversion test raised an anomaly:`
          `Anomaly "Universe Var(0) undefined."`   exit 1
      - the same thing written in term mode, `Definition collision@{lo hi top}
        (t : token@{hi top}) : @eq ... := @eq_refl ...`, no tactics at all:
          identical message, exit 1.

    `exact_no_check` declines the **tactic-level** retypecheck.  It is not a
    `Set`/`Unset` flag, it switches nothing off in the kernel, and ground rule 2
    is therefore not engaged: the term is still handed to the kernel at
    `Defined.`, the kernel typechecks it and accepts, and `rocqchk` reading the
    `.vo` afterwards re-checks it by name —

      checking cst:AuditBlindStuckCase.collision

    — and certifies.  So the acceptance being exhibited is the kernel's own, on
    two independent implementations of it, which is what category (a) asks for.

    But it is a real difference in degree from the other five, and from
    rocq#21839 itself, whose exhibit
    ../GuardChecker/WrongEnvReduction.v is a direct `Definition oops : False`
    with no tactic anywhere.  #22391 is a peer of #21839 on all five audit
    channels — that claim is measured and stands — and it is *weaker* than
    #21839 on the separate question of how much ceremony it takes to put the
    term in front of the kernel.  `AuditBlindSextet.v`'s table records the
    caveat in the same words.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindStuckCase.v`      exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... type-in-type: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    ** On Rocq Platform 9.0.1 it does not run at all, and that is a finding

    `coqc.exe -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"` aborts with

      Error: Anomaly "in Univ.repr: Universe Var(0) undefined."

    at **exit 129**.  As this file stands the abort lands on the control's
    `Fail Defined.` below, which comes first and which `Fail` cannot catch
    because an anomaly is not an error; with the control deleted, the exhibit's
    own `Defined.` aborts identically, and so does upstream's original
    `Set Universe Polymorphism` spelling with no `Polymorphic` attributes at all.
    All three measured.

    So on 9.0.1 this is a crash, not a `False`.  The comparison with 9.2 has to
    be stated narrowly, because the section above measured 9.2's elaborator
    aborting on this same construction with the same anomaly family:

      - 9.0.1, `exact_no_check` then `Defined.`:
          `Anomaly "in Univ.repr: Universe Var(0) undefined."`, exit 129
      - 9.2, `exact_no_check` then `Defined.`:                    **accepted**
      - 9.2, `exact` or term mode:
          `Anomaly "Universe Var(0) undefined."`, exit 1

    What changed between the two releases is therefore the **kernel's** verdict
    on a term the elaborator will not build on either one.  That is still a
    regression in the direction that matters — 9.0.1 had no route here at all,
    9.2 has one and takes it silently — but it is not the whole
    delayed-substitution path going quiet.  rocq#22380, the other member of this
    family, aborts on 9.0.1 with the same `Univ.repr` anomaly.  **This file is
    therefore 9.2-only among the two installed toolchains**, and it is the only
    one of the six in `AuditBlindSextet.v` of which that is true.

    Because the abort is an anomaly rather than an error, `Fail` cannot catch it,
    which is why this exhibit carries its own control instead of putting it in
    `AuditBlindControls.v` — that file must stay green on both toolchains. *)

(** ** Control — the same construction with the reader's slots NOT permuted.

    `lo` becomes a global monomorphic universe, so `read_token@{hi top}` lands on
    the binder's slots 0 and 1 and the uncomposed instance happens to be the
    right one.  Measured on 9.2: rejected at `Defined.`, by the kernel, with

      The term "fun t : token => eq_refl" has type
       "forall t : token, read_token t = read_token t"
      while it is expected to have type
       "forall t : token, read_token t = read_constant t".

    On 9.0.1 this control aborts with the same `Univ.repr` anomaly as the
    exhibit, so it carries no signal there; its verdict is a 9.2 measurement. *)

Module ControlNoPermutation.
  Monomorphic Universe GLO.

  Polymorphic NonCumulative Inductive token@{u v | u < v} : Set :=
  | make_token (ghost : Type@{v} := Type@{u}).

  Polymorphic Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
    match t with make_token ghost => ghost end.

  Polymorphic Definition read_constant@{hi top | GLO < hi, hi < top}
      (t : token@{hi top}) : Type@{top} :=
    match t with make_token ghost => Type@{GLO} end.

  Polymorphic Definition collision@{hi top | GLO < hi, hi < top}
      (t : token@{hi top}) :
    @eq Type@{top} (read_token@{hi top} t) (read_constant@{hi top} t).
  Proof.
    exact_no_check (@eq_refl Type@{top} (read_token@{hi top} t)).
  Fail Defined.
  Abort.
End ControlNoPermutation.

(** ** The exhibit. *)

Polymorphic NonCumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Polymorphic Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Polymorphic Definition read_constant@{lo hi top | lo < hi, hi < top}
    (t : token@{hi top}) : Type@{top} :=
  match t with make_token ghost => Type@{lo} end.

(** The kernel accepts this.  Two readers that return different universes are
    convertible while both are stuck on [t]. *)
Polymorphic Definition collision@{lo hi top | lo < hi, hi < top}
    (t : token@{hi top}) :
  @eq Type@{top} (read_token@{hi top} t) (read_constant@{lo hi top} t).
Proof.
  exact_no_check (@eq_refl Type@{top} (read_token@{hi top} t)).
Defined.

Monomorphic Universes LO HI TOP.
Monomorphic Constraint LO < HI.
Monomorphic Constraint HI < TOP.

Definition inst
  : @eq Type@{TOP} (read_token@{HI TOP} make_token@{HI TOP})
                   (read_constant@{LO HI TOP} make_token@{HI TOP})
  := collision@{LO HI TOP} make_token@{HI TOP}.

(** [lhs] and [rhs] are honest: each is the ordinary iota reduction. *)
Definition lhs
  : @eq Type@{TOP} (read_token@{HI TOP} make_token@{HI TOP}) Type@{HI} := eq_refl.
Definition rhs
  : @eq Type@{TOP} (read_constant@{LO HI TOP} make_token@{HI TOP}) Type@{LO} := eq_refl.

Definition collapse : @eq Type@{TOP} Type@{HI} Type@{LO} :=
  eq_trans (eq_trans (eq_sym lhs) inst) rhs.

From Stdlib Require Import Hurkens.

Definition contradiction : False := TypeNeqSmallType.paradox _ collapse.

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
