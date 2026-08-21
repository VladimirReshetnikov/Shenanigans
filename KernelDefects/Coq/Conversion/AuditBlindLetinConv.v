(** * rocq#22378 — conversion mislays the relevance of let-bound constructor fields

    rocq-prover/rocq#22378, filed 2026-08-20 12:47 UTC by `SkySkimmer`, **OPEN**,
    fix PR unmerged.  One of nine `kind: inconsistency` issues filed in fifty-five
    minutes that day.  The issue body says the construction was *"Reported by
    OpenAI by email to a random core team member"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    `kernel/conversion.ml`'s `convert_under_context` substitutes let-bound
    constructor fields away with `esubst_of_context`, so it lifts the conversion
    context by the two surviving `nat` arguments — but it pushes the relevance
    annotations of all **four** original binders.  The two real variables are then
    looked up at positions marked irrelevant, and `x` converts with `y`.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindLetinConv.v`      exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... type-in-type: <none>`,
                                          `* ... unsafe (co)fixpoints: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    Same on Rocq Platform 9.0.1 (`coqc -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"`):
    exit 0, `Closed under the global context`, `coqchk` clean in both modes.

    ** Control

    `AuditBlindControls.v` module `C78` runs the identical construction with
    `SProp` changed to `Prop` — one token — and the same `coqc` rejects it:

      The term "eq_refl" has type "fst_of p = fst_of p"
      while it is expected to have type "fst_of p = snd_of p"
      (cannot unify "fst_of p" and "snd_of p").

    So it is the *irrelevance* of the let-bound fields, not their presence, that
    carries the defect. *)

Inductive sUnit : SProp := stt.

Inductive pair_with_lets : Type :=
| pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).

Definition fst_of (p : pair_with_lets) : nat :=
  match p with pack x y _ _ => x end.

Definition snd_of (p : pair_with_lets) : nat :=
  match p with pack x y _ _ => y end.

(** The kernel accepts this: [fst_of p] and [snd_of p] project different
    arguments and are nonetheless convertible. *)
Definition collision (p : pair_with_lets) : fst_of p = snd_of p := eq_refl.

Definition zero_eq_one : O = S O := collision (pack O (S O)).

Definition contradiction : False :=
  match zero_eq_one in (_ = n)
    return (match n with O => True | S _ => False end)
  with eq_refl => I end.

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
