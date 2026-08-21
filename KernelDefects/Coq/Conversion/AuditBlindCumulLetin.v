(** * rocq#22383 — variance inference walks past a let-bound constructor field

    rocq-prover/rocq#22383, filed 2026-08-20 13:13 UTC by `SkySkimmer`, **OPEN**,
    fix PR unmerged.  Reported the same way as #22378 — *"Reported by OpenAI by
    email to a random core team member"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    Cumulativity inference decomposes a constructor's type with
    `whd_decompose_prod`, which **erases let-bindings**.  `token`'s only field is
    a let, `ghost := Type@{u}`, so `u` never appears in what the inference looks
    at and `u` is recorded as *irrelevant* to the inductive's subtyping.  `match`
    can still read the let out.  Upstream's own diagnosis: *"`u` is irrelevant in
    `token` but match can get it out through the letin."*

    `read_token@{Set u}` applied to `make_token@{u v}` therefore returns
    `Type@{u}` at type `Type@{u}` — a universe that contains itself — and
    `Hurkens.TypeNeqSmallType` finishes.

    Note that `Set Universe Polymorphism` is *not* load-bearing as a flag: it is
    replaced here by per-declaration `Polymorphic` attributes so that this file
    changes no ambient setting for anything that `Require`s it, and universe
    polymorphism is a feature rather than a weakened check.  Marking `u`
    irrelevant by hand with `*u`, as upstream does, is likewise not load-bearing:
    plain `Cumulative` **infers** the same wrong variance.  `*u` is kept because
    it is what upstream wrote and because it names the wrong answer explicitly.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindCumulLetin.v`     exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... type-in-type: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    Same on Rocq Platform 9.0.1: exit 0, clean audit, `coqchk` clean in both modes.

    ** Control, and it is one token

    `AuditBlindControls.v` module `C83` writes `=u` instead of `*u` — declaring
    the universe **invariant**, which is the answer the inference should have
    reached — and the same `coqc` rejects it:

      The term "make_token" has type "let ghost := Type in token"
      while it is expected to have type "token"
      (universe inconsistency: Cannot enforce Set = u).

    The error prints `let ghost := Type in token`, which is the let the inference
    had thrown away. *)

Polymorphic Cumulative Inductive token@{*u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Polymorphic Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

(** [make_token@{u v}] is silently accepted at [token@{Set u}]. *)
Polymorphic Definition small@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (make_token@{u v}).

Polymorphic Definition small_is_universe@{u v | Set < u, u < v} :
  @eq Type@{v} small@{u v} Type@{u} := eq_refl.

From Stdlib Require Import Hurkens.

Definition contradiction : False :=
  TypeNeqSmallType.paradox small (eq_sym small_is_universe).

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
