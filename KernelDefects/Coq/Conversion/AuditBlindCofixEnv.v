(** * rocq#22386 — a cofixpoint's recursive tree is computed in the wrong environment

    rocq-prover/rocq#22386, filed 2026-08-20 13:16 UTC by `yannl35133`, **OPEN**,
    fix PR unmerged.  The issue body says *"Found by an LLM and @dselsam"*.

    ** Category (a): a closed proof of `False` with every audit channel silent

    The guard condition for a `cofix` computes the recursive tree of its declared
    codomain in an environment that does not carry the surrounding `let`s.  Here
    the codomain is written `actual`, a local definition standing for `Empty` —
    an **inductive** type.  Unfolded, the declaration is `cofix recur : Empty`,
    which is not a cofixpoint at all; not unfolded, the check has nothing to
    object to.  The result is an infinitely deep element of an inductive type,
    and an ordinary structural `Fixpoint` over it returns `False`.

    `decoy`, the second `let`, is upstream's: it shows that the environment is
    ignored rather than misread — a genuine coinductive type sitting in scope
    changes nothing.

    ** Measured on Rocq 9.2 (OCaml 4.14.2), the current stable release

      - `coqc AuditBlindCofixEnv.v`       exit 0
      - `Print Assumptions contradiction` `Closed under the global context`
      - `rocqchk` (default)               `Modules were successfully checked`, exit 0
      - `rocqchk -bytecode-compiler yes`  `Modules were successfully checked`, exit 0
      - `rocqchk -o`                      `* Axioms: <none>`,
                                          `* ... unsafe (co)fixpoints: <none>`
      - plain `Require` downstream        survives; see AuditBlindSextet.v

    Same on Rocq Platform 9.0.1: exit 0, clean audit, `coqchk` clean in both modes.

    ** Control, and it is one token

    `AuditBlindControls.v` module `C86` keeps both `let`s and writes the codomain
    as `Empty` rather than as `actual`.  Same file, same `let`s, one identifier
    changed, and the same `coqc` rejects it:

      Recursive definition of recur is ill-formed.
      In environment
      actual := Empty : Type
      decoy := Stream : Type
      recur : Empty
      The codomain is "Empty"
      which should be a coinductive type.
      Recursive definition is: "wrap recur".

    The check that should fire is right there, and it fires the moment the name
    is spelled out. *)

CoInductive Stream : Type := next : Stream -> Stream.
Inductive Empty : Type := wrap : Empty -> Empty.

Definition cycle : Empty :=
  let actual := Empty in
  let decoy := Stream in
  cofix recur : actual := wrap recur.

Fixpoint absurd (x : Empty) : False :=
  match x with wrap y => absurd y end.

Definition contradiction : False := absurd cycle.

(** Expected: [Closed under the global context]. *)
Print Assumptions contradiction.
