(** * rocq#21736 -- VM conversion: [Register Inline] dropped the universe instance

    THIS FILE IS EXPECTED TO BE REJECTED.  It is a regression witness, not a
    build target.  On an affected Rocq it compiles and yields an axiom-free
    [False]; on a fixed one the kernel refuses the deferred cast at [Qed].

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    The defect: [Register Inline] asks the VM to inline a constant, and
    [genlambda.ml] failed to substitute the universe instance when it did.
    [foo@{u v} : Type@{v} := Type@{u}] then compiles to something the VM
    converts with [Type@{v}] regardless of the instance, so [vm_cast_no_check]
    accepts [eq_refl : Type@{v} = foo@{u v}].  That is [Type@{v} = Type@{u}]
    for [u < v], and Hurkens does the rest.

    Two things make this the most serious entry in section 4.4 of
    ../../../CATALOG.md.

    It affected **every patch release from 8.5 to 9.1** -- some sixteen years of
    releases -- and, unlike the guard-checker family, **[coqchk] was affected
    too**.  [coqchk] re-runs conversion, and the VM it re-runs it with had the
    same bug, so the second checker agreed.  That is the same shape as this
    repository's two strongest live findings, from opposite systems: #21839
    (../GuardChecker/WrongEnvReduction.v), where [coqchk] shares Rocq's guard
    checker, and lean4#14613 (../../Lean/Universes/), where [leanchecker] shares
    Lean's kernel.  A second checker is a second opinion only where it is a
    second implementation.

    Note where the rejection lands: not at the [Lemma] line but at [Qed].
    [vm_cast_no_check] is the whole point -- it defers conversion to the kernel
    at proof-checking time, which is what makes the VM part of the trusted base
    rather than a tactic.  A fixed Rocq catches it exactly there.

    Upstream: <https://github.com/rocq-prover/rocq/issues/21736>
      affected 8.5-9.1 (and coqchk), fixed in 9.2.0.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2):

      REJECTED at [Qed] of [bar], exit code 1, with

        The term "eq_refl" has type "Type = Type"
        while it is expected to have type "typ".

    The displayed types print without their universe annotations, so the message
    reads oddly -- [Type = Type] is exactly what the file is trying and failing
    to prove, at two different universe levels.  ../verify.ps1 asserts
    [while it is expected to have type] rather than the bare types. *)

Set Universe Polymorphism.

Definition foo@{u v} : Type@{v} := Type@{u}.
Register Inline foo.

Definition typ@{v u k} := Type@{v} = foo@{u v} :> Type@{k}.

Lemma bar@{v u k|u < v, v < k} : typ@{v u k}.
Proof.
  vm_cast_no_check (@eq_refl Type@{k} Type@{v}).
Qed.

From Stdlib Require Import Hurkens.

Unset Universe Polymorphism.

Lemma bad : False.
Proof.
  eapply TypeNeqSmallType.paradox. apply bar.
Qed.

Print Assumptions bad.
