(** * rocq#21702 -- module system: [with Definition] stored the weaker universes

    THIS FILE IS EXPECTED TO BE REJECTED.  It is a regression witness, not a
    build target.  On an affected Rocq it compiles and yields an axiom-free
    [False]; on a fixed one the universe constraints are enforced and [A] is
    refused.

    Category (per ../../README.md): IMPLEMENTATION DEFECT (fixed).

    The defect: [check_with_def] type-checked the body supplied by
    [with Definition] and then stored *that body's* universe constraints instead
    of the signature's.  [SIG] declares [coerce@{}] with [Constraint u <= v];
    the with-body [fun (x : Type@{u}) => x] needs no constraint at all, being the
    identity.  Storing the weaker set leaves [M.coerce : Type@{u} -> Type@{v}]
    with no [u <= v] recorded -- a cast from a larger universe into a smaller
    one, which is exactly the hypothesis [Hurkens.TypeNeqSmallType.paradox]
    wants.

    Note the shape, because it recurs: nothing here is a misstatement about a *term*.
    The term is the identity function and it is fine.  What was lost is a side
    condition, and the kernel then reasons correctly from a premise that is too
    weak.  Compare ./UniverseFlagDesync.v (#22287), where a flag rather than a
    constraint is what desyncs, and
    ../../../EscapeHatches/Lean/ArenaTrustedMetadata.lean, where derived
    metadata is what is falsified.  Three subsystems, one failure mode.

    Upstream: <https://github.com/rocq-prover/rocq/issues/21702>
      affected the kernel 8.5-9.1 -- twenty patch releases -- fixed in 9.2.0.

    Verified with [coqc] on The Rocq Prover 9.2 (OCaml 4.14.2):

      REJECTED at [A], exit code 1, with

        The term "M.coerce Type" has type "Type@{WithDefUniverses.28}"
        while it is expected to have type "Type@{small}"
        (universe inconsistency: Cannot enforce WithDefUniverses.28 <= small
         because small < big < WithDefUniverses.27 <= WithDefUniverses.28).

    The needle ../verify.ps1 asserts is [universe inconsistency]: the
    constraint that went missing is precisely the one now enforced.  The
    numbered universe names are anonymous and would move if the file were
    edited, so they are deliberately not part of the assertion. *)

Set Universe Polymorphism.

Module Type SIG.
  Section S.
    Universe u v.
    Constraint u <= v.
    Parameter coerce@{} : Type@{u} -> Type@{v}.
  End S.
End SIG.

Module Type SIG2 := SIG with Definition coerce@{u v} := fun (x : Type@{u}) => x.
Declare Module M : SIG2.

Section Test.
  Universe big small.
  Constraint small < big.
  Definition A : Type@{small} := M.coerce Type@{big}.
End Test.
From Stdlib Require Import Hurkens.
Definition false_ : False := Hurkens.TypeNeqSmallType.paradox A eq_refl.
Print Assumptions false_.
