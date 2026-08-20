(** * A closed [False] that `rocqchk -bytecode-compiler yes` certifies as checked

    rocq-prover/rocq#22352, reported 2026-08-18 by Jason Gross and **OPEN**.

    [rocqchk] typechecks each constant's body, and then — with the non-default
    [-bytecode-compiler yes] — performs VM conversions using the bytecode it
    reads from the .vo's separately serialised [vmlibrary] segment, with nothing
    tying that segment to the bodies it just checked.  Splice one honest
    compilation's [library] onto another's [vmlibrary] and the resulting .vo is
    well formed, well typed, and lies about what its constants compute.

    The lie is cashed by the [<:] VMcast below.  [poc_evil]'s BODY is
    [idb true]; its BYTECODE says [false].  So [myeq_refl bool false] is accepted
    at type [myeq bool poc_evil false], and with [evil_true] on the other side
    [true] and [false] are identified.

    ** What each channel reports, measured on Rocq 9.2 (the current release)

      - [rocq c Evil.v]:                    exit 0.  Not caught.
      - [Print Assumptions boom]:           "Closed under the global context".
                                            **Not caught.**
      - [rocqchk -bytecode-compiler yes]:   "Modules were successfully checked".
                                            **Not caught.**
      - [rocqchk] (default):                [Fatal Error: Type error: ActualType],
                                            at [Evil.evil_false].  Caught.
      - [rocqchk] on the spliced Defs ALONE: accepted in BOTH modes, correctly —
                                            its declarations are well typed and
                                            only its bytecode segment lies.

    So the .vo that is hand-edited with is not the .vo that fails.  The failure
    surfaces one library downstream, in the file whose VMcast only typechecked
    because [rocq compile] believed the bogus bytecode.

    ** Where this sits in the catalog

    CATALOG.md §1.2 has a row reading "[hand-edited] or stale .vo / .olean → nothing;
    neither system re-typechecks on import", with the note that Rocq hardened its
    [coqchk] path in 8.19.  That is the row this exhibit refines.  [coqchk] IS
    the answer to a hand-edited .vo, it DOES re-typecheck, and in one of its two
    supported modes it still certifies this one.  §4.7's asymmetry, in its
    sharpest form so far: not "the checker is not run", but "the checker ran,
    said [Modules were successfully checked], and had not derived the code it
    executed from the terms it checked".

    Note what is NOT claimed.  This needs a hand-edited object file, so it is not
    a route to [False] from ordinary source — [splice.py] is the probe.  What is
    new is that the tool whose entire purpose is to catch a hand-edited object
    file reports success on this one.  The [False] itself needs no flag: [rocq c]
    accepts it with defaults, and [Print Assumptions] is clean.

    ** Control

    ../verify.ps1 compiles this same file against an UNSPLICED [Defs.vo] and
    requires it to be rejected:

      The term "myeq_refl bool false" has type "myeq bool false false"
      while it is expected to have type "myeq bool poc_evil false".

    Acceptance below means something only because that control fails.

    ** Versions

    Upstream: present since 8.20 ([e6535d48bd], which introduced the dedicated
    [vmlibrary] segment), reported against master at 9.4+alpha.  **Measured here
    on 9.2 (vo_version 90299)**, which is the current stable release — upstream's
    report does not state 9.2, so this file is where that is pinned.
    rocq#22353 is the fix, and it is not in any release.

    Write-up: ../../../Reports/2026-08-18-rocqchk-vm-bytecode.md *)

Require Import Defs.

Inductive myeq (A : Type) (x : A) : forall _ : A, Prop := myeq_refl : myeq A x x.
Inductive True  : Prop := I.
Inductive False : Prop := .

(** Honest: [poc_evil]'s body really is [idb true]. *)
Definition evil_true : myeq bool poc_evil true := myeq_refl bool poc_evil.

(** The VMcast.  The kernel VM-converts [poc_evil] through the .vo's stored
    bytecode, which says [false]. *)
Definition evil_false : myeq bool poc_evil false :=
  (myeq_refl bool false) <: (myeq bool poc_evil false).

Definition myeq_sym (A : Type) (x y : A) (h : myeq A x y) : myeq A y x :=
  myeq_ind A x (fun z => myeq A z x) (myeq_refl A x) y h.

Definition myeq_trans (A : Type) (x y z : A) (h1 : myeq A x y) (h2 : myeq A y z)
  : myeq A x z := myeq_ind A y (fun w => myeq A x w) h1 z h2.

Definition true_eq_false : myeq bool true false :=
  myeq_trans bool true poc_evil false (myeq_sym bool poc_evil true evil_true) evil_false.

Definition boom : False :=
  myeq_ind bool true (fun b => match b return Prop with true => True | false => False end)
    I false true_eq_false.
