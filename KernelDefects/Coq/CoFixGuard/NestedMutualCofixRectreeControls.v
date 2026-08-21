(** * Controls for NestedMutualCofixRectree.v — three ways to move the same term, all refused

    rocq#22389.  Ground rule 6.  The exhibit is a closed [False] that every
    audit channel calls clean, so it is worth nothing until the same procedure
    on the same toolchain refuses deliberately-broken twins built from the same
    pieces.

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit 0.  Every refusal is wrapped
    in [Fail], so a control that stopped refusing would fail the file.

    The three controls each move the offending term — the corecursive call
    sitting in [ic ...], an *inductive* constructor — a little, without changing
    what it is:

    | # | Arrangement                                     | Verdict | The kernel says |
    | - | ----------------------------------------------- | ------- | --------------- |
    | 1 | the mutual block un-nested to top level         | REFUSED | [Recursive call on a non-recursive argument of constructor "f2"] |
    | 2 | still nested, but the call names the INNER cofix | REFUSED | [Recursive call on a non-recursive argument of constructor "f"] |
    | 3 | the [with] clause deleted and its body inlined   | REFUSED | [Recursive call on a non-recursive argument of constructor "ic cycleC"] |
    | 4 | no nesting at all                               | REFUSED | [Recursive call on a non-recursive argument of constructor "ic cycleD"] |
    | 5 | a nested mutual block whose members share a type | ACCEPTED | [Closed under the global context], and correctly |

    The first four name the very check the exhibit slips past, and §3 and §4
    name the offending subterm itself.  §5 is the other direction: the shared
    rectree is not wrong in general, only when a member's declared type differs
    from the outer one's, and a productive corecursive value written in exactly
    the exhibit's shape is accepted and computes.  So the trigger is pinned to
    one thing: **being a non-main member of a nested mutual block whose declared
    type is not the outer cofixpoint's**.  Upstream's report does not narrow it;
    this is the repository's measurement.

    §2 is the sharpest, and it is two tokens.  The exhibit's [g] calls [cycle],
    a binding of the *outer* block; replace those two occurrences by [f], a
    binding of the *inner* block, and the construction is the same infinite
    regress — but now the recursive call belongs to the block that IS checked
    against its own tree, and the kernel refuses immediately.  The inner block
    was never broken.  What is broken is the outer block's walk through it.

    Measured on Rocq 9.2 (OCaml 4.14.2) **and** on Rocq 9.0.1 (Rocq Platform
    9.0~2025.08, driven with [-coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"]).
    Every verdict and every message below is byte-identical on the two.  Each
    refusal was re-derived by stripping the single [Fail] in front of it and
    capturing [coqc]'s output, one control at a time, on each toolchain — not
    inferred from the file compiling.

    Expected output of this file, in order: on 9.2, twelve copies of the
    [register-all] warning on [Inductive I] — 9.0.1 emits none, see
    NestedMutualCofixRectree.v under "Note on output" — then
    [Closed under the global context] from §5, then [= 0 : nat].

    For the audit-channel control — the proof that [Print Assumptions] and
    [rocqchk -o] do report an unguarded cofixpoint when they are given one — see
    CofixWrongEnvRectreeControls.v §7, which prints
    [cycleU is assumed to be guarded.] and makes [rocqchk -o] list the constant
    under unsafe (co)fixpoints.  It is not repeated here. *)

CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
Inductive I : Type := ic : C I -> I.

(** ** 1 — the same two definitions, un-nested.

    [f] and [g] promoted to a top-level mutual [CoFixpoint].  Now [check_cofix]
    looks a tree up for each member from that member's own declared codomain,
    and [g2 : D (C I) I] is checked against [D]'s tree, in which the [X] and [Y]
    slots are parameters and therefore non-recursive.  REFUSED:

      Recursive definition of g2 is ill-formed.
      In environment
      f2 : C I
      g2 : D (C I) I
      Recursive call on a non-recursive argument of constructor
      "f2".
      Recursive definition is: "dc (C I) I f2 (ic f2)".

    So the per-member lookup exists and is correct.  Nesting is what skips it. *)

Fail CoFixpoint f2 : C I := cc I f2 g2
with g2 : D (C I) I := dc (C I) I f2 (ic f2).

(** ** 2 — still nested, but the recursive call names the inner cofixpoint.

    Two tokens from the exhibit: [cycle] becomes [f], twice.  The shape, the
    types, the infinite regress and the [ic] in the [Y] slot are all unchanged.
    But [f] is a binding of the *inner* block, and the inner block gets its own
    correct per-member check — so the refusal is immediate, and it is the
    refusal the exhibit should have got:

      Recursive definition of g is ill-formed.
      In environment
      cycleB : C I
      f : C I
      g : D (C I) I
      Recursive call on a non-recursive argument of constructor
      "f".
      Recursive definition is: "dc (C I) I f (ic f)".

    This is the load-bearing control.  It shows the defect is not "nested mutual
    cofixpoints are unchecked" — they are checked, correctly — but precisely
    that the OUTER block's walk re-uses its own tree for members that are not
    its own. *)

Fail CoFixpoint cycleB : C I :=
  (cofix f : C I := cc I f g
   with g : D (C I) I := dc (C I) I f (ic f)
   for f).

(** ** 3 — the [with] clause deleted, its body inlined into the main member.

    One nested [cofix], one member, no mutual block; [g]'s body written where
    [g] was used.  The main member's declared type is [C I], the same as the
    outer cofixpoint's, so the outer tree is now the RIGHT tree for it — and it
    immediately catches what the mutual arrangement let through, naming the
    offending subterm:

      Recursive definition of cycleC is ill-formed.
      In environment
      cycleC : C I
      f : C I
      Recursive call on a non-recursive argument of constructor
      "ic cycleC".
      Recursive definition is:
      "cofix f : C I := cc I f (dc (C I) I cycleC (ic cycleC))".

    Nesting alone is therefore not the trigger either.  Being a member of a
    nested mutual block whose declared type differs from the outer one is. *)

Fail CoFixpoint cycleC : C I :=
  (cofix f : C I := cc I f (dc (C I) I cycleC (ic cycleC))).

(** ** 4 — the baseline: no nesting at all.

    The plainest way to write the same intent.  REFUSED, with the same message
    as §3:

      Recursive definition of cycleD is ill-formed.
      In environment
      cycleD : C I
      Recursive call on a non-recursive argument of constructor
      "ic cycleD".
      Recursive definition is: "cc I cycleD (dc (C I) I cycleD (ic cycleD))". *)

Fail CoFixpoint cycleD : C I := cc I cycleD (dc (C I) I cycleD (ic cycleD)).

(** ** 5 — the positive control: the same shape, honestly.

    A nested mutual [cofix] with a non-main member and an outer recursive call
    inside it — structurally the exhibit — but both nested members declare the
    outer cofixpoint's own type, so the one shared rectree really is each
    member's own.  ACCEPTED, and rightly: [zeros] is productive, and
    [Eval compute] gets a [nat] out of it.

    This is what keeps the finding honest.  The defect is not "the outer tree is
    reused" — reuse is correct whenever the types agree, and PR #22392's remedy
    of forbidding outer recursive calls in non-main members is therefore
    stricter than the [False] requires, which its author says outright.  The
    defect is reuse across a *type change*, and §1–§4 above are what happens
    when the type changes.

    Expected: [Closed under the global context], then [= 0 : nat]. *)

CoInductive Str : Type := scons : nat -> Str -> Str.

CoFixpoint zeros : Str :=
  (cofix a : Str := scons 0 b
   with b : Str := scons 0 zeros
   for a).

Print Assumptions zeros.

Definition tl (s : Str) : Str := match s with scons _ t => t end.
Definition hd (s : Str) : nat := match s with scons n _ => n end.

Eval compute in (hd (tl (tl zeros))).
