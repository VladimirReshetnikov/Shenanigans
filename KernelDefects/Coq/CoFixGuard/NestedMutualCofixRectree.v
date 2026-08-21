(** * rocq#22389 — every member of a nested mutual cofixpoint is checked with the same rectree

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit code 0, with a clean audit on
    every channel.

    Category (per ../../README.md and CATALOG.md §1.3): **IMPLEMENTATION
    DEFECT**, live on the installed toolchain — category (a), a closed proof of
    [False] the kernel accepts with the audit reporting nothing.  No flag, no
    axiom, no hand-edited [.vo].

    ** Provenance

    [rocq-prover/rocq#22389](https://github.com/rocq-prover/rocq/issues/22389),
    "Nested mutual cofixpoint all checked with the same rectree", filed
    2026-08-20 by `yannl35133` (Yann Leray), labelled `kind: inconsistency` +
    `part: cofixpoints`, **OPEN**.  Fix PR
    [#22392](https://github.com/rocq-prover/rocq/pull/22392), "Forbid recursive
    calls in nested cofixpoints outside of the main branch", also **open**.
    Filed at 13:22:35Z, six minutes after its sibling #22386 (13:16:30Z), by
    the same maintainer and with the same credit line — *"Found by an LLM and
    @dselsam ; feel free to open these issues directly."*  The nine
    `kind: inconsistency` issues of that day span 12:31:00Z to 13:26:25Z.

    ** Why this is a second exhibit and not the same one from another angle

    The question is worth answering explicitly, because #22386 and #22389 land
    six minutes apart, in the same file, in the same function family, and both
    end with an infinite inhabitant of an inductive type.  The shared invariant
    is real and worth naming:

        every [cofix] body must be checked against the recursive tree of ITS
        OWN declared codomain.

    #22386 and #22389 are two different ways of losing it.  But they are two,
    not one, and four things say so.  The first two bullets are **inspection of
    [kernel/inductive.ml] at V9.2.0 and of the two PR diffs, not measurement**;
    the fourth is measured, in NestedMutualCofixRectreeControls.v:

      - **Different code.**  #22386 is [check_cofix]'s call site — the tree is
        looked up in [fixenv] instead of [env].  #22389 is inside
        [check_one_cofix]'s [check_rec_call], the [CoFix] branch: when the body
        being walked *contains* a nested mutual block, that branch does
        [Array.iter (check_rec_call env' alreadygrd (n+nbfix) tree) vdefs] —
        every member against [tree], the tree of the OUTER cofixpoint.  No tree
        is ever looked up for the inner members at all.
      - **Different fix.**  PR #22388 moves two lines.  PR #22392 rewrites the
        branch, adds a *new kernel error constructor*
        ([RecCallInNonMainMutual], in [kernel/type_errors.ml] and
        [.mli]) and a new message in [vernac/himsg.ml].  #22392's diff shows
        [check_one_cofix ?evars env nbfix def deftype] still taking [deftype] —
        it branches from before #22388 — so the two patches are independent, not
        one split in half.
      - **Different kind of mistake.**  #22386 is a slip with an obvious right
        answer: read the type in the environment it belongs to.  #22389 is a gap
        in the *criterion*, not its implementation.  #22392 does not compute the
        right tree per member; it forbids the shape.  Its author says so:
        *"Simply forbids recursive call of an outer cofixpoint in a nested
        mutual cofixpoint, for branches other than the main one"*, which is
        *"more drastic that really necessary"* — upstream's wording, quoted
        exactly, [that] for [than] — *"but the theory needs to be improved
        before we have a proper criterion that would allow them again."*
      - **Different controls.**  #22386's twins are refused with
        [The codomain is "..."]; this one's are refused with
        [Recursive call on a non-recursive argument of constructor].  Nothing in
        the control set overlaps.

    So: same directory, same invariant, two exhibits.

    ** The mechanism

    [C A] is coinductive and [I] is an ordinary inductive type *nested through
    it* — [ic : C I -> I], which Rocq permits.  A [C I] value therefore carries
    one [I] per unfolding, in the [Y] slot of [D (C I) I].  The consistency of
    that arrangement rests entirely on the cofix guard check refusing to put a
    corecursive call in the [Y] slot, because [Y] is a *parameter* of [D] and so
    a **non-recursive** position of [D]'s tree.

    The account of the rectree alignment in the next paragraph is **inspection
    of [kernel/inductive.ml] at V9.2.0**, not measurement; what is measured is
    the outcome — acceptance here, and the four refusals of
    NestedMutualCofixRectreeControls.v §1–§4, all of which report
    [RecCallInNonRecArgOfConstructor], the error this body avoids.

    In the construction below the outer [CoFixpoint cycle : C I] has a nested
    mutual block [cofix f : C I := ... with g : D (C I) I := ... for f].  The
    outer check walks the body carrying [tree] = the tree of [C], correct for
    [f], and applies it to [g] as well.  Read against [C]'s tree the two real
    arguments of [dc] line up with the two arguments of [cc] — [C A] and
    [D (C A) A], **both recursive** — so [ic cycle], which is [g]'s [Y] slot and
    an inductive value, is accepted as a guarded corecursive position.  The
    structural [empty] then walks the resulting infinite chain of [I]s forever.

    The inner block is *not* the problem, and this is the sharpest part: the
    kernel does check it, separately and correctly, with [g] against [D]'s own
    tree.  It passes honestly, because the offending occurrences name [cycle] —
    a binding of the *outer* block — and so are invisible to the inner check.
    Rename them to [f] and the inner check refuses at once.  That is control §2
    of NestedMutualCofixRectreeControls.v, and it is two tokens.

    ** Measured — the full audit surface, on two installed toolchains

    | Channel                                | 9.2 (OCaml 4.14.2) | 9.0.1 Platform |
    | -------------------------------------- | ------------------ | -------------- |
    | [coqc] on this file                    | exit 0             | exit 0         |
    | [Print Assumptions contradiction]      | Closed under the global context | same |
    | [rocqchk], default                     | exit 0, [Modules were successfully checked] | same |
    | [rocqchk -bytecode-compiler yes]       | exit 0             | exit 0         |
    | [rocqchk -o]: Axioms                   | [<none>]           | [<none>]       |
    | [rocqchk -o]: type-in-type             | [<none>]           | [<none>]       |
    | [rocqchk -o]: unsafe (co)fixpoints     | [<none>]           | [<none>]       |
    | [Require] of the [.vo] downstream      | exit 0, clean      | exit 0, clean  |

    Measured separately: a downstream file that only [Require]s this one derives
    [2 + 2 = 5] at exit 0 with two clean [Print Assumptions] lines and a clean
    [rocqchk -o].  The escape is exhibited once, for the sibling, in
    CofixWrongEnvRectreeEscape.v; it behaves identically here.

    ** How far back, by inspection

    [kernel/inductive.ml] at V8.4pl6, V8.9.1, V8.12.2, V8.16.1, V8.20.1, V9.0.0
    and V9.2.0 all carry the same three lines,

        let nbfix = Array.length vdefs in
        let env' = push_rec_types recdef env in
        (Array.iter (check_rec_call env' alreadygrd (n+nbfix) tree vlra) vdefs; ...

    with only the [tree]/[vlra] argument list changing across the range.
    **Inspection, not measurement**, for every tag but the two in the table.
    Like #22386 this is not a regression from a recent refactor.

    ** Note on output

    **On 9.2 only**, [Inductive I] draws twelve copies of a warning — *"I is
    nested using C. No scheme for C is registered as All. It can be generated
    using command "Scheme All" e.g. "Scheme All for C.". [register-all,
    automation,default]"* — which is about derived scheme registration and has
    nothing to do with the finding.  Rocq 9.0.1 emits it zero times; measured,
    both toolchains.  So the two compilations agree on exit code, on both
    [Print Assumptions] lines and on every [rocqchk] row of the table above,
    and differ only in this warning.  It is left unsilenced rather than
    suppressed, because this file takes no flags.
    NestedMutualCofixRectreeControls.v repeats the same three declarations and
    so draws the same twelve warnings, for the same reason. *)

(** ** The construction, verbatim from rocq#22389. *)

CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
Inductive I : Type := ic : C I -> I.

CoFixpoint cycle : C I :=
  (cofix f : C I := cc I f g
   with g : D (C I) I := dc (C I) I cycle (ic cycle)
   for f).

Fixpoint empty (i : I) : False :=
  match i with
  | ic c => match c with
    | cc _ _ d => match d with
      | dc _ _ _ j => empty j
      end
    end
  end.

Definition contradiction : False := empty (ic cycle).

(** [Closed under the global context] *)
Print Assumptions contradiction.

(** ** Everything follows, still with a clean audit. *)

Definition one_eq_two : 1 = 2 := match contradiction return 1 = 2 with end.
Print Assumptions one_eq_two.
