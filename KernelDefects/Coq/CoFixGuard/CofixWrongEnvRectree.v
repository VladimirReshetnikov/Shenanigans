(** * rocq#22386 — a cofixpoint's recursive tree is computed in the wrong environment

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit code 0, with a clean audit on
    every channel this repository has.

    Category (per ../../README.md and CATALOG.md §1.3): **IMPLEMENTATION
    DEFECT**, live on the installed toolchain — category (a) of the four, a
    closed proof of [False] the kernel accepts with the audit reporting nothing.
    No flag, no axiom, no [Require] of anything, no hand-edited [.vo], no
    metaprogramming.  Nine lines of ordinary source.

    ** Provenance

    [rocq-prover/rocq#22386](https://github.com/rocq-prover/rocq/issues/22386),
    "Cofixpoint recursive tree computed in wrong environment", filed 2026-08-20
    by `yannl35133` (Yann Leray), labelled `kind: inconsistency` +
    `part: cofixpoints`, **OPEN**.  Fix PR
    [#22388](https://github.com/rocq-prover/rocq/pull/22388), "Compute rectrees
    for cofixpoints in the right environment", also **open**, milestone 9.3.0,
    approved by `SkySkimmer`.

    The issue body does not claim the finding: *"Found by an LLM and @dselsam ;
    feel free to open these issues directly."*  It is one of the nine
    `kind: inconsistency` issues Rocq received in fifty-five minutes on
    2026-08-20, filed by two maintainers on behalf of an outside reporter the
    bodies name.  Provenance write-up:
    ../../../Reports/2026-08-20-rocq-august-wave.md.

    ** The defect, and why it is the cofixpoint twin of rocq#21839

    This is the most interesting thing about it, so it goes first.
    ../GuardChecker/WrongEnvReduction.v is rocq#21839, *"Incorrect environment
    passed to reduction during guard checking"* — the strongest Rocq exhibit in
    this catalog.  There, [subterm_specif] reduced a term under an environment
    in which the term's local [let] bindings were not the ones in scope, and
    concluded that a non-smaller value was a structural subterm.  **This is the
    same mistake, one binder-kind over.**  Both are a de Bruijn context that is
    off by a fixed amount; both are triggered by local [let] bindings — the one
    binder kind whose body a reduction will unfold, so a shifted lookup finds
    something plausible instead of getting stuck; both leave a well-typed term
    whose only lie is its guardedness; and both are
    therefore invisible to [Print Assumptions] *and* to [rocqchk].  The pair is
    worth stating as a pair, and the tracker states it too: #21839 carries
    `part: fixpoints`, #22386 carries `part: cofixpoints`, and the environment
    is wrong in both.

    The provenance of the pair is its own small fact.  Both issues were filed by
    the same maintainer, `yannl35133`, four months and three weeks apart —
    #21839 on 2026-03-30 with *"PR coming soon"* and no attribution, so found
    in-house; #22386 on 2026-08-20 credited to an outside reporter.  Two
    auditing efforts arrived at the same mistake in the same file, from opposite
    directions, without either citing the other.

    Mechanism, from PR #22388's diff — **inspection of the patch**, not
    measurement; the boundary measurement that confirms it is in the controls
    file.  [kernel/inductive.ml]'s [check_cofix] builds

        let fixenv = push_rec_types recdef env in
        try check_one_cofix ?evars fixenv nbfix bodies.(i) types.(i)

    — [env] extended with one binding per member of the block — and
    [check_one_cofix] then does [codomain_is_coind ?evars env deftype] on *that*
    environment.  But [types.(i)] is a term of [env], not of [fixenv]: read
    there, every de Bruijn index inside it is [nbfix] slots too small.  When the
    declared type is a plain constant nothing happens, because constants carry
    no indices.  When it is a [let]-bound alias, the lookup **silently succeeds
    against a different binding**, and [WfPaths.lookup_subterms] hands the guard
    check the recursive tree of whatever coinductive type that other binding
    named.  PR #22388 hoists the two lines into [check_cofix], where the right
    environment is in scope, and passes the tree down:

        +        let ((mind, _),_) = codomain_is_coind ?evars env types.(i) in
        +        let vlra = WfPaths.lookup_subterms env mind in
        +        check_one_cofix ?evars fixenv nbfix bodies.(i) vlra

    In the construction below [actual] is [Rel 2] and [decoy] is [Rel 1] where
    the [cofix] sits.  The block has one member, so [fixenv] pushes one binding
    and [Rel 2] there is [decoy] — which [whd_all] unfolds to [Stream].
    [Stream] is coinductive with a single unary constructor, so the check runs
    against [Stream]'s tree, and [wrap recur] — the single unary constructor of
    the *inductive* [Empty] — is accepted as a guarded corecursive call.  The
    declared type never changed: [cycle] is an infinite inhabitant of an
    inductive type, and the ordinary structural [absurd] walks it forever.

    The second [let] is not decoration.  Delete it and the shifted lookup lands
    on [recur] itself, and 9.2 refuses with [The codomain is "recur"] — the
    kernel stating the defect in its own words.  See
    CofixWrongEnvRectreeControls.v, which brackets the shift from both sides and
    measures it to be exactly [nbfix].

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

    Nothing reports anything, twice over, on the current stable release and on
    the previous one.  [rocqchk] misses it for the reason CATALOG.md §4.7
    already records for #21839: at 9.2 the checker type-checks bodies with the
    kernel's own [Typeops.infer], so it re-runs the very code that failed and is
    not an independent implementation of it.  The [-o] line for unsafe
    (co)fixpoints is not broken — CofixWrongEnvRectreeControls.v §7 makes the
    same shape print [cycleU is assumed to be guarded.] and makes [rocqchk -o]
    list it.  **The reporting channel exists and works; #22386 simply does not
    reach it.**

    ** How far back, by inspection

    [kernel/inductive.ml] at V8.4pl6, V8.9.1, V8.12.2, V8.16.1, V8.20.1, V9.0.0
    and V9.2.0 all carry the same two lines —
    [let ((mind, _),_) = codomain_is_coind env deftype] inside
    [check_one_cofix], reached from [try check_one_cofix fixenv nbfix bodies.(i)
    types.(i)].  Only argument lists move across that range: [?evars] joins
    [codomain_is_coind] and [check_one_cofix] at V8.20.1, a [cache] parameter
    joins [check_one_cofix] at V9.2.0, and at V8.4pl6 the destructuring is one
    level shallower — [let (mind, _) = codomain_is_coind env deftype] — because
    [codomain_is_coind] did not yet return a universe instance.  The call site
    and the environment it passes are identical at all seven tags.
    **Inspection, not measurement**, for every tag but the two in
    the table.  Unlike most of CATALOG.md §4.1 this is not a regression from a
    recent refactor: nothing introduced it, and PR #22388 is the first time the
    lines move.

    ** Escape

    CofixWrongEnvRectreeEscape.v is ordinary Rocq that only [Require]s this file
    and derives [1 = 2], accepted with its own clean [Print Assumptions] and its
    own clean [rocqchk].  So this joins #21839 in the small set where **both**
    audit channels report nothing **and** the [False] propagates.

    Companion exhibit: NestedMutualCofixRectree.v (rocq#22389), the other
    cofixpoint issue of the same hour, which loses the same invariant by a
    different route. *)

(** ** The construction, verbatim from rocq#22386.

    [Stream] is the decoy's type and is otherwise unused; [Empty] is an ordinary
    inductive type with one constructor, so it is uninhabited. *)

CoInductive Stream : Type := next : Stream -> Stream.
Inductive Empty : Type := wrap : Empty -> Empty.

Definition cycle : Empty :=
  let actual := Empty in
  let decoy := Stream in
  cofix recur : actual := wrap recur.

Fixpoint absurd (x : Empty) : False :=
  match x with wrap y => absurd y end.

Definition contradiction : False := absurd cycle.

(** [Closed under the global context] *)
Print Assumptions contradiction.

(** ** Everything follows, still with a clean audit. *)

Definition one_eq_two : 1 = 2 := match contradiction return 1 = 2 with end.
Print Assumptions one_eq_two.
