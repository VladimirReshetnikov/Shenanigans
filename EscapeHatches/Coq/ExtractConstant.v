(** * Extraction: [Extract Constant] replaces a verified function with OCaml
      that nothing checks

    Category (see ../../README.md): ESCAPE HATCH.  The [False] here is *not*
    inside Rocq -- everything Rocq proves in this file is true, and
    [Print Assumptions] is right to say so.  What breaks is the sentence people
    actually mean by "verified program": that the *extracted* program satisfies
    the theorem proved about the Coq function.  [Extract Constant] severs the
    two, and no audit in Rocq -- not [Print Assumptions], not [coqchk] -- says a
    word about it.

    This is the honest Rocq counterpart of Lean's [@[implemented_by]], and the
    comparison is not symmetric.  Lean's [@[implemented_by]] + [native_decide]
    lets the compiled answer flow back into a *proof*, and pays for it with a
    fresh per-use axiom in [#print axioms] (../Lean/NativeDecide.lean).  Rocq's
    extraction cannot make Rocq believe anything -- and correspondingly emits no
    audit entry at all, because from Rocq's point of view nothing happened.  The
    cost is real and is paid entirely outside the system, by whoever runs the
    binary.

    The refman states the rule this file measures, verbatim, under
    [Extract Constant]: the replacement text "is not checked at all by
    extraction, even for syntax errors".  Section 4 turns that sentence into an
    exit code.

    Toolchain: The Rocq Prover 9.2 (compiled with OCaml 4.14.2).  The OCaml
    round trip -- extract, compile, run, compare -- is
    ./ExtractConstant.driver.ml, driven by ../verify.ps1.  Compile this file
    WITHOUT [-Q]: [coqc -Q . ""] suppresses [Print] output. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
Import ListNotations.

Extraction Language OCaml.

(** Two shipped Stdlib mapping modules and one line from the refman.  Nothing
    in this block is exotic and none of it is ours; [ExtrOcamlNatInt] is
    discussed in section 3. *)
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
Extract Inductive list => "list" [ "[]" "( :: )" ].

(** ** 1. The minimal disagreement

    Deliberately the same shape as ../Lean/NativeDecide.lean section 1: two
    different booleans, one for the logic and one for the machine. *)

Definition secret : bool := false.

(** The kernel's answer, by delta-reduction.  This is a real theorem and it
    stays a real theorem for the whole file. *)
Theorem secret_false : secret = false.
Proof. reflexivity. Qed.

(** The machine's answer.  Note what this is *not*: not a claim, not an axiom,
    not a proof obligation.  It is a string. *)
Extract Constant secret => "true".

(** ** 2. A verified safety property that the extracted program violates

    [nth_safe] is the shape people write when they want the type to carry a
    bounds guarantee: the [option] is the obligation, and [nth_safe_in_range]
    says that a [Some] answer certifies the index was in range.

    The replacement returns [Some 0] for *every* index.  It does not raise, so
    there is no crash to notice: the extracted program simply reports a
    successful, in-range lookup that never happened. *)

Definition nth_safe (l : list nat) (i : nat) : option nat := nth_error l i.

Theorem nth_safe_in_range :
  forall l i x, nth_safe l i = Some x -> i < length l.
Proof.
  intros l i x H. unfold nth_safe in H.
  apply nth_error_Some. rewrite H. discriminate.
Qed.

Theorem nth_safe_out_of_range :
  forall l i, length l <= i -> nth_safe l i = None.
Proof.
  intros l i H. unfold nth_safe. apply nth_error_None. exact H.
Qed.

Extract Constant nth_safe => "(fun l i -> Some (try List.nth l i with _ -> 0))".

(** ** 3. The shipped hatch: [nat] as [int]

    Sections 1 and 2 need the user to write [Extract Constant].  This one does
    not.  [ExtrOcamlNatInt] is a Stdlib module whose entire content is
    [Extract Inductive nat => int] plus [Extract Constant] realizers for the
    arithmetic -- including [Extract Inlined Constant Compare_dec.leb => "(<=)"],
    which is what [grows] below picks up.  The refman recommends it for
    performance.  It is unsound for programs in exactly the same way, because
    Rocq's [nat] is unbounded and OCaml's [int] is 63-bit.

    The module says so, in a source comment: "Since [int] is bounded while
    [nat] is (theoretically) infinite, you have to make sure by yourself that
    your program will not manipulate numbers greater than [max_int]."  That
    sentence is the entire safety argument, it is not machine-checkable, and it
    is not reproduced anywhere the consumer of a [.vo] will see it.

    [grows] is total and terminating, its theorem is [Nat.leb_le] plus
    [Nat.le_succ_diag_r], and no [Extract Constant] of ours touches it.  The
    extracted [grows max_int] is [false]. *)

Definition grows (n : nat) : bool := Nat.leb n (S n).

Theorem grows_true : forall n, grows n = true.
Proof. intro n. unfold grows. apply Nat.leb_le. apply Nat.le_succ_diag_r. Qed.

(** ** 4. "not checked at all by extraction, even for syntax errors"

    The refman's claim is exact.  [junk] is spliced verbatim into the emitted
    [.ml]; [coqc] exits 0; the first thing in the toolchain that objects is
    [ocamlc], several steps later, in a file the user did not write. *)

Definition junk : bool := false.
Extract Constant junk => "let let let ( ( ( ".

(** ** 5. What the audit reports

    Nothing.  All four theorems are closed under the global context, and they
    are *correct* to be -- each is a true statement about the Coq function. *)

Print Assumptions secret_false.
Print Assumptions nth_safe_in_range.
Print Assumptions nth_safe_out_of_range.
Print Assumptions grows_true.

(** The only place in the entire system that mentions [secret] is a printing
    command about *inlining*.  [Extract Constant] marks its target [NoInline] as
    a side effect, so the constant's name escapes here -- but the replacement text
    does not, and neither does the fact that there is one.  There is no
    [Print Extraction Constant]; the [Foreign] table is a different feature and
    is empty.

    Expected below: an [Extraction Inline:] block and an [Extraction NoInline:]
    block, both dominated by [ExtrOcamlNatInt]'s own entries, with [junk],
    [nth_safe] and [secret] filed among them in alphabetical rather than source
    order; and an empty [Extraction Foreign Constant:].  Note what this means
    for auditing by inspection: our three entries are indistinguishable from
    the fourteen the shipped module contributed. *)

Print Extraction Inline.
Print Extraction Foreign.

(** [coqchk] is no better, and this is the sharper half.  ../verify.ps1 runs
    [coqchk -o ExtractConstant] on the [.vo] this file produces and asserts
    [* Axioms: <none>] alongside [Modules were successfully checked].  Compare
    ../../CATALOG.md section 4.7: [coqchk] *rejects* a [.vo] built with
    [Unset Universe Checking] and *reports* the other two typing flags.  It has
    no opinion about extraction at all, because extraction is not part of the
    kernel's data -- it is a plugin table that rides along in the [.vo]. *)

(** ** 6. Emitting the two programs

    Two separate targets, because [ExtractConstant_junk.ml] does not compile and
    would take the good one down with it.  ../verify.ps1 asserts:

      - [ocamlfind ocamlopt] accepts [ExtractConstant_payload.ml] and the
        resulting binary prints the three disagreements;
      - [ocamlfind ocamlc] REJECTS [ExtractConstant_junk.ml] with
        [Error: Syntax error].

    That rejection is the control for section 4.  The OCaml compiler is the only
    checker anywhere in this pipeline; it fires here, and sections 1, 2 and 3
    are exactly the cases where it does not fire, because a lie that typechecks
    is still a lie. *)

Extraction "ExtractConstant_payload.ml" secret nth_safe grows.
Extraction "ExtractConstant_junk.ml" junk.

(** ** 7. Controls

    Rule 6 of ../../README.md: acceptance means nothing without a
    deliberately-broken twin that the same procedure rejects.  There are three,
    and together they mark out exactly where the checking stops.

    Control A -- the Coq side holds.  The disagreement of section 1 is not
    reachable inside Rocq: [secret] is [false] and stays [false].  If a [.v]
    file could assert the extracted behaviour, this file would belong in
    ../../KernelDefects/ instead. *)

Fail Definition secret_true : secret = true := eq_refl.

(** Control B -- extraction does check that the *Coq* name resolves.  Measured:
    this is the entire extent of the validation applied to an
    [Extract Constant]. *)

Fail Extract Constant no_such_constant_anywhere => "true".

(** Control C -- [Extract Inductive] checks the constructor *count*, so the
    mechanism is not incapable of checking things.  It just never looks at the
    OCaml. *)

Fail Extract Inductive bool => "bool" [ "true" ].

(** ** 8. Three measurements that are not in the manual

    (a) Argument slots are not checked either.  [Extract Constant f "a" "b" "c"]
        on a two-argument [f] is accepted and emits a three-argument body under
        a two-argument signature.  Only [ocamlc] notices.

    (b) A second [Extract Constant] for the same constant silently wins, with no
        warning and no way to see the shadowed one.  So "which OCaml is my
        verified function replaced by" is answered by the last [Require] to
        express an opinion.

    (c) The customization is an ordinary library object.  It is stored in the
        [.vo] and is in force for every consumer, transitively.
        ./ExtractConstantDownstream.v [Require]s this file and extracts
        [secret] with no [Extract Constant] of its own -- and gets
        [let secret = true].  A dependency can therefore choose the OCaml your
        verified program is built from, and your [Print Assumptions] will be
        clean.

    (a) and (b) are demonstrated in ./ExtractConstantUnchecked.v; (c) is
    ./ExtractConstantDownstream.v.  ../verify.ps1 compiles and greps both. *)

(** ** What this file settles

    * The Coq-side theorems [secret_false], [nth_safe_in_range],
      [nth_safe_out_of_range] and [grows_true] are true, closed and axiom-free,
      and remain so.  Nothing here is a defect in Rocq, which is why the file
      is in this directory and not in ../../KernelDefects/.
    * The extracted OCaml contradicts three of them, observably:
      ./ExtractConstant.driver.ml exits nonzero unless it sees [secret = true],
      [nth_safe [1;2;3] 99 = Some 0] and [grows max_int = false].
    * [Print Assumptions] reports nothing, [coqchk] reports nothing, and the
      only trace anywhere is a [NoInline] entry naming the constant but not the
      replacement.
    * What is lost is not consistency -- it is the *refinement* between the Coq
      function and the binary, the step on which every "verified software"
      claim depends and which no proof assistant checks.  CompCert, the
      flagship extraction-based verified program, states this boundary itself
      and keeps its [Extract Constant] list short and reviewed for exactly this
      reason. *)
