(** * Companion to ./ExtractConstant.v, section 8(a) and 8(b): two things the
      manual does not say are unchecked

    Category: ESCAPE HATCH (../../README.md).  Toolchain: Rocq 9.2.
    Driven by ../verify.ps1, which asserts [coqc] exit 0 and both emitted
    strings.

    (a) ARGUMENT SLOTS ARE NOT CHECKED.  [Extract Constant f "a" "b"] is the
        documented way to name a constant's arguments so the replacement can
        refer to them.  Supplying three slots for a two-argument function is
        accepted, and the emitted body has three parameters under a
        two-parameter signature.  [ocamlc] is the first thing to object.

    (b) A SECOND [Extract Constant] SILENTLY WINS.  There is no warning, no
        error, and no way to see the shadowed replacement.  Combined with
        ./ExtractConstantDownstream.v -- where the declaration arrives from a
        [Require] -- this means the answer to "which OCaml is my verified
        function replaced by?" is decided by [Require] order, invisibly. *)

From Stdlib Require Import Extraction List Arith.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlBasic.
Extract Inductive list => "list" [ "[]" "( :: )" ].

(** ** (a) Three slots for a two-argument function *)

Definition pick (l : list nat) (i : nat) : option nat := nth_error l i.

Extract Constant pick "l" "i" "x" => "(fun l i x -> None)".

(** Emits, under the signature [nat list -> nat -> nat option]:
      [let pick = (fun l i x -> None)] *)
Extraction "ExtractConstant_arity.ml" pick.

(** ** (b) Last declaration wins, silently *)

Definition flag : bool := false.

Extract Constant flag => "true".
Extract Constant flag => "false".

(** Emits [let flag = false].  The [true] is gone without a trace; even
    [Print Extraction Inline] shows only that [flag] is [NoInline]. *)
Extraction "ExtractConstant_shadow.ml" flag.

Print Extraction Inline.

(** ** The control for this file

    The mechanism is not incapable of checking.  It checks the Coq name, and
    [Extract Inductive] checks the constructor count.  Both refusals are
    machine-checked in ./ExtractConstant.v section 7. *)
