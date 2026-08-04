(** * Companion to ./ExtractConstant.v, section 8(c): the replacement crosses
      a [Require] boundary

    An [Extract Constant] declaration is an ordinary library object.  It is
    written into the [.vo] and is in force for every consumer of that [.vo],
    transitively, exactly like a [Hint] or a [Notation].

    This file writes no [Extract Constant] at all.  It [Require]s
    ./ExtractConstant.v and extracts [secret] -- and gets [let secret = true],
    because the upstream file said so.  [Print Assumptions secret_false] here
    is still [Closed under the global context].

    So a dependency several levels up can choose the OCaml your verified
    program is built from, and nothing in your file, your audit output, or
    [coqchk] will mention it.  The only way to find out is to read the emitted
    [.ml], or to run [Print Extraction Inline] and notice a name you did not
    put there.

    Category: ESCAPE HATCH (../../README.md).  Toolchain: Rocq 9.2.
    Driven by ../verify.ps1, which asserts the string [let secret = true] in
    the emitted [ExtractConstant_downstream.ml]. *)

Require Import ExtractConstant.
From Stdlib Require Import Extraction.

Print Assumptions secret_false.

(** The only trace, and it is not an audit: the upstream constants appear in
    the [NoInline] table of a file that never mentioned them. *)
Print Extraction Inline.

Extraction "ExtractConstant_downstream.ml" secret.
