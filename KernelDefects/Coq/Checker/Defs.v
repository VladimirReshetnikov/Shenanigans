(** * The honest source both halves of the splice are compiled from

    rocq#22352.  This file is compiled TWICE by ../verify.ps1 — once as written,
    and once with [idb true] rewritten to [idb false].  The two .vo files differ
    only in this constant's value, and therefore have byte-identical [opaques]
    and [summary] segments; that is what makes the splice produce a well-formed
    object file rather than a corrupt one.

    [splice.py] then takes the FIRST file's [library] segment (the body:
    [poc_evil = true]) and the SECOND file's [vmlibrary] segment (the compiled
    bytecode: [poc_evil = false]) and writes them into one .vo.  Nothing else is
    edited, and no patched tool is involved anywhere.

    [-noinit] and the local [bool] keep the exhibit self-contained: no [Stdlib],
    no [Require] but our own, and a [bool] whose two constructors are the ones
    the paradox distinguishes. *)

Unset Elimination Schemes.

Inductive bool : Set := true | false.

Definition idb (b : bool) : bool := b.

(** The one constant the two compilations disagree about. *)
Definition poc_evil : bool := idb true.
