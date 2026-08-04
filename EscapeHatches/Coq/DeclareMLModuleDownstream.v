(** * Companion to ./DeclareMLModule.v, section 4: [Require] re-links the
      plugin

    This file writes no [Declare ML Module].  It [Require]s ./DeclareMLModule.v
    and then uses [Derive], which is a vernacular command that exists only while
    [rocq-runtime.plugins.derive] is loaded.  It works -- so requiring a library
    dynamically linked that library's OCaml into *this* [coqc] process.

    [Print ML Modules] below confirms it by name.  [Print Assumptions] is clean.

    The generalisation is the one that matters: [Require]ing any library links
    that library's plugins, transitively, at every depth, with no per-package
    prompt and no manifest the consumer sees.  Which [.cmxs] a package name
    resolves to is decided by [OCAMLPATH], outside the source tree.

    Category: ESCAPE HATCH (../../README.md).  Toolchain: Rocq 9.2.
    Driven by ../verify.ps1. *)

Require Import DeclareMLModule.

Derive g in (g = 1) as Hg.
Proof. subst g. reflexivity. Qed.

Print Assumptions Hg.
Print ML Modules.
