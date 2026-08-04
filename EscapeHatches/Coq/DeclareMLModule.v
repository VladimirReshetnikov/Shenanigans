(** * [Declare ML Module]: dynamically linking OCaml into the process that runs
      the kernel

    Category (see ../../README.md): ESCAPE HATCH.  It is documented, it is how
    every tactic in Rocq that is not written in Ltac gets there -- [lia],
    [congruence], [firstorder], [Derive], extraction itself -- and it is
    unbounded.  A [.cmxs] loaded this way runs with the privileges of [coqc]
    inside [coqc]'s address space, sharing the kernel's mutable global
    environment.  Nothing about that appears in [Print Assumptions], and
    [coqchk] does not so much as read the plugin's name.

    Read this file next to ../Lean/NativeDecide.lean.  Lean's escape hatches all
    stop at a boundary: [@[implemented_by]] buys a per-use axiom in
    [#print axioms], [unsafe] is quarantined *by the kernel*, and the one Lean
    route the audit cannot see needs [set_option debug.skipKernelTC true] and is
    caught by [leanchecker].  Lean has no counterpart to this file at all --
    there is no supported way to load native code into [lean]'s process and have
    it edit the environment.  Rocq's plugin API is the single largest difference
    between the two systems' trusted computing bases, and it is the one thing in
    ../../CATALOG.md section 1.2 with no Lean row.

    Toolchain: The Rocq Prover 9.2 (compiled with OCaml 4.14.2).  Verified by
    ../verify.ps1.  Compile WITHOUT [-Q]: [coqc -Q . ""] suppresses [Print]
    output.

    HONESTY NOTE, and it is the point of section 5.  Everything asserted in
    sections 1-4 was measured on this machine with shipped plugins.  Loading a
    plugin *we wrote* was NOT achieved here, for a reason that is a property of
    this Rocq installation and not of Rocq: the [.cmxs] we build is ABI-
    incompatible with the prebuilt [rocq] binaries in this opam switch.  Section
    5 states exactly what was tried, what failed, what the failure was, and what
    it would take.  The plugin source is ./DeclareMLModule.plugin.ml. *)

(** ** 1. Loading is a vernacular command, and it extends the vernacular

    [Derive] is not part of Rocq's grammar until the line below runs.  After it,
    it is.  That is dynamically loaded native code editing the parser of the
    process that is about to typecheck your proofs. *)

Declare ML Module "rocq-runtime.plugins.derive".

Derive f in (f = 0) as Hf.
Proof. subst f. reflexivity. Qed.

(** ** 2. What the audit reports

    [Closed under the global context].  Correctly, in the narrow sense: [Hf]'s
    proof term really does depend on nothing.  The point is that the sentence
    "this theorem depends on no assumptions" is now being produced by a process
    whose behaviour was chosen, in part, by a shared library named one command
    earlier -- and [Print Assumptions] has no vocabulary for that. *)

Print Assumptions Hf.

(** The only trace anywhere is [Print ML Modules], which is a listing, not an
    audit: it names the findlib packages that happen to be loaded, says nothing
    about what any of them did, and does not distinguish the one this file asked
    for from the seven the Prelude loaded before we got here.

    Expected below, in load order: [rocq-runtime.plugins.ltac],
    [...number_string_notation], [...tauto], [...cc_core], [...cc],
    [...firstorder_core], [...firstorder], [...derive]. *)

Print ML Modules.

(** ** 3. [coqchk] does not participate

    ../verify.ps1 runs [coqchk -o DeclareMLModule] on this file's [.vo] and
    asserts [Modules were successfully checked] together with
    [* Axioms: <none>] and all four other CONTEXT SUMMARY lines empty.

    [coqchk] does not load plugins -- it is a separate binary with its own
    reduced kernel and no [Mltop] -- so it neither executes the ML module nor
    reports that one was requested.  Contrast ../../CATALOG.md section 4.7:
    [coqchk] *rejects* a [.vo] built with [Unset Universe Checking] and
    *reports* the other two typing flags.  Here there is nothing to report,
    because from the [.vo]'s point of view a plugin is a name to re-load, not a
    fact about the proof.

    Note the asymmetry this creates.  [coqchk] is the recommended backstop
    precisely for the case where you do not trust the [.v] files.  It is exactly
    the case a plugin is designed for. *)

(** ** 4. The reach: [Require] re-links the plugin into *your* process

    An ML module is recorded in the [.vo] and re-loaded transitively.
    ./DeclareMLModuleDownstream.v [Require]s this file, writes no
    [Declare ML Module] of its own, and gets [Derive] anyway -- which means it
    got the shared library, executed in its own [coqc].

    So the real statement is not "a file that loads a plugin trusts it".  It is
    that [Require]ing *any* library dynamically links that library's OCaml into
    your [coqc], transitively, at every depth, with no per-package prompt, no
    manifest the consumer sees, and no audit entry.  The findlib search path is
    the [OCAMLPATH] environment variable, so which [.cmxs] a given package name
    resolves to is decided outside the source tree entirely.

    This is the same shape as ./ExtractConstant.v section 8(c) -- a dependency
    silently choosing something about your build that your audit cannot see --
    but one level more severe, because extraction only decides what your
    *output* is, while a plugin decides what your *checker* is. *)

(** ** 5. What was not reached here, and exactly why

    The stronger claim in ../../CATALOG.md section 1.2 -- that a plugin can put
    a constant into the environment that [Print Assumptions] under-reports -- is
    NOT demonstrated by this file.  Here is the boundary, precisely.

    WHAT IS ESTABLISHED, from Rocq 9.2's own shipped sources:

      - The API is exported and unguarded.  [library/global.mli] exposes, to any
        loaded plugin, [set_typing_flags], [set_check_guarded],
        [set_check_positive], [set_check_universes], [push_named_assum],
        [add_univ_constraints], [fill_opaque] and [reset_safe_env].  The last
        takes an arbitrary [Safe_typing.safe_environment] and installs it as
        *the* global environment; it has no vernacular counterpart, so nothing a
        [.v] file can write is equivalent to it.

      - [Print Assumptions] can only see four kinds of thing.  [vernac/
        assumptions.ml] fold (lines ~368-427) emits exactly [Variable],
        [Axiom], [Opaque] and [Transparent] context objects, and it derives the
        [Theory:]/"assumed to be guarded"/"unsafe hierarchy" lines from
        [cb.const_typing_flags] -- the flags *stored on the constant*.  A
        plugin that writes a constant and then rewrites its stored
        [const_typing_flags] is therefore invisible by construction: the audit
        reads the same record the plugin just edited.  Note that this is not a
        bug.  There is no defensible alternative once arbitrary OCaml is in the
        process.

    WHAT WAS ATTEMPTED AND FAILED, on this machine:

      A minimal plugin (./DeclareMLModule.plugin.ml) was written and BUILDS
      cleanly:

        ocamlfind ocamlopt -package rocq-runtime.vernac -shared \
                  hatch_plugin.ml -o hatch_plugin.cmxs        (exit 0)

      With a two-line findlib [META] and [OCAMLPATH] pointed at it, findlib
      resolves the package and [Dynlink] is reached -- and then:

        Cannot find FLEXDLL_RELOCATE
        Cannot find FLEXDLL_RELOCATE
        Error: Dynlink error: error loading shared library:
          Dynlink.Error (Dynlink.Cannot_open_dll
            "Failure(\"A dynamic link library (DLL) initialization routine
             failed.\")")

      The diagnosis is symmetric and conclusive.  A standalone OCaml host
      compiled by this switch loads our [.cmxs] fine and FAILS on Rocq's own
      shipped [tuto0_plugin.cmxs] with the identical error; [coqc] does the
      reverse.  [objdump -p] shows why: the shipped [.cmxs] imports
      [msvcrt.dll], ours imports the UCRT [api-ms-win-crt-*] set.  The [rocq]
      binaries in this opam switch are a prebuilt distribution linked against a
      different mingw-w64 runtime than the switch's current
      [x86_64-w64-mingw32-gcc] and [flexlink] emit.  This is a Windows
      binary-distribution mismatch, not a Rocq limitation: the plugin mechanism
      demonstrably works, since section 1's [Derive] is a [.cmxs] that loaded.

    WHAT IT WOULD TAKE: a Rocq built from source in the same switch as the
    plugin (any Linux or macOS opam switch, or a Windows switch that builds
    [rocq] rather than installing a binary package), after which
    ./DeclareMLModule.plugin.ml compiles and loads unchanged.  This is left as
    a **gap** rather than claimed; see ../../CATALOG.md.

    THE STANDING OF SECTIONS 1-4 IS UNAFFECTED.  They do not need a plugin of
    ours.  What they measure is that loading OCaml into the kernel's process is
    a one-line, transitive, unaudited operation -- and that is the row in
    ../../CATALOG.md section 1.2 this file is for. *)

(** ** 6. Controls

    Rule 6 of ../../README.md.  Two, both machine-checked by this file exiting
    0, which requires both [Fail]s to succeed.

    Control A -- the package name is resolved, and a bad one is refused:
    [Findlib error: no-such-findlib-package-anywhere not found in: ...].  This
    is the *only* validation applied.  Note what is not checked: nothing about
    the [.cmxs] itself, and the search path is [OCAMLPATH]. *)

Fail Declare ML Module "no-such-findlib-package-anywhere".

(** Control B -- there is exactly one structural restriction, and it is about
    sections, not about trust: [Cannot Declare ML Module while sections are
    opened.] ([vernac/mltop.ml:468]). *)

Section AControlSection.
Fail Declare ML Module "rocq-runtime.plugins.derive".
End AControlSection.

(** ** What this file settles

    * Loading arbitrary native code into the process that runs the kernel is a
      single documented vernacular command, and it visibly changes that
      process -- [Derive] is not in the grammar before the [Declare ML Module]
      line and is after it.
    * [Print Assumptions] reports [Closed under the global context];
      [coqchk -o] reports [* Axioms: <none>] and does not mention the plugin.
      The only trace in the whole system is [Print ML Modules], a listing that
      says nothing about what was loaded or what it did.
    * The effect is transitive through [Require] and resolved through
      [OCAMLPATH], so the set of shared libraries linked into your [coqc] is a
      property of your dependency graph and your environment, not of your file.
    * The two things that ARE checked are the findlib package name and the
      section state.  Both refusals are asserted above.
    * Rocq's own maintainers agree about the standing of this hatch: it is why
      [coqchk] exists as a separate binary with its own kernel and no [Mltop].
      The gap measured in section 3 is that [coqchk] neither runs the plugin
      nor tells you one was requested -- so the recommended backstop is silent
      about the mechanism it was built to backstop. *)
