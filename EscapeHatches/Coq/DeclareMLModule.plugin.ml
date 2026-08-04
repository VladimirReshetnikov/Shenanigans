(* The plugin half of ../Coq/DeclareMLModule.v section 5.
   NOT LOADED BY ../verify.ps1.  See the honesty note below.

   Everything here runs at LOAD time -- there is no vernacular command to
   invoke, and no proof to write.  `Declare ML Module "hatch".` is the whole
   attack surface: the toplevel `let () = ...` at the bottom of this file
   executes inside coqc, before the next line of the .v file is parsed.

   -- BUILD -----------------------------------------------------------------

     ocamlfind ocamlopt -package rocq-runtime.vernac -shared \
               hatch_plugin.ml -o hatch_plugin.cmxs

   next to a findlib META:

     version       = "0.1"
     description   = "escape-hatch demonstration"
     requires      = "rocq-runtime.vernac"
     plugin(native) = "hatch_plugin.cmxs"
     plugin(byte)   = "hatch_plugin.cma"

   in a directory `hatch/` under some $DIR, then:

     OCAMLPATH=$DIR coqc user.v          where user.v begins
     Declare ML Module "hatch".

   -- STATUS ON THIS MACHINE -------------------------------------------------

   BUILDS (ocamlfind ocamlopt exit 0, against Rocq 9.2 / OCaml 4.14.2).
   DOES NOT LOAD, for a reason that is not Rocq's:

     Cannot find FLEXDLL_RELOCATE
     Error: Dynlink error: error loading shared library:
       Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"A dynamic link
       library (DLL) initialization routine failed.\")")

   Symmetric diagnosis: a standalone OCaml host built by this switch loads
   THIS .cmxs and fails on Rocq's shipped tuto0_plugin.cmxs with the identical
   error; coqc does the reverse.  `objdump -p` shows the shipped plugins import
   msvcrt.dll and ours import the UCRT api-ms-win-crt-* set -- the opam switch
   ships prebuilt rocq binaries linked against a different mingw-w64 runtime
   than its own flexlink emits.  On a from-source switch this file is expected
   to load unchanged; that expectation is NOT asserted here.

   -- WHAT IT WOULD SHOW -----------------------------------------------------

   (1) that the toplevel effect runs at all -- the banner;
   (2) that the kernel's check flags are a mutable global reachable from a
       plugin, with no vernacular involved;
   (3) that `Global.push_named_assum` puts an assumption into the kernel's
       global named context directly.  How `Print Assumptions` classifies the
       result is the open question section 5 declines to answer without a
       measurement: `vernac/assumptions.ml` emits a `Variable` for a VarRef,
       so the prediction is that it appears under `Variables:` rather than
       `Axioms:` -- i.e. under-reported as to KIND but not silent.  The
       genuinely silent variant needs `Global.reset_safe_env`, which installs
       an arbitrary `Safe_typing.safe_environment` and has no vernacular
       counterpart; it is deliberately not written here, because an unmeasured
       exploit is a claim, and this repository does not make claims it has not
       run.                                                                  *)

let banner () =
  Feedback.msg_notice
    Pp.(str "[hatch] arbitrary OCaml is running inside coqc, sharing the \
             kernel's global environment")

(* (2) The kernel's three check flags are a mutable global. *)
let report_flags () =
  let f = Global.typing_flags () in
  Feedback.msg_notice
    Pp.(str
          (Printf.sprintf
             "[hatch] check_guarded=%b check_positive=%b check_universes=%b"
             f.Declarations.check_guarded
             f.Declarations.check_positive
             f.Declarations.check_universes))

(* (3) A global assumption of type False, pushed straight into the kernel's
       named context.  No `Axiom`, no `Variable`, no vernacular at all. *)
let false_type () =
  match Rocqlib.lib_ref "core.False.type" with
  | Names.GlobRef.IndRef ind -> Constr.UnsafeMonomorphic.mkInd ind
  | _ -> CErrors.user_err (Pp.str "core.False.type is not an inductive")

let push_hypothesis () =
  Global.push_named_assum (Names.Id.of_string "hatch_hypothesis", false_type ())

let () =
  banner ();
  report_flags ();
  push_hypothesis ()
