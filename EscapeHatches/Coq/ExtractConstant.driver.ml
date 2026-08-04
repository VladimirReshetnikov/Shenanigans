(* Runs the OCaml that `coqc ExtractConstant.v` produced and asserts that it
   contradicts the Coq theorems proved about the same functions.

   This file is the observable half of ./ExtractConstant.v.  It exits 0 only if
   ALL THREE disagreements are present, so a future Rocq that started checking
   `Extract Constant` would make ../verify.ps1 fail loudly rather than silently
   pass.

   Build (see ../verify.ps1):
     coqc ExtractConstant.v
     ocamlfind ocamlopt ExtractConstant_payload.mli ExtractConstant_payload.ml \
                        ExtractConstant.driver.ml -o driver.exe
     ./driver.exe                                                          *)

let failures = ref 0

(* [coq] is what the Coq theorem named in [thm] proves the value to be;
   [want] is what the extracted program is expected to produce instead. *)
let check thm ~coq ~want ~got =
  if got = want && want <> coq then
    Printf.printf "  DISAGREES  %-24s Coq: %-8s extracted: %s\n" thm coq got
  else begin
    incr failures;
    Printf.printf "  UNEXPECTED %-24s Coq: %-8s extracted: %s (wanted %s)\n"
      thm coq got want
  end

let show_opt = function None -> "None" | Some v -> "Some " ^ string_of_int v

let () =
  print_endline "extracted program vs. the theorems proved about it:";

  (* Theorem secret_false : secret = false. *)
  check "secret_false"
    ~coq:"false" ~want:"true"
    ~got:(string_of_bool ExtractConstant_payload.secret);

  (* Theorem nth_safe_out_of_range :
       forall l i, length l <= i -> nth_safe l i = None.
     99 is out of range for a 3-element list, so Coq proves None.  The
     companion Theorem nth_safe_in_range says a Some answer certifies the
     index was in range; the extracted program returns Some for index 99. *)
  check "nth_safe_out_of_range"
    ~coq:"None" ~want:"Some 0"
    ~got:(show_opt (ExtractConstant_payload.nth_safe [1; 2; 3] 99));

  (* Theorem grows_true : forall n, grows n = true.
     No Extract Constant of ours is involved here -- only the shipped Stdlib
     module ExtrOcamlNatInt. *)
  check "grows_true"
    ~coq:"true" ~want:"false"
    ~got:(string_of_bool (ExtractConstant_payload.grows max_int));

  print_newline ();
  if !failures = 0 then begin
    print_endline
      "3/3 disagreements; Print Assumptions said `Closed under the global context'";
    exit 0
  end else begin
    Printf.printf "%d of 3 disagreements were NOT observed\n" !failures;
    exit 1
  end
