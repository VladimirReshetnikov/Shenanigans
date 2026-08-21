(** * Controls for CofixWrongEnvRectree.v — the kernel states the defect in its own words

    rocq#22386.  Ground rule 6: an exhibit without a load-bearing control is
    worthless.  Acceptance of the exhibit means nothing unless the *same*
    procedure on the *same* toolchain rejects deliberately-broken twins, and
    unless the audit that is silent there is shown to be working everywhere
    else.

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit 0.  Every refusal below is
    wrapped in [Fail], so a control that stopped refusing would fail the file.

    These controls are unusually good, and the reason is that the guard checker
    **prints the wrong environment's answer**.  Its error message names the
    binding it actually read, so §3 and §4 below do not merely refuse — they
    display the defect: the environment banner says [recur : actual] one line
    above [The codomain is "decoy"].

    Seven controls, all measured on Rocq 9.2 (OCaml 4.14.2) **and** on Rocq
    9.0.1 (Rocq Platform 9.0~2025.08, driven with
    [-coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"]).  Every verdict and every
    message below is byte-identical on the two.  Each refusal was re-derived by
    stripping the single [Fail] in front of it and capturing [coqc]'s output,
    one control at a time, on each toolchain — not inferred from the file
    compiling.  Expected output of the file itself, in order:
    [Closed under the global context] from §6', then §7's two-line
    [Axioms: / cycleU is assumed to be guarded.]  Nothing else.

    | # | Arrangement                                   | Verdict  | The kernel says |
    | - | --------------------------------------------- | -------- | --------------- |
    | 1 | no [let] at all                               | REFUSED  | [The codomain is "Empty"] |
    | 2 | [Definition] aliases instead of [let]         | REFUSED  | [The codomain is "Empty"] |
    | 3 | one [let], no decoy                           | REFUSED  | [The codomain is "recur"] |
    | 4 | the gap binding is a [fun], not a [let]       | REFUSED  | [The codomain is "decoy"] |
    | 5 | the gap [let] binds an *inductive* type       | REFUSED  | [The codomain is "nat"] |
    | 6 | two cofixpoints, ONE gap [let]                | REFUSED  | [The codomain is "r1"] |
    | 6'| two cofixpoints, TWO gap [let]s               | ACCEPTED | [Closed under the global context] |
    | 7 | the same shape under [Unset Guard Checking]   | ACCEPTED | [cycleU is assumed to be guarded.] |

    §6 and §6' are the finding this file adds to upstream's report, which does
    not narrow the trigger at all: the lookup is off by **exactly [nbfix]**, the
    number of members in the [cofix] block.  One member needs one gap binding;
    two members need two, and are refused with one.  That brackets the shift
    from both sides and pins it to a quantity, which is a stronger statement
    than "a [let] is needed".

    §7 is the other half of ground rule 6, in the direction the audit cares
    about: it proves the [Print Assumptions] and [rocqchk -o] channels that stay
    silent on the exhibit are alive and correct on the same construction reached
    honestly. *)

CoInductive Stream : Type := next : Stream -> Stream.
Inductive Empty : Type := wrap : Empty -> Empty.

(** ** 1 — the plain form, with no [let] anywhere.

    A [cofix] whose declared type is written out is refused, because [Empty] is
    inductive.  This is the check working.  REFUSED:

      Recursive definition of recur is ill-formed.
      In environment
      recur : Empty
      The codomain is "Empty"
      which should be a coinductive type.
      Recursive definition is: "wrap recur". *)

Fail Definition control_no_let : Empty := cofix recur : Empty := wrap recur.

(** ** 2 — the aliases are [Definition]s, not [let]s.

    Same two names, same decoy, same shape as the exhibit — but a constant
    carries no de Bruijn index, so there is nothing for the shifted lookup to
    land on and [whd_all] unfolds [actualC] to [Empty] in either environment.
    This isolates the trigger to *local* bindings.  REFUSED:

      In environment
      recur : actualC
      The codomain is "Empty"
      which should be a coinductive type. *)

Definition actualC := Empty.
Definition decoyC := Stream.

Fail Definition control_constant_alias : Empty := cofix recur : actualC := wrap recur.

(** ** 3 — one [let], and no decoy.

    The exhibit with its second [let] deleted: one token of difference.  The
    block has one member, so the lookup is off by one and lands on the [cofix]'s
    own binding, which is an assumption and does not reduce.  REFUSED, and the
    message is the defect said out loud — the codomain of a cofixpoint is being
    read off the cofixpoint's own name:

      Recursive definition of recur is ill-formed.
      In environment
      actual := Empty : Type
      recur : actual
      The codomain is "recur"
      which should be a coinductive type.
      Recursive definition is: "wrap recur". *)

Fail Definition control_one_let : Empty :=
  let actual := Empty in
  cofix recur : actual := wrap recur.

(** ** 4 — the gap binding is a [fun] parameter instead of a [let].

    The distance is right and the decoy is coinductive, but a lambda binds an
    assumption with no body, so [whd_all] leaves it stuck.  REFUSED — and note
    what the two lines say together: [recur : actual] is the declared type the
    kernel is printing, and [The codomain is "decoy"] is the type it read.

      In environment
      actual := Empty : Type
      decoy : Stream
      recur : actual
      The codomain is "decoy"
      which should be a coinductive type.
      Recursive definition is: "wrap recur".

    So the trigger needs a binding that is BOTH at distance [nbfix] AND has a
    body the reduction will unfold.  That is a [let], and only a [let]. *)

Fail Definition control_lambda_gap : Stream -> Empty :=
  let actual := Empty in
  fun (decoy : Stream) => cofix recur : actual := wrap recur.

(** ** 5 — the gap [let] binds an inductive type.

    Distance right, [let] right, body unfolds — and the tree lookup still fails,
    because what it finds is not coinductive.  REFUSED, naming a type the
    declared type never mentions and the file never used:

      In environment
      actual := Empty : Type
      decoy := nat : Set
      recur : actual
      The codomain is "nat"
      which should be a coinductive type.
      Recursive definition is: "wrap recur". *)

Fail Definition control_inductive_decoy : Empty :=
  let actual := Empty in
  let decoy := nat in
  cofix recur : actual := wrap recur.

(** ** 6 — the [nbfix] boundary, refused side: two cofixpoints, one gap [let].

    Nothing changes but the arity of the block.  With two members the lookup is
    off by two, so one gap binding is no longer enough and the shifted index
    lands on [r1] — the first member's own binding.  REFUSED:

      Recursive definition of r1 is ill-formed.
      In environment
      actual := Empty : Type
      decoy1 := Stream : Type
      r1 : actual
      r2 : actual
      The codomain is "r1"
      which should be a coinductive type.
      Recursive definition is: "wrap r1". *)

Fail Definition control_two_members_one_let : Empty :=
  let actual := Empty in
  let decoy1 := Stream in
  (cofix r1 : actual := wrap r1
   with r2 : actual := wrap r2
   for r1).

(** ** 6' — the [nbfix] boundary, accepted side: two cofixpoints, two gap [let]s.

    Add the second gap binding and the distance matches the arity again.
    ACCEPTED, and [two_two] is another infinite inhabitant of [Empty].  Together
    with §6 this measures the shift to be exactly [nbfix], which is the quantity
    PR #22388's [push_rec_types] diagnosis predicts.

    Expected: [Closed under the global context]. *)

Definition two_two : Empty :=
  let actual := Empty in
  let decoy1 := Stream in
  let decoy2 := Stream in
  (cofix r1 : actual := wrap r1
   with r2 : actual := wrap r2
   for r1).

Print Assumptions two_two.

(** ** 7 — the same shape with the guard check honestly switched off.

    The reporting channel that is silent on the exhibit, exercised on the same
    construction reached the sanctioned way.  This is not a route to [False]
    worth cataloguing — ../../../EscapeHatches/Coq/TypingFlags.v owns that, and
    ground rule 2 makes anything behind a flag an escape hatch.  It is here to
    establish that the silence in CofixWrongEnvRectree.v is a *miss* and not an
    absence of machinery.

    Expected, measured on 9.2 and 9.0.1:

        Axioms:
        cycleU is assumed to be guarded.

    and on the [.vo],

        rocqchk -o CofixWrongEnvRectreeControls
        * Constants/Inductives relying on unsafe (co)fixpoints:
            CofixWrongEnvRectreeControls.cycleU

    where the exhibit's own [.vo] reports [<none>] on that same line.  Both
    channels work.  #22386 does not reach either. *)

#[local] Unset Guard Checking.
Definition cycleU : Empty := cofix recur : Empty := wrap recur.
#[local] Set Guard Checking.

Definition contradictionU : False :=
  (fix absurdU (x : Empty) : False := match x with wrap y => absurdU y end) cycleU.

Print Assumptions contradictionU.
