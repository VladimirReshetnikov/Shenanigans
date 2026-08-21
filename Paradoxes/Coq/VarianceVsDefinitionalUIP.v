(** * Variance analysis calls a universe irrelevant, and definitional UIP is
      refuted

    rocq-prover/rocq#22376, filed 2026-08-20 12:31 UTC by `SkySkimmer` (Gaëtan
    Gilbert) and **OPEN**, label `kind: inconsistency`, fix PR
    [#22377](https://github.com/rocq-prover/rocq/pull/22377) unmerged.  The issue
    body names its source: *"Reported by OpenAI by email to a random core team
    member (not me). For anyone reading this, please directly open issues instead
    of emailing random people."*

    ** Category: PARADOX (per ../../README.md)

    Ground rule 1 decides it, and the audit says so out loud.  On Rocq 9.2:

        Print Assumptions contradiction.
        Axioms:
        seq relies on definitional UIP.

    The `False` is **conditional on definitional UIP**, and definitional UIP is
    not a hole in the kernel — it is a documented, believed-consistent extension
    of the theory that Rocq offers behind `Set Definitional UIP`, on the same
    footing as `SProp` itself.  So what this file proves has the shape
    [`GuardVsUnivalence.v`](GuardVsUnivalence.v) proves: *Rocq 9.2 refutes a
    principle its own metatheory says is consistent with it.*  There it was
    univalence; here it is definitional UIP.  That places both in `Paradoxes/`
    and neither in `KernelDefects/`, which requires a **closed** `False` with a
    silent audit — this one is closed but the audit is not silent.

    **Why not `EscapeHatches/`, since a flag is involved.**  Ground rule 2 makes
    a `False` behind a flag an escape hatch, and the flag test is the right one
    for `Unset Guard Checking` or `Unset Universe Checking`, whose entire purpose
    is to switch a check off.  `Set Definitional UIP` switches nothing off: it
    adds a reduction rule that is supposed to be sound.  A `False` obtained with
    it on is therefore evidence about Rocq, not evidence about the user.
    [`../../EscapeHatches/Coq/TypingFlags.v`](../../EscapeHatches/Coq/TypingFlags.v)
    exhibits the honest flag routes and none of them looks like this.

    **Where this file deviates from the rest of `Paradoxes/`, stated plainly.**
    Every other exhibit here carries its hypothesis in the *type* of the
    theorem — `Univalence_transport -> False`, `Univalence -> UIP -> False`.
    Definitional UIP is a conversion rule, not a proposition, so it cannot be
    written as a premise; it shows up in `Print Assumptions` instead.  The cost
    is reported, and reported in the one place ground rule 3 asks for, but a
    reader expecting a two-place implication will not find one.  §5's
    [small_is_universe] is the nearest thing: the false judgment, stated, with
    everything after it honest Hurkens.

    ** The mechanism

    `seq` is the SProp-valued identity type; with `Set Definitional UIP` its
    eliminator computes, and the kernel represents a `match` on it as an
    `FCaseInvert` frame.  Variance analysis for a `Cumulative Inductive` walks
    the constructor types to decide, for each bound universe, whether an instance
    may vary.  Upstream's title is the finding: it *"incorrectly ignores stack
    data of FCaseInvert"*.  The universe `u` in §2's [Hidden] occurs only inside
    the argument of a `transport`, i.e. only in an `FCaseInvert` stack, so the
    analysis never sees it and marks it **irrelevant**.

    An irrelevant universe may be instantiated at anything without a constraint,
    so [Box@{hi z w h}] and [Box@{lo z w h}] are convertible, a [Type@{hi}] goes
    in and a [Type@{lo}] comes out, and §5 gets a universe that is an element of
    itself.  Hurkens does the rest.

    ** Measured, not inferred: the `*` is not needed

    Upstream writes the annotation explicitly — `Hidden@{*u z w h | ...}` — and
    comments that *"`*u` should not be accepted"*.  That understates it.  §2
    below carries **no variance annotation at all**, and the analysis infers the
    irrelevance unprompted; `Print Hidden` reports

        (* *u =z =w =h |= u < z
                          z < w
                          w < h *)

    So nothing has to be asserted by the author for the defect to bite: writing
    `Cumulative Inductive` is enough.  That is this repository's sharpening of
    the report, and §3's control 1 is its other half — demanding `=u` explicitly
    is refused, so the annotation is *checked*, it is just checked against a
    wrong answer.

    ** What each audit channel reports, measured on Rocq 9.2

      - `coqc` on this file:              exit 0.
      - `Print Assumptions contradiction`: `Axioms:` / `seq relies on
                                          definitional UIP.`  **Reported.**  This
                                          is the channel that catches it, and it
                                          is why the file is here and not in
                                          `KernelDefects/`.
      - `rocqchk` on the `.vo`:            exit 0, `Modules were successfully
                                          checked`.
      - `rocqchk -bytecode-compiler yes`:  exit 0, same.
      - `rocqchk -o` summary:              `* Axioms: <none>`
                                          `* Constants/Inductives relying on
                                             type-in-type: <none>`
                                          `* Constants/Inductives relying on
                                             unsafe (co)fixpoints: <none>`
      - downstream plain `Require` + a
        derivation of `1 = 2`:             exit 0, and `Print Assumptions` on the
                                          downstream constant still says `seq
                                          relies on definitional UIP.`

    Two of those deserve to be read together.  `Print Assumptions` names the
    cost and carries it across a `Require`; **`rocqchk -o`'s summary has no line
    for definitional UIP at all**, so the independent checker's own bill of
    materials reports `* Axioms: <none>` over this file.  Anyone auditing a
    build with `rocqchk -o` rather than `Print Assumptions` learns nothing here.
    That is a measurement of the summary's coverage, not a claim that upstream
    considers it a defect; compare
    [`../../Audits/Coq/CheckerCoverage/`](../../Audits/Coq/CheckerCoverage/),
    which is where the general question lives.

    ** Toolchain (ground rule 4)

    | Rocq                    | §2 [Hidden] | §5 [contradiction] | `Print Assumptions`               | Source            |
    | ----------------------- | ----------- | ------------------ | --------------------------------- | ----------------- |
    | 9.2 (OCaml 4.14.2)      | accepted    | accepted, exit 0   | `seq relies on definitional UIP.` | measured here     |
    | 9.0.1 (Rocq Platform)   | accepted    | accepted, exit 0   | `seq relies on definitional UIP.` | measured here     |
    | master                  | accepted    | accepted           | —                                 | upstream, cited   |

    The 9.0.1 row was measured with
    `coqc.exe -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"`.  Unlike its two
    siblings in this wave — rocq#22380 and rocq#22391, both of which *anomaly* on
    9.0.1 — this one behaves identically on the two releases, so it is the older
    of the three defects and has no version boundary to report.

    ** Where it sits in CATALOG.md, checked before filing

    The catalog has **no row for #22376**, by issue number or by mechanism.  Its
    nearest neighbour is §4.3's
    [#15916](https://github.com/rocq-prover/rocq/issues/15916) — *"Variance
    inference for section universes ignored use in inductives"*, fixed in
    **8.16** — cited from the catalog, not measured here.  The failure shape is
    the same one, variance inference under-approximating where a universe is
    actually used, and the site is different: sections there, the stack of an
    `FCaseInvert` frame here.  So the family is not new; this member is, and
    unlike #15916 it is live on the current stable release.

    ** Expected future state: REJECTION

    When #22377 merges, §2's [Hidden] stops inferring `*u`, §5 stops compiling,
    and this file fails.  That failure is the intended signal, exactly as in
    [`GuardVsUnivalence.v`](GuardVsUnivalence.v); `../verify.ps1` should be read
    accordingly.

    Write-up: ../../Reports/2026-08-20-rocq-august-wave.md *)

Set Universe Polymorphism.
Set Definitional UIP.

From Stdlib Require Import Hurkens.

(** ** 1. The ingredients

    [seq] is the SProp-valued identity type and [transport] is its eliminator
    into [Type].  Both need `Set Definitional UIP`; §3's control 2 is the
    measurement of that. *)

Inductive seq@{i} {A : Type@{i}} (x : A) : A -> SProp :=
| srefl : seq x x.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq x y) : P x -> P y :=
  match e in seq _ y return P x -> P y with
  | srefl _ => fun v => v
  end.

(** ** 2. The inductive whose variance is misstated

    No variance annotation.  `u` occurs only under the [transport], i.e. only in
    the stack of an `FCaseInvert` frame, and the analysis concludes it is
    irrelevant. *)

Cumulative Inductive Hidden@{u z w h | u < z, z < w, w < h}
    (Y : Type@{w}) (e : @seq@{h} Type@{w} Type@{z} Y)
    (Q : Y -> Type@{w}) : Type@{w} :=
| hide : Q (@transport@{h w} Type@{w} (fun T : Type@{w} => T)
              Type@{z} Y e Type@{u}) -> Hidden Y e Q.

(** Expected: `(* *u =z =w =h |= u < z / z < w / w < h *)`.  The `*` is the
    defect, and this file never asked for it. *)
Set Printing Universes.
Print Hidden.
Unset Printing Universes.

(** ** 3. Controls -- four deliberately-broken twins, all refused

    Ground rule 6.  `Fail` is silent in batch mode, so each assertion is carried
    by this file's exit code; the messages below were captured by compiling each
    control standalone on Rocq 9.2.

    Control 1 isolates the trigger to ONE token: demand `=u` where §2 left the
    annotation off, and the whole chain still declares, but the first place the
    irrelevance is *used* is refused.  So the declared variance is genuinely
    checked; §2 is the check returning the wrong answer, not the check being
    skipped.

      In environment
      A : Type
      The term "boxInv A" has type "BoxInv@{hi z w h}" while it is expected to
      have type "BoxInv@{lo z w h}"
      (universe inconsistency: Cannot enforce hi = lo because lo < hi).

    Upstream quotes the same message for the same reason, so this control is a
    re-measurement of a documented fact rather than a new one. *)

Cumulative Inductive HiddenInv@{=u z w h | u < z, z < w, w < h}
    (Y : Type@{w}) (e : @seq@{h} Type@{w} Type@{z} Y)
    (Q : Y -> Type@{w}) : Type@{w} :=
| hideInv : Q (@transport@{h w} Type@{w} (fun T : Type@{w} => T)
                 Type@{z} Y e Type@{u}) -> HiddenInv Y e Q.

Definition BoxInv@{u z w h | u < z, z < w, w < h} : Type@{w} :=
  HiddenInv@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A).

Definition boxInv@{u z w h | u < z, z < w, w < h}
    (A : Type@{u}) : BoxInv@{u z w h} :=
  hideInv@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A) A.

Definition unboxInv@{u z w h | u < z, z < w, w < h}
    (x : BoxInv@{u z w h}) : Type@{u} :=
  match x with hideInv _ _ _ A => A end.

Fail Definition lowerInv@{lo hi z w h | lo < hi, hi < z, z < w, w < h}
    (A : Type@{hi}) : Type@{lo} :=
  unboxInv@{lo z w h} (boxInv@{hi z w h} A).

(** Control 2 is the hypothesis itself, and it is also one token: with
    `Definitional UIP` unset, [seq] is an ordinary SProp inductive and its
    eliminator into [Type] does not exist, so §1 cannot even be written.  This is
    the measurement that makes the `False` *conditional* rather than closed, and
    hence the measurement that decides this file's directory.

      Incorrect elimination of "e" in the inductive type "seq_plain":
      the return type has sort "Type" while it should be SProp.
      Elimination of an inductive object of sort SProp
      is not allowed on a predicate in sort "Type"
      because strict proofs can be eliminated only to build strict proofs. *)

Unset Definitional UIP.

Inductive seq_plain@{i} {A : Type@{i}} (x : A) : A -> SProp :=
| srefl_plain : seq_plain x x.

Fail Definition transport_plain@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq_plain x y) : P x -> P y :=
  match e in seq_plain _ y return P x -> P y with
  | srefl_plain _ => fun v => v
  end.

Set Definitional UIP.

(** Control 3.  Definitional UIP by itself proves nothing of the kind: with the
    flag on and no [Hidden] in sight, the honest [Type : Type] is still refused,
    so §5's collapse comes from §2 and not from the flag.

      The term "eq_refl" has type "Type = Type" while it is expected to have
      type
       "Type = Small0"
      (universe inconsistency: Cannot enforce TypeNeqSmallType.Paradox.u0 =
      C3.102 because C3.102 < C3.101 <= TypeNeqSmallType.Paradox.u0).

    The two anonymous levels are named after the file they are generated in, so
    that pair varies; the shape does not. *)

Definition Small0 : Type := Type.
Fail Definition control_flag_alone : False :=
  TypeNeqSmallType.paradox Small0 eq_refl.

(** Control 4.  And Hurkens is not doing the work either: handed a [Type] that
    really is one level below, its precondition is not provable.

      The term "eq_refl : Type = Type" has type "Type@{lo} = Type@{lo}"
      while it is expected to have type
       "Type@{TypeNeqSmallType.Paradox.u0} = Type@{lo}"
      (universe inconsistency: Cannot enforce lo =
      TypeNeqSmallType.Paradox.u0 because lo < TypeNeqSmallType.Paradox.u0). *)

Fail Definition control_hurkens@{lo hi | lo < hi} : False :=
  TypeNeqSmallType.paradox Type@{lo} (eq_refl : @eq Type@{hi} Type@{lo} Type@{lo}).

(** ** 4. Passing a universe through the irrelevant slot *)

Definition Box@{u z w h | u < z, z < w, w < h} : Type@{w} :=
  Hidden@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A).

Definition box@{u z w h | u < z, z < w, w < h}
    (A : Type@{u}) : Box@{u z w h} :=
  hide@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A) A.

Definition unbox@{u z w h | u < z, z < w, w < h}
    (x : Box@{u z w h}) : Type@{u} :=
  match x with hide _ _ _ A => A end.

(** [box] at `hi`, [unbox] at `lo`.  Control 1's twin is refused here; this one
    is accepted, because `u` is irrelevant and the two [Box]es convert. *)

Definition lower@{lo hi z w h | lo < hi, hi < z, z < w, w < h}
    (A : Type@{hi}) : Type@{lo} :=
  unbox@{lo z w h} (box@{hi z w h} A).

(** ** 5. The false judgment, stated

    [small] is [Type@{lo}] shipped down into [Type@{lo}] itself, and
    [small_is_universe] is the equation saying so.  This is the nearest this
    file comes to putting its cost in a statement: everything below is honest,
    and everything above is what Rocq should not have accepted. *)

Definition small@{lo hi z w h | lo < hi, hi < z, z < w, w < h}
    : Type@{lo} := lower@{lo hi z w h} Type@{lo}.

Definition small_is_universe@{lo hi z w h + | lo < hi, hi < z, z < w, w < h +}
    : @eq Type@{hi} small@{lo hi z w h} Type@{lo} := eq_refl.

(** ** 6. [False], with the cost named

    [TypeNeqSmallType.paradox] is Stdlib's Hurkens instance: a [Type] that is
    equal to a universe containing it yields [False].  Nothing here is novel;
    §5 is the whole finding. *)

Definition contradiction : False :=
  TypeNeqSmallType.paradox small (eq_sym small_is_universe).

(** Expected on 9.2 and on 9.0.1:

      Axioms:
      seq relies on definitional UIP. *)
Print Assumptions contradiction.

(** And it travels: a `Require` of this file gives a downstream consumer a
    usable [False], with the same audit line. *)

Definition one_eq_two : 1 = 2 := match contradiction with end.
Print Assumptions one_eq_two.
