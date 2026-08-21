(** * A stuck [if] is reified without its universe substitution, and definitional
      UIP is refuted

    rocq-prover/rocq#22380, filed 2026-08-20 13:00 UTC by `SkySkimmer` (Gaëtan
    Gilbert) and **OPEN**, label `kind: inconsistency`, fix PR
    [#22381](https://github.com/rocq-prover/rocq/pull/22381) ("Fix reification of
    FCase(Invert) in cclosure") unmerged.  The issue body names its source:
    *"Reported by OpenAI by email to a random core team member (not me).  For
    anyone reading this, please directly open issues instead of emailing random
    people."*

    ** Category: PARADOX (per ../../README.md)

    Same reasoning as [`VarianceVsDefinitionalUIP.v`](VarianceVsDefinitionalUIP.v),
    and the same measurement decides it.  On Rocq 9.2:

        Print Assumptions contradiction.
        Axioms:
        seq relies on definitional UIP.

    The `False` is conditional on definitional UIP — a documented,
    believed-consistent extension of the theory, not a check switched off — so by
    ground rule 1 this is a paradox: *Rocq 9.2 refutes a principle its own
    metatheory says is consistent with it.*  `KernelDefects/` needs a closed
    `False` with a silent audit; the audit here is not silent.  That file's
    header works the classification through in full, including why `Set
    Definitional UIP` is not an escape hatch in ground rule 2's sense and where
    this shape deviates from the rest of `Paradoxes/`; the argument is not
    repeated here.

    ** The one thing that is genuinely open about the classification

    Upstream says, in the issue body: *"The example uses UIP but the substitution
    is also missing on the predicate and branches (not just CaseInvert) so there
    should be an inconsistency without UIP too."*

    If such a spelling exists, it is a **closed** `False` with a silent audit and
    it belongs in `KernelDefects/`, not here.  Nobody has produced one — upstream
    offers it as an expectation, not a witness — and no attempt was made to
    produce one for this file.  So the classification above is a classification
    of *the construction that exists*, and it should be revisited if a UIP-free
    spelling appears.  Note that the sibling rocq#22391, from the same wave and
    the same family of uncomposed-universe-instance defects, **does** have a
    flag-free closed `False` on 9.2, so the expectation is not idle.

    ** The mechanism

    Two ingredients have to line up.

    *The stuck case.*  [flag] is closed with `Qed`, so it is opaque and
    `if flag then certificate else certificate` never reduces, even though both
    branches are the same type.  Every use of [cert_choice] therefore carries a
    live `FCase` closure through conversion.

    *The missing substitution.*  Upstream's summary, quoting the reporter:

    > The identity-term-substitution fast path in `CClosure.to_constr_case`
    > reconstructs a case without applying its delayed universe substitution to
    > the parameters, predicate, or branches. An identity term substitution does
    > not imply an identity universe substitution.

    > The witness forces a shared case closure during strict-equality
    > conversion. The application typechecker then reifies a residual type
    > through this fast path. The built-in `exact_no_check` tactic skips an
    > elaborator check, but does not skip the kernel check at `Defined` or the
    > subsequent standalone check; both accept the erroneous type.

    (Quoted verbatim, re-checked against the issue body.  Ground rule 7's
    *second* exception exists for a source that uses one of the words the rule
    asks to avoid; none of these sentences does — *witness* is on the rule's
    **preferred** list, not its avoid list — so nothing here is bracketed.  An
    earlier draft of this header replaced it with "[construction]" and cited that
    exception; the citation was wrong, and a quotation that needed no alteration
    has been restored.  The reproducer's *identifiers* are verbatim for a
    different reason: so that this file can be diffed against the issue body.
    That is what puts `payload` in [cert_payload] below, and in control 1's
    [cert_payload_t] — upstream's word, ground rule 7's **first** exception, and
    nowhere this file's own vocabulary.)

    So [cert_escaped] is checked with stale universe indices: the pair's first
    field is lowered from `Type@{lo'}` to `Type@{lo}` while its equality
    certificate is left alone.  §3 reads the two fields back out with ordinary
    pattern matching and gets a `Type@{lo}` that equals `Type@{hi}`.

    ** What each audit channel reports, measured on Rocq 9.2

      - `coqc` on this file:              exit 0.
      - `Print Assumptions contradiction`: `Axioms:` / `seq relies on
                                          definitional UIP.`  **Reported.**
      - `rocqchk` on the `.vo`:            exit 0, `Modules were successfully
                                          checked`.
      - `rocqchk -bytecode-compiler yes`:  exit 0, same.  (Worth stating because
                                          rocq#22352 is a defect where those two
                                          modes disagree; they do not here.)
      - `rocqchk -o` summary:              `* Axioms: <none>`
                                          `* Constants/Inductives relying on
                                             type-in-type: <none>`
                                          `* Constants/Inductives relying on
                                             unsafe (co)fixpoints: <none>`
      - downstream plain `Require` + a
        derivation of `1 = 2`:             exit 0, and `Print Assumptions` on the
                                          downstream constant still says `seq
                                          relies on definitional UIP.`

    As in the sibling file, `Print Assumptions` is the only channel that names
    the cost, and it names it downstream too; `rocqchk -o`'s summary has no line
    for definitional UIP and so reports `* Axioms: <none>` over this file.

    ** Toolchain (ground rule 4), and the version boundary

    | Rocq                    | §2 [cert_escaped]                         | §6 [contradiction] | Source          |
    | ----------------------- | ----------------------------------------- | ------------------ | --------------- |
    | 9.2 (OCaml 4.14.2)      | accepted                                  | accepted, exit 0   | measured here   |
    | 9.0.1 (Rocq Platform)   | **`Anomaly "in Univ.repr: Universe Var(2) undefined."`, exit 129** | not reached | measured here |
    | master                  | accepted                                  | accepted           | upstream, cited |

    The 9.0.1 row is the interesting one and it is a **version-boundary
    finding**, not a clean bill of health.  Measured with
    `coqc.exe -coqlib "C:\Rocq-Platform~9.0~2025.08\lib\coq"`, 9.0.1 does not
    quietly accept and it does not cleanly reject: it aborts with an anomaly, at
    the point where the kernel checks [cert_escaped].  An anomaly is Rocq asking
    to be sent a bug report, so on 9.0.1 the same construction is a *crash*
    rather than a `False`.

    Two readings, and nothing measured here chooses between them:

      - 9.0.1 might be *unaffected*, the stale index being caught by an
        assertion that later releases lost.
      - 9.0.1 might be affected by the same defect and merely fail differently,
        the malformed universe instance tripping `Univ.repr` before it can be
        used.

    Nothing in this file distinguishes those, and no attempt was made to; what is
    measured is only that **this construction does not yield a `False` on
    9.0.1**.  The sibling rocq#22391 anomalies on 9.0.1 in the same way, with
    `Universe Var(0)` in place of `Var(2)`, which suggests one boundary rather
    than two coincidences — that too is an observation, not a diagnosis.

    ** Where it sits in CATALOG.md, checked before filing

    The catalog has **no row for #22380**, by issue number or by mechanism.
    Three neighbours are there, all cited from the catalog rather than measured
    here:

      - §4.4, [#21690](https://github.com/rocq-prover/rocq/issues/21690) —
        *"Missing stack conversion for irrelevant-to-relevant match; with
        `Definitional UIP`, `0 = 1`"*, fixed in **9.2.0**.  Same ingredient, one
        site over, and the release that fixed it is the release this file runs
        on.
      - §4.3, [#21689](https://github.com/rocq-prover/rocq/issues/21689) and
        [#21970](https://github.com/rocq-prover/rocq/issues/21970) — *"Double
        universe substitution in letins from match indices / constructor
        arguments"*, 9.2.0 / 9.3.  The same class of mistake, a universe
        substitution applied the wrong number of times, one layer away in
        `CClosure`.
      - §4.6's corrections paragraph,
        [#20016](https://github.com/rocq-prover/rocq/issues/20016) — *"bad case
        inversion with `Set Definitional UIP`"* — which the catalog struck off
        after measuring that **9.2.0 rejects it**.  #22380 is a live
        case-inversion route with the same flag on that same release, so that
        paragraph closes an issue and not the family.

    ** Expected future state: REJECTION

    #22381 is unmerged.  When it lands, §2 stops being accepted and this file
    stops compiling; that failure is the intended signal, and `../verify.ps1`
    should be read accordingly.

    Write-up: ../../Reports/2026-08-20-rocq-august-wave.md *)

Set Universe Polymorphism.
Set Definitional UIP.

From Stdlib Require Import Hurkens.

(** ** 1. The ingredients

    [flag] is opaque: `Qed`, not `Defined`.  §4's control 1 is the measurement
    that this single token is load-bearing. *)

Definition flag : bool. Proof. exact true. Qed.

Inductive seq@{i} {A : Type@{i}} (x : A) : A -> SProp :=
| srefl : seq x x.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq x y) : P x -> P y :=
  match e in seq _ y return P x -> P y with
  | srefl _ => fun v => v
  end.

(** A dependent pair carrying a type and a certificate that the type *is* a
    named universe.  Both branches of the [if] are the same, so the only thing
    the [if] contributes is that it is stuck. *)

Definition certificate@{anchor data out | anchor < out, data < out}
    : Type@{out} :=
  { A : Type@{data} & @eq Type@{out} A Type@{anchor} }.

Definition cert_choice@{anchor data out | anchor < out, data < out}
    : Type@{out} :=
  if flag then certificate@{anchor data out}
  else certificate@{anchor data out}.

Definition cert_inhabitant@{anchor data out | anchor < data, data < out}
    : cert_choice@{anchor data out} :=
  match flag as b return
    (if b then certificate@{anchor data out}
     else certificate@{anchor data out}) with
  | true => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  | false => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  end.

(** [cert_force_type] is the residual type the application typechecker has to
    reify.  The [transport] is what routes it through the `FCaseInvert` path,
    and it is the only place definitional UIP is used. *)

Definition cert_force_type@{anchor data out top |
    anchor < data, data < out, out < top} : Type@{out} :=
  let T := (fun _ : unit => cert_choice@{anchor data out}) tt in
  @transport@{top top} Type@{out}
    (fun X : Type@{out} => X -> Type@{out})
    T (if flag then certificate@{anchor data out}
       else certificate@{anchor data out})
    (@srefl@{top} Type@{out} T)
    (fun _ : T => unit -> T)
    cert_inhabitant@{anchor data out}.

Definition cert_payload@{anchor data out | anchor < data, data < out}
    : unit -> cert_choice@{anchor data out} :=
  fun _ => cert_inhabitant@{anchor data out}.

(** ** 2. The declaration the kernel should refuse

    Bound at `@{lo hi w}` on the right and claimed at `@{lo lo' hi}` on the
    left, with `lo = lo'`.  `exact_no_check` skips the elaborator's check — §4's
    control 2 shows the elaborator does refuse it — but the kernel still runs at
    the end of the command, and the kernel accepts. *)

Definition cert_escaped@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z}
    : cert_choice@{lo lo' hi} :=
  ltac:(exact_no_check ((cert_payload@{lo hi w} : cert_force_type@{lo hi w z}) tt)).

(** ** 3. Reading the pair back out

    Nothing here is unusual.  [cert_collapse] discharges the stuck [if] and
    [cert_first]/[cert_second] are ordinary projections.  They are stated before
    the controls only because control 3 needs them. *)

Definition cert_collapse@{anchor data out | anchor < out, data < out}
    (x : cert_choice@{anchor data out}) : certificate@{anchor data out} :=
  (match flag as b return
     (if b then certificate@{anchor data out}
      else certificate@{anchor data out}) -> certificate@{anchor data out}
   with
   | true => fun x => x
   | false => fun x => x
   end) x.

Definition cert_first@{anchor data out | anchor < out, data < out}
    (x : certificate@{anchor data out}) : Type@{data} :=
  match x with existT _ A _ => A end.

Definition cert_second@{anchor data out | anchor < out, data < out}
    (x : certificate@{anchor data out})
    : @eq Type@{out} (cert_first@{anchor data out} x) Type@{anchor} :=
  match x as x return
    @eq Type@{out} (cert_first@{anchor data out} x) Type@{anchor}
  with existT _ A e => e end.

(** ** 4. Controls -- five deliberately-broken twins, all refused

    Ground rule 6.  `Fail` is silent in batch mode, so each assertion is carried
    by this file's exit code; the messages below were captured by compiling each
    control standalone on Rocq 9.2.

    Control 1 -- ONE TOKEN, and it is the sharpest of the five.  Everything
    below is §1 and §2 again with a single change: [flag_t] is closed with
    `Defined` instead of `Qed`.  Transparent, the [if] reduces, [cert_choice_t]
    is just [certificate], there is no stuck case closure for
    `to_constr_case`'s fast path to mishandle -- and the same
    `exact_no_check` is now **refused by the kernel**:

      The term "(cert_payload_t : cert_force_type_t) tt" has type
       "{A : Type & A = Type}"
      while it is expected to have type "cert_choice_t".

    Upstream's report does not isolate the trigger this far.  Opacity is the
    whole difference, and it is `Qed` versus `Defined`.

    That the **kernel** is the stage that refuses was measured rather than
    inferred, because the `ltac:(...)` spelling reports the error against the
    whole command and so does not say.  Rewritten as
    `Proof. exact_no_check ... Defined.`, the tactic succeeds and closes the
    goal — the elaborator raises nothing — and the message above is reported at
    `Defined` itself, `line ..., characters 0-8`.  §2's identical term is
    accepted at that same point. *)

Definition flag_t : bool. Proof. exact true. Defined.

Definition cert_choice_t@{anchor data out | anchor < out, data < out}
    : Type@{out} :=
  if flag_t then certificate@{anchor data out}
  else certificate@{anchor data out}.

Definition cert_inhabitant_t@{anchor data out | anchor < data, data < out}
    : cert_choice_t@{anchor data out} :=
  match flag_t as b return
    (if b then certificate@{anchor data out}
     else certificate@{anchor data out}) with
  | true => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  | false => @existT (Type@{data})
      (fun A : Type@{data} => @eq Type@{out} A Type@{anchor})
      Type@{anchor} (@eq_refl Type@{out} Type@{anchor})
  end.

Definition cert_force_type_t@{anchor data out top |
    anchor < data, data < out, out < top} : Type@{out} :=
  let T := (fun _ : unit => cert_choice_t@{anchor data out}) tt in
  @transport@{top top} Type@{out}
    (fun X : Type@{out} => X -> Type@{out})
    T (if flag_t then certificate@{anchor data out}
       else certificate@{anchor data out})
    (@srefl@{top} Type@{out} T)
    (fun _ : T => unit -> T)
    cert_inhabitant_t@{anchor data out}.

Definition cert_payload_t@{anchor data out | anchor < data, data < out}
    : unit -> cert_choice_t@{anchor data out} :=
  fun _ => cert_inhabitant_t@{anchor data out}.

Fail Definition cert_escaped_t@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z}
    : cert_choice_t@{lo lo' hi} :=
  ltac:(exact_no_check ((cert_payload_t@{lo hi w} : cert_force_type_t@{lo hi w z}) tt)).

(** Control 2 -- ONE TOKEN the other way: the same term as §2 with
    `exact_no_check` dropped, so the elaborator's conversion runs.  It refuses.
    That is what makes §2 a statement about the *kernel* and not about a lax
    tactic: the two conversions disagree, and the stricter one is not the one
    that decides.

      The term "(cert_payload : cert_force_type) tt" has type
       "cert_choice@{lo hi w}"
      while it is expected to have type "cert_choice@{lo lo' hi}". *)

Fail Definition cert_escaped_elab@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z}
    : cert_choice@{lo lo' hi} :=
  (cert_payload@{lo hi w} : cert_force_type@{lo hi w z}) tt.

(** Control 3 -- the `lo = lo'` clause deleted.  The kernel still accepts the
    escaped declaration, so the defect is still there; what is gone is the
    identification of the two levels that turns a stale index into a collapse.
    §5's [cert_small] is then refused, and the message names exactly the
    constraint that was doing the work.

      Universe constraints are not implied by the ones declared: lo' <= lo *)

Definition cert_escaped_free@{lo lo' hi w z |
    lo < hi, lo' < hi, hi < w, w < z}
    : cert_choice@{lo lo' hi} :=
  ltac:(exact_no_check ((cert_payload@{lo hi w} : cert_force_type@{lo hi w z}) tt)).

Fail Definition cert_small_free@{lo lo' hi w z |
    lo < hi, lo' < hi, hi < w, w < z} : Type@{lo} :=
  cert_first@{lo lo' hi}
    (cert_collapse@{lo lo' hi} cert_escaped_free@{lo lo' hi w z}).

(** Control 4 -- the hypothesis itself, one token.  With `Definitional UIP`
    unset, [seq] is an ordinary SProp inductive, its eliminator into [Type] does
    not exist, and §1 cannot be written.  This is the measurement that makes the
    `False` conditional, and hence the measurement that decides this file's
    directory.

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

(** Control 5 -- Hurkens is not doing the work: handed a [Type] that really is
    one level below, its precondition is not provable.

      The term "eq_refl : Type = Type" has type "Type@{lo} = Type@{lo}"
      while it is expected to have type
       "Type@{TypeNeqSmallType.Paradox.u0} = Type@{lo}"
      (universe inconsistency: Cannot enforce lo =
      TypeNeqSmallType.Paradox.u0 because lo < TypeNeqSmallType.Paradox.u0). *)

Fail Definition control_hurkens@{lo hi | lo < hi} : False :=
  TypeNeqSmallType.paradox Type@{lo} (eq_refl : @eq Type@{hi} Type@{lo} Type@{lo}).

(** ** 5. The false judgment, stated

    [cert_small] is a [Type@{lo}]; [cert_small_is_universe] says it is
    [Type@{lo}] itself, as an equation at [Type@{hi}].  Everything below is
    honest, and everything above §5 is what Rocq should not have accepted. *)

Definition cert_small@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z} : Type@{lo} :=
  cert_first@{lo lo' hi}
    (cert_collapse@{lo lo' hi} cert_escaped@{lo lo' hi w z}).

Definition cert_small_is_universe@{lo lo' hi w z |
    lo = lo', lo < hi, hi < w, w < z}
    : @eq Type@{hi} cert_small@{lo lo' hi w z} Type@{lo} :=
  cert_second@{lo lo' hi}
    (cert_collapse@{lo lo' hi} cert_escaped@{lo lo' hi w z}).

(** ** 6. [False], with the cost named *)

Definition contradiction : False :=
  TypeNeqSmallType.paradox cert_small (eq_sym cert_small_is_universe).

(** Expected on 9.2:

      Axioms:
      seq relies on definitional UIP. *)
Print Assumptions contradiction.

(** And it travels: a `Require` of this file gives a downstream consumer a
    usable [False], with the same audit line. *)

Definition one_eq_two : 1 = 2 := match contradiction with end.
Print Assumptions one_eq_two.
