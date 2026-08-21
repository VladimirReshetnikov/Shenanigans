(** * The two conversion machines the audit cannot see: [vm_compute] and
      [native_compute]

    Category (see ../../README.md): ESCAPE HATCH.  The cost is real and is not
    reported.  [Print Assumptions] says [Closed under the global context] for
    every theorem below, [Print Typing Flags] is unchanged, [coqchk]'s CONTEXT
    SUMMARY says [* Axioms: <none>], and nothing in the [.vo] records which
    machine decided the proof.  Unlike the other flag-gated files here, no
    command-line argument is needed: [vm_compute] is on in a default build.

    What is actually bought.  [vm_compute] and [native_compute] are not tactics.
    They leave a [VMcast]/[NATIVEcast] node in the proof term, and the *kernel*
    re-runs the corresponding machine at [Qed].  So the trusted base of a file
    that uses one is not [kernel/reduction.ml] but

      - [kernel/byterun/coq_interp.c] with [vmbytegen.ml]/[vmvalues.ml] (VM), or
      - the OCaml native compiler, invoked as [ocamlfind ocamlopt] at
        proof-checking time, plus [Dynlink] (native).

    Three things are established below, each with a control:

      1. the machines are kernel-level, not tactic-level (section 1);
      2. they decide things the ordinary machine does not -- by ignoring the
         [Opaque] strategy (section 2) and by margin on real computations
         (section 3);
      3. none of it is reported (section 5), while [coqchk] -- which *is* a real
         backstop here, having no VM and redoing the work itself -- pays a
         measured 16x for that (section 6).

    Toolchain: The Rocq Prover 9.2, opam switch rocq-9.2, OCaml 4.14.2,
    [COQ_NATIVE_COMPILER_DEFAULT=no].  Second toolchain and version matrix in
    section 7.  Verified by ../verify.ps1. *)

From Stdlib Require Import ZArith.

(** ** 1. They are not tactics: the kernel is what runs them

    [vm_cast_no_check t] closes the goal with [t] and performs no check at
    tactic level.  The only thing that ever compares the two sides is the
    kernel, at [Qed], using the VM. *)

Definition step (b : bool) : bool := negb (negb b).

Theorem kernel_ran_the_vm : Pos.iter step true 30000000%positive = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(** CONTROL -- ../verify.ps1 compiles [ComputeMachinesWrongValue.v], which is
    this declaration with the right-hand side changed to [false].  The tactic
    still succeeds; the kernel rejects, at [Qed], with

      The term "eq_refl" has type "false = false"
      while it is expected to have type "Pos.iter step true 30000000 = false"

    That the refusal comes from [Qed] and not from the tactic is this section. *)

(** ** 2. [Opaque] is a strategy hint, not a seal -- and the VM does not read it

    Measured, all eight machines against all three ways Rocq can hide a body.
    [Y] = the body is reached, [.] = it is not.

      |                       | compute cbv lazy simpl cbn hnf | vm_compute native_compute | conversion ([reflexivity]) |
      | [Opaque] a Definition |  .   .    .    .     .    .    |     Y            Y        |            Y               |
      | [Lemma ... Qed]       |  .   .    .    .     .    .    |     .            .        |            .               |
      | [Module M : SIG]      |  .   .    .    .     .    .    |     .            .        |            .               |

    Two readings follow, and only the first is the familiar one. *)

Definition secret : nat := 5.
Opaque secret.

(** Stuck under every ordinary machine -- each prints [secret]. *)
Eval compute in secret.
Eval cbv     in secret.
Eval lazy    in secret.
Eval simpl   in secret.
Eval cbn     in secret.
Eval hnf     in secret.

(** Reduced by both kernel machines -- each prints [5].  The author's
    [Opaque] declaration is simply not consulted. *)
Eval vm_compute     in secret.
Eval native_compute in secret.

Theorem broke_the_seal : secret = 5.
Proof. vm_compute. reflexivity. Qed.

(** *** 2a. CORRECTION to ../../CATALOG.md section 1.2

    That row reads "Both ignore [Opaque]", which is true of the machines and
    overstates the consequence.  [Opaque] never sealed anything against
    *conversion*: it sets the [Conv_oracle] unfolding priority, which the six
    reduction tactics honour and which unification does not consult at all.  So
    the goal [broke_the_seal] closes is closable without any of them -- *)

Goal secret = 5. Proof. reflexivity. Qed.

(** -- and it is closable through the kernel with an ordinary cast as well. *)

Goal secret = 5. Proof. change_no_check (5 = 5). reflexivity. Qed.

(** What [vm_compute] therefore breaks is the *displayed* abstraction, not
    provability.  Stated precisely: [Opaque] is the only one of Rocq's three
    hiding mechanisms that [vm_compute] overrides, and it is also the only one
    that was never load-bearing.  The two that are load-bearing hold, at tactic
    level and at kernel level both, and the rest of this section is the
    controls that show it. *)

(** *** 2b. CONTROL: [Qed]-opacity holds against the VM

    Folklore says [vm_compute] unfolds [Qed] constants.  On 9.2 it does not,
    and neither does the kernel's VM conversion. *)

Lemma sealed : nat. Proof. exact 5. Qed.
Goal sealed = 5. Proof. Fail reflexivity.                    Abort.
Goal sealed = 5. Proof. Fail (compute;        reflexivity).  Abort.
Goal sealed = 5. Proof. Fail (vm_compute;     reflexivity).  Abort.
Goal sealed = 5. Proof. Fail (native_compute; reflexivity).  Abort.

(** ../verify.ps1 compiles [ComputeMachinesQedSeal.v] for the kernel half,
    whose [vm_cast_no_check] is refused at [Qed] with

      The term "eq_refl" has type "5 = 5"
      while it is expected to have type "sealed = 5" *)

(** *** 2c. CONTROL: signature ascription holds against the VM *)

Module Type SIG. Parameter x : nat. End SIG.
Module M : SIG. Definition x := 5. End M.
Goal M.x = 5. Proof. Fail reflexivity.                    Abort.
Goal M.x = 5. Proof. Fail (compute;        reflexivity).  Abort.
Goal M.x = 5. Proof. Fail (vm_compute;     reflexivity).  Abort.
Goal M.x = 5. Proof. Fail (native_compute; reflexivity).  Abort.

(** ** 3. A separation the exit code can see

    [kernel_ran_the_vm] above and [ComputeMachinesNoVM.v] are the *same*
    theorem with the *same* script, differing only in which cast the kernel
    finds: [change_no_check] leaves a [DEFAULTcast], so [Qed] uses ordinary
    conversion.  Measured here, sequentially, on an otherwise idle machine,
    with the 1.0 s [ZArith] load subtracted:

      | iterations | [VMcast] | [DEFAULTcast] | ratio |
      | ---------- | -------- | ------------- | ----- |
      |  2 000 000 |   1.2 s  |      6.0 s    |   5x  |
      |  8 000 000 |   1.6 s  |     23.1 s    |  14x  |
      | 30 000 000 |   4.7 s  |  4 m 17 s     |  54x  |

    The ordinary side is super-linear where the VM is linear, so the ratio is
    not a constant factor -- it is a wall.  ../verify.ps1 asserts the separation
    at 30 000 000 with a 60 s cap: this file must be accepted (3.7 s to 13.0 s
    across runs here, disk-cache dependent), and [ComputeMachinesNoVM.v] must be
    killed (it needs 257 s).

    This is what "decides something the ordinary conversion machine does not"
    means in practice.  It is not a soundness claim about the VM; it is the
    reason a development reaches for [vm_compute] in the first place, and hence
    the reason the enlarged trusted base is not optional for it. *)

(** ** 4. [native_compute] silently becomes [vm_compute]

    This build has [COQ_NATIVE_COMPILER_DEFAULT=no], so every [native_compute]
    above emitted

      Warning: native_compute disabled at configure time; falling back to
      vm_compute. [native-compiler-disabled,native-compiler,default]

    and was decided by the VM instead.  Nothing else changes: same theorems,
    same [.vo], same section 5 output.  [-native-compiler yes] does not restore
    it, and says so:

      Warning: Native compiler is disabled, -native-compiler yes option ignored.

    So *which machine decided a proof is a property of the installation, not of
    the file*, and the file cannot tell.  Where the native compiler is enabled,
    the proof additionally depends on [ocamlfind ocamlopt] being present and
    generating correct code at check time, and on [Dynlink] loading the result
    into the kernel's own process.  That is a build-time dependency of a
    logical claim, and no audit surface mentions it. *)

(** ** 5. The audit surface: nothing *)

Print Assumptions kernel_ran_the_vm.
Print Assumptions broke_the_seal.

(** Both print [Closed under the global context].  The flag report is likewise
    untouched -- [true]/[true]/[true] -- because no typing flag was set.
    Contrast ./TypingFlags.v, where this same command is what discloses the
    cost, and ./RewriteRules.v, where the [Theory:] banner does. *)

Print Typing Flags.

(** ** 6. [coqchk] does not trust the VM, and that is what it costs

    Unlike [Unset Guard Checking] and [Unset Positivity Checking], which
    [coqchk] merely lists while exiting 0 (../../CATALOG.md section 4.7), a
    [vm_compute] proof is genuinely re-verified: [coqchk] has no VM and redoes
    the computation with its own conversion.  Measured at 2 000 000 iterations,
    with each tool's own baseline on an empty [ZArith] file subtracted
    ([coqc] 1.0 s, [coqchk] 35.7 s -- [coqchk] re-checks all of [ZArith]):

      | step                                | work  |
      | ----------------------------------- | ----- |
      | [coqc], kernel uses the VM          |  1.2 s |
      | [coqc], kernel uses ordinary conv.  |  6.0 s |
      | [coqchk]                            | 19.0 s |

    Exit 0, and the CONTEXT SUMMARY reads [* Axioms: <none>] with no mention of
    the VM.  So the *report* is blind in both tools; the difference is that
    [coqchk] does not take the VM's word for it, at about 16x the cost of the
    proof it is checking.

    And that ratio is the whole problem, because it applies to the size the
    hatch exists for.  [coqchk] on *this file* -- whose [kernel_ran_the_vm] runs
    at 30 000 000 iterations, and which [coqc] accepts in 3.7 s -- did not
    finish inside 400 s (exit 124).  ../verify.ps1 therefore [coqchk]s the
    cut-down companion and not this file, which is itself the measurement: a
    development that uses [vm_compute] because it must is, by construction, a
    development [coqchk] cannot practically check.  That is the honest reason
    the backstop is rarely run over such proofs, and it is not recorded
    upstream.  Contrast ../../KernelDefects/Coq/ModuleSystem/UniverseFlagDesync.v,
    where [coqchk] rejects the [.vo] outright and cheaply: there the backstop
    works, here it merely exists. *)

(** ** 7. Version matrix, and what this hatch has cost historically

    The route is not hypothetical.  rocq-prover/rocq#21736 -- [Register Inline]
    with universe polymorphism, where the VM's lambda generation failed to
    substitute the universe instance -- let [vm_cast_no_check] prove
    [Type@{v} = Type@{u}] and hence Hurkens, on *every patch release from 8.5 to
    9.1, and through [coqchk] too*.  Fixed in 9.2.0.

    Measured here on that surface.  The probe is six lines: a polymorphic
    [U@{u v | u < v} : Type@{v} := Type@{u}], then [Register Inline U], then
    [vm_cast_no_check (@eq_refl Type@{k} U@{j k})] at type [U@{j k} = U@{i k}]
    with [i < j < k].

      | Rocq  | verdict                                                       |
      | ----- | ------------------------------------------------------------- |
      | 9.0.1 | Anomaly "File kernel/vmbytegen.ml, line 942, characters 15-21: |
      |       | Assertion failed."  exit 129 -- the process dies              |
      | 9.2   | rejected: Unable to unify "Type@{i}" with "Type@{j}"  exit 1   |

    CONTROL: the identical file with the [Register Inline] line deleted is
    rejected on both, with the same message and exit 1, which pins the trigger
    on [Register Inline] and not on universe polymorphism.  On 9.0.1 the surface
    is total -- even [Eval vm_compute in U@{i k}] anomalies, and so does
    [native_cast_no_check] via the fallback of section 4; 9.2 evaluates it
    correctly to [Type@{i}].

    Note what holds the line on 9.0.1: an OCaml [assert].  Assertions are
    removable at build time, and a build configured with [-noassert] would
    miscompile silently rather than abort.  That is the same shape as
    lean4#8554, where a non-aborting [panic!] left four conservative [Expr]
    flags unconservative -- and it is why "the assertion caught it" is a weaker
    statement than it looks.

    Still open upstream and not attempted here: #16891 (VM/native memory
    corruption on ill-typed terms via [exact_no_check]) and #13439 (VM buffer
    overflow).

    *** What was searched for and not found.  A differential audit of the VM
    against ordinary kernel conversion over all four primitive families -- 31
    [PrimInt63] operations at 15 boundary operands, 17 [PrimFloat] operations at
    15 values including both zeros, both infinities and NaN, [PrimString] (new
    in 9.0) at and past its [max_length] of 16 777 211, and [PArray] at and past
    its [max_length] of 4 194 303 -- found 0 divergences in 15 989 comparisons.
    Each comparison is the kernel's own: the VM's answer is frozen with
    [Eval vm_compute in], and [change_no_check] then forces [Qed] to re-derive
    the same list with ordinary conversion.  Harness proposed as
    ../../Audits/Coq/ConversionMachines/VmVsOrdinary.v. *)

