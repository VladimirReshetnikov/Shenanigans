(** * Controls for LetinRelevanceShift.v -- where the window starts and stops

    rocq#22378.  Acceptance of the exhibit means nothing on its own: `eq_refl`
    is accepted for a great many honest reasons.  What makes the exhibit a
    measurement is that the *same procedure*, on the *same toolchain*, refuses
    eleven neighbouring arrangements -- and refuses them in the kernel, not in
    the elaborator.

    THIS FILE IS EXPECTED TO BE **ACCEPTED**, exit code 0.  There are twelve
    refusal sites -- §1 contributes two -- and every one of them is wrapped in
    `Fail`, so an arrangement that stopped being refused would turn this file
    into an exit-1 failure rather than passing silently.  Four constructions are
    *supposed* to be accepted and are stated plainly: `inner_pair_collapses`
    (§1), `Machines.vm_alive`, `Machines.vm_stuck_ok` and `Machines.lazy_lane`
    (§11).  The two that carry the finding, `inner_pair_collapses` and
    `lazy_lane`, are followed by `Print Assumptions`.

    ** Reading the rejection messages: which component refused

    Every control here states its goal with
    `ltac:(exact_no_check (@eq_refl _ ...))` rather than with a bare `eq_refl`,
    and the reason is visible in the message.  Spelled `eq_refl`, the same
    control is refused by the *elaborator*:

        In environment
        p : pair_with_lets
        The term "eq_refl" has type "left p = left p"
        while it is expected to have type "left p = right p" (cannot unify
        "left p" and "right p").

    Spelled `exact_no_check`, the elaborator is bypassed and the term reaches
    the kernel, which refuses it with the *same* sentence minus the parenthesis:

        The term "fun p : pair_with_lets => eq_refl" has type
         "forall p : pair_with_lets, left p = left p"
        while it is expected to have type
         "forall p : pair_with_lets, left p = right p".

    The trailing `(cannot unify ... and ...)` is the elaborator's; its absence is
    how one reads off that the kernel itself declined.  **Controls 2 through 9
    below each produce that second message verbatim**, with the identifiers of
    their own section substituted -- §9 substitutes `zero` for `right`, which is
    the only substitution that is not a module name -- so it is quoted once here
    rather than eight times.  Controls 1, 10 and 11 do *not* produce it: §10's
    scrutinee is closed, so neither side is under a binder and the message has no
    `fun`/`forall` in it, and §11's comes from the VM at `Qed`.  All three quote
    their own messages in place.

    ** What each control removes

      1.  nothing at all -- only the projection index moves          (§1)
      2.  one of the two local definitions                           (§2)
      3.  the `:=`, so the two `SProp` binders become arguments      (§3)
      4.  the innermost local definition's `SProp`, made `Prop`      (§4)
      5.  the outermost local definition's `SProp`, made `Prop`      (§5)
      6.  the position: the local definitions come first             (§6)
      7.  the position: the local definitions are interleaved        (§7)
      8.  `SProp` altogether: the local definitions live in `Set`    (§8)
      9.  one of the two sides from the window                       (§9)
      10. the stuck scrutinee, so iota fires first                   (§10)
      11. the lazy machine, replaced by the VM on the same term      (§11)

    Section 1 is the load-bearing one and it is stronger than a one-token
    control: **not one token of the program changes.**  The same constructor,
    the same three projections, the same file -- and `snd3 = thd3` is accepted
    while `fst3 = snd3` is refused.  The only difference between the accepted
    statement and the refused one is which of three arguments is named.  That
    pins the defect to a *window of de Bruijn positions* rather than to
    "constructors with local definitions are broken", and upstream's report,
    which has two arguments and therefore no inside and outside, cannot state
    it.

    ** A note on the slot-by-slot commentary below

    Each section says which de Bruijn slot ends up carrying which relevance
    annotation.  That arithmetic is a *reading of upstream's stated mechanism*
    -- quoted in LetinRelevanceShift.v -- against the verdicts measured here,
    and the two agree in all eleven cases.  It is **not** an inspection of
    `kernel/conversion.ml`: no Rocq sources are installed on this machine and
    none were read.  The verdicts and the quoted messages are measured; the slot
    arithmetic offered as their explanation is not. *)

Inductive sUnit : SProp := stt.
Inductive pUnit : Prop  := ptt.

(** ** 1. The window -- three arguments, two local definitions

    `k = 2` local definitions, `n = 3` real arguments.  The window covers the
    innermost two, `y` and `z`.  Nothing about the constructor changes between
    the accepted line and the refused ones. *)

Inductive triple_with_lets : Type :=
| pack3 (x y z : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).

Definition fst3 (t : triple_with_lets) : nat := match t with pack3 x y z => x end.
Definition snd3 (t : triple_with_lets) : nat := match t with pack3 x y z => y end.
Definition thd3 (t : triple_with_lets) : nat := match t with pack3 x y z => z end.

(** Inside the window: ACCEPTED. *)
Definition inner_pair_collapses (t : triple_with_lets) : snd3 t = thd3 t :=
  ltac:(exact_no_check (@eq_refl _ (snd3 t))).

Check inner_pair_collapses.
(** Expected: `Closed under the global context`. *)
Print Assumptions inner_pair_collapses.

(** One position further out: REFUSED.

        The term "fun t : triple_with_lets => eq_refl" has type
         "forall t : triple_with_lets, fst3 t = fst3 t"
        while it is expected to have type
         "forall t : triple_with_lets, fst3 t = snd3 t". *)
Fail Definition outer_pair (t : triple_with_lets) : fst3 t = snd3 t :=
  ltac:(exact_no_check (@eq_refl _ (fst3 t))).

(** Straddling the window: REFUSED, same message with `thd3` for `snd3`.

        The term "fun t : triple_with_lets => eq_refl" has type
         "forall t : triple_with_lets, fst3 t = fst3 t"
        while it is expected to have type
         "forall t : triple_with_lets, fst3 t = thd3 t". *)
Fail Definition straddling_pair (t : triple_with_lets) : fst3 t = thd3 t :=
  ltac:(exact_no_check (@eq_refl _ (fst3 t))).

(** ** 2. One local definition instead of two

    `k = 1` moves the window down to a single position, and a single position
    holds no *pair*, so nothing is convertible that should not be.  This is the
    answer to "does one `SProp` local definition suffice?" -- it does not. *)

Module OneLet.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End OneLet.

(** ** 3. `:=` becomes `:` -- the same two `SProp` binders, as arguments

    The binders keep their type and their `SProp` sort and their position; they
    simply stop being local definitions.  Nothing is then substituted away, so
    nothing is lifted, so no annotation lands on the wrong slot.  This is the
    answer to "is it the `SProp`, or is it the letin?" -- it is the letin. *)

Module Arguments_.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit) (ghost2 : sUnit).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y g1 g2 => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y g1 g2 => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End Arguments_.

(** ** 4. The innermost local definition retyped `SProp` -> `Prop`

    One identifier changes -- `sUnit := stt` becomes `pUnit := ptt` on `ghost2`
    only.  The lift is unchanged, two annotations are still pushed for two
    substituted binders, and the innermost slot now carries a *relevant*
    annotation.  The pair is broken.  So it is not the count of local
    definitions that matters but the sorts they carry. *)

Module InnerProp.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : pUnit := ptt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End InnerProp.

(** ** 5. The outermost local definition retyped `SProp` -> `Prop`

    The mirror of §4, on `ghost1`.  Refused as well: both slots of the pair have
    to be marked irrelevant, and here only one is. *)

Module OuterProp.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : pUnit := ptt) (ghost2 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End OuterProp.

(** ** 6. The local definitions moved in front of the `nat` arguments

    Same four binders, same sorts, same `:=`; only the declaration order
    changes.  Now the two irrelevant annotations land past the two real
    arguments instead of on top of them, and the collapse disappears.  This is
    the answer to "does reordering the binders kill it?" -- it does. *)

Module LetsFirst.
  Inductive pair_with_lets : Type :=
  | pack (ghost1 : sUnit := stt) (ghost2 : sUnit := stt) (x y : nat).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End LetsFirst.

(** ** 7. The local definitions interleaved with the `nat` arguments

    `x`, `ghost1`, `y`, `ghost2`.  Two local definitions again, both `SProp`,
    both `:=`, and still refused: the shift is by two but only the innermost
    slot is marked irrelevant, so the pair is again split. *)

Module Interleaved.
  Inductive pair_with_lets : Type :=
  | pack (x : nat) (ghost1 : sUnit := stt) (y : nat) (ghost2 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End Interleaved.

(** ** 8. Local definitions that are not in `SProp` at all

    Two trailing local definitions in `Set`.  They are substituted away exactly
    as the `SProp` ones are, and the lift is exactly the same -- but the
    annotations that get pushed onto the wrong slots are `Relevant`, so pushing
    them there is harmless.  This is the answer to "does any letin do?" -- no;
    the misplaced annotations have to be irrelevant ones. *)

Module SetLets.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : nat := O) (ghost2 : nat := O).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision (p : pair_with_lets) : left p = right p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End SetLets.

(** ** 9. Only one side of the comparison sits in the window

    The exhibit's own constructor, unchanged.  `right` is replaced by the branch
    that returns the literal `O`, which is a constructor application and
    relevant.  Refused -- so the rule is "both heads are read as irrelevant",
    not "an index is off by two".  Without this control the exhibit would be
    consistent with a plain de Bruijn misalignment, which is a different defect
    with a different set of reachable consequences. *)

Module OneSided.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition zero  (p : pair_with_lets) : nat := match p with pack x y => O end.
  Fail Definition collision (p : pair_with_lets) : left p = zero p :=
    ltac:(exact_no_check (@eq_refl _ (left p))).
End OneSided.

(** ** 10. The scrutinee is closed, so iota fires before the branches are compared

    The exhibit's constructor and projections, applied to `pack 0 1` instead of
    a variable.  Both matches reduce, the branch contexts are never entered, and
    the kernel compares `0` with `1` honestly.  REFUSED:

        The term "eq_refl" has type "left (pack 0 1) = left (pack 0 1)"
        while it is expected to have type "left (pack 0 1) = right (pack 0 1)".

    So the defect lives in the comparison of two *stuck* matches.  It is not
    reachable by evaluating anything. *)

Module ClosedScrutinee.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.
  Fail Definition collision : left (pack O (S O)) = right (pack O (S O)) :=
    ltac:(exact_no_check (@eq_refl _ (left (pack O (S O))))).
End ClosedScrutinee.

(** ** 11. The VM refuses what the lazy machine accepts

    The strongest measurement in this file, and the one that belongs in the
    catalog row.  One file, one constructor, one term -- `@eq_refl _ (left p)`
    cast to `left p = right p` -- handed to the kernel twice, over the two
    conversion machines the kernel actually ships.

      `exact_no_check`     lazy machine   ACCEPTED, `Closed under the global
                                          context`
      `vm_cast_no_check`   VM             REFUSED, at `Qed`

    The VM's refusal lands at `Qed.` and not at the tactic, because
    `vm_cast_no_check` defers the conversion to proof-checking time -- the same
    place, for the same reason, as the rejection in RegisterInlineVM.v.  There
    it was the VM that was wrong and the lazy machine that held; here the roles
    are exactly swapped.

    `vm_alive` is in this file so that the refusal cannot be read as the VM lane
    being absent: it is a conversion the VM has to actually compute, on this
    switch, in this file, and it succeeds.  (The native lane is not measured --
    the native compiler is disabled in this switch, so `native_compute` falls
    back to the VM and would report the VM's verdict under another name.)

    The VM's message, at `Qed`:

        In environment
        p : pair_with_lets
        The term "eq_refl" has type "left p = left p"
        while it is expected to have type "left p = right p". *)

Module Machines.
  Inductive pair_with_lets : Type :=
  | pack (x y : nat) (ghost1 : sUnit := stt) (ghost2 : sUnit := stt).
  Definition left  (p : pair_with_lets) : nat := match p with pack x y => x end.
  Definition right (p : pair_with_lets) : nat := match p with pack x y => y end.

  (** The VM lane is live and does real work here. *)
  Lemma vm_alive : 30 * 30 = 900.
  Proof. vm_cast_no_check (@eq_refl nat 900). Qed.

  (** And it handles *this* inductive and *this* stuck match without
      complaint, so its refusal below is a verdict on the conversion and not
      a failure to compile the term. *)
  Lemma vm_stuck_ok (p : pair_with_lets) : left p = left p.
  Proof. vm_cast_no_check (@eq_refl _ (left p)). Qed.

  (** The VM refuses the exhibit's conversion. *)
  Lemma vm_lane (p : pair_with_lets) : left p = right p.
  Proof. vm_cast_no_check (@eq_refl _ (left p)).
  Fail Qed.
  Abort.

  (** The lazy machine accepts it, in the same file, on the same term. *)
  Lemma lazy_lane (p : pair_with_lets) : left p = right p.
  Proof. exact_no_check (@eq_refl _ (left p)). Qed.

  (** Expected: `Closed under the global context`. *)
  Print Assumptions lazy_lane.
End Machines.
