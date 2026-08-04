(** * Univalence + UIP, and why Rocq needs both where Lean needs one

    PARADOX (see ../README.md): the cost is a hypothesis in the *statement*.
    [univalence_uip_false] is axiom-free — [Print Assumptions] says
    [Closed under the global context] — and it is a negative result about type
    theory, never a defect in Rocq.

    ** The asymmetry this file exists to record

    The classical inconsistency is univalence together with UIP (uniqueness of
    identity proofs, Streicher's axiom K).  Univalence makes [bool = bool]
    inhabited by the swap as well as by [eq_refl]; UIP says those are the same
    proof; transport along the swap sends [true] to [false] and along [eq_refl]
    to [true].

    **Rocq needs both hypotheses.  Lean needs only univalence.**  §1 below is the
    machine-checked reason: Rocq refuses all three judgments that Lean accepts by
    [rfl], because Rocq's [Prop] is not definitionally proof-irrelevant.  That is
    exactly why HoTT can be developed in Rocq and cannot be developed in Lean,
    and it is the sharpest single difference between the two systems in this
    whole repository.

    The Lean counterpart is
    ../Lean/TypeTheoryParadoxes/Univalence.lean, whose §1 shows the same three
    judgments *succeeding*. *)

(** ** 1. UIP is NOT definitional in Rocq

    Each [Fail] below is an assertion: the command it wraps must be rejected.
    In Lean the corresponding three lines are accepted by [rfl]. *)

Fail Example uip_defn (h1 h2 : (bool : Type) = bool) : h1 = h2 := eq_refl.
Fail Example uip_refl (h : (bool : Type) = bool) : h = eq_refl := eq_refl.
Fail Example cast_id (h : (bool : Type) = bool) (b : bool) :
  eq_rect _ (fun T : Type => T) b _ h = b := eq_refl.

(** ** 2. The two hypotheses *)

Record Bijection (A B : Type) := {
  toFun  : A -> B;
  invFun : B -> A;
  bleft  : forall a, invFun (toFun a) = a;
  bright : forall b, toFun (invFun b) = b
}.
Arguments toFun {A B}.

(** The univalence ingredient: bijections yield equalities, and transport along
    such an equality computes.  Weaker than full univalence, so refuting it
    refutes univalence a fortiori.  A [Record], not an [Axiom] — the cost lives
    in the type of the theorem, and the audit stays clean. *)
Record Univalence := {
  ua      : forall {A B : Type}, Bijection A B -> A = B;
  ua_cast : forall {A B : Type} (e : Bijection A B) (a : A),
              eq_rect A (fun T : Type => T) a B (ua e) = toFun e a
}.

(** The second ingredient, which Lean gets for free from proof irrelevance. *)
Definition UIP := forall (A : Type) (x y : A) (p q : x = y), p = q.

(** Boolean negation is a bijection — the swap the classical argument uses. *)
Definition notBij : Bijection bool bool.
Proof. refine {| toFun := negb; invFun := negb |}; intros []; reflexivity. Defined.

(** ** 3. [False] *)

Theorem univalence_uip_false (U : Univalence) (K : UIP) : False.
Proof.
  pose proof (ua_cast U notBij true) as H.
  (* H : eq_rect _ _ true _ (ua U notBij) = negb true, i.e. ... = false *)
  rewrite (K Type bool bool (ua U notBij) eq_refl) in H.
  (* UIP collapses the swap to eq_refl, and transport along eq_refl is trivial *)
  simpl in H.
  discriminate H.
Qed.

(** [Closed under the global context] *)
Print Assumptions univalence_uip_false.

(** ** 4. Neither hypothesis alone is enough here

    This is what makes the Rocq statement genuinely two-premise, and it is worth
    stating because the Lean file's one-premise version can otherwise look like
    the same theorem.

    - Univalence alone is consistent with Rocq: that is the HoTT model, and
      whole libraries are built on it.
    - UIP alone is consistent with Rocq: it is provable for types with decidable
      equality ([Stdlib.Logic.Eqdep_dec]) and consistent in general.

    So neither is refutable, and §3 refutes only their conjunction.  In Lean §1's
    three judgments make UIP a *theorem*, so the conjunction degenerates and
    univalence alone is refuted.

    The choice underneath is proof irrelevance, and it is deliberate on both
    sides: Lean takes it and gives up univalence; Rocq declines it and keeps
    both options open. *)
