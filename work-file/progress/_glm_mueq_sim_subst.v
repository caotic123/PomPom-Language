(* GLM worker 4 — mueq simulation infrastructure, part 2: substitution.      *)
(*                                                                          *)
(* mueq/mubeq substitution under a conditional conv_subst compatibility      *)
(* premise.  Lifting is already unconditional here (part 1 discharged it    *)
(* with conv_lift_glm), so the only remaining premise is the subst          *)
(* compatibility of conv, which awaits worker 1's conv-subst bundle.        *)
(*                                                                          *)
(* As in part 1, this re-derives the subst layer of _luna_mueq_subst.v       *)
(* (which does not kernel-check on this toolchain: Nat.lt_trichotomy used    *)
(* without importing PeanoNat), with the import fixed and _glm-suffixed     *)
(* names.                                                                   *)

Require Import Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations TypeRules.
Require Import _luna_mueq _luna_mueq_equiv.
Require Import _glm_mueq_sim_lift.

(* Conditional premise: substitution commutes with conversion.  Until
   worker 1 provides a closed conv_subst bundle, every subst-level result
   below quantifies over this premise explicitly (no global assumptions). *)
Definition conv_subst_compatible : Prop :=
  forall t t' u u', conv t t' -> conv u u' -> forall k,
    conv (subst u k t) (subst u' k t').

(* The named premise carried by the simulation modules. *)
Definition mueq_subst_premise_glm : Prop := conv_subst_compatible.

Definition subst_mubeq_branches (u : term) (k : nat)
    (bs : list (term * term)) : list (term * term) :=
  map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs.

Lemma mueq_subst_var_glm : forall n u u' k, mueq u u' ->
    mueq (subst u k (TVar n)) (subst u' k (TVar n)).
Proof.
  intros n u u' k Huu'.
  destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
  - assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
    cbn [subst]. rewrite Hlt. constructor.
  - subst n.
    assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [subst]. rewrite Hlt, Heq.
    eapply mueq_lift_glm; eauto.
  - assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
    cbn [subst]. rewrite Hlt, Heq. constructor.
Qed.

Lemma mueq_subst_mut :
  conv_subst_compatible ->
  ((forall t t', mueq t t' -> forall u u' k,
      mueq u u' -> mueq (subst u k t) (subst u' k t')) /\
   (forall bs bs', mubeq bs bs' -> forall u u' k,
      mueq u u' ->
      mubeq (subst_mubeq_branches u k bs)
            (subst_mubeq_branches u' k bs'))).
Proof.
  intros Hsubst.
  unfold conv_subst_compatible in Hsubst.
  apply (mueq_mubeq_ind
    (fun (t t' : term) (_ : mueq t t') =>
      forall (u u' : term) (k : nat), mueq u u' ->
        mueq (subst u k t) (subst u' k t'))
    (fun (bs bs' : list (term * term)) (_ : mubeq bs bs') =>
      forall (u u' : term) (k : nat), mueq u u' ->
        mubeq (subst_mubeq_branches u k bs)
              (subst_mubeq_branches u' k bs')));
    cbn [subst_mubeq_branches]; intros.
  all: try solve [eapply mueq_subst_var_glm; eauto].
  all: try solve [unfold subst_mubeq_branches; cbn [map]; constructor; eauto].
  all: try solve [constructor].
  all: try solve [constructor; eauto].
  all: try solve [
    match goal with
    | Hm : mueq ?uu ?uu',
      hc : conv (TApp (TMuS ?S1) ?i1) (TApp (TMuS ?S2) ?i2),
      kk : nat |- _ =>
        refine (me_muapp _ _ _ _ (Hsubst _ _ _ _ hc (mueq_conv _ _ Hm) kk))
    end].
Qed.

Lemma mueq_subst_glm : conv_subst_compatible ->
  forall t t' u u' k, mueq t t' -> mueq u u' ->
    mueq (subst u k t) (subst u' k t').
Proof.
  intros Hsubst t t' u u' k Htt' Huu'.
  exact (proj1 (mueq_subst_mut Hsubst) t t' Htt' u u' k Huu').
Qed.

Lemma mubeq_subst_glm : conv_subst_compatible ->
  forall bs bs' u u' k, mubeq bs bs' -> mueq u u' ->
    mubeq (subst_mubeq_branches u k bs)
          (subst_mubeq_branches u' k bs').
Proof.
  intros Hsubst bs bs' u u' k Hbs Huu'.
  exact (proj2 (mueq_subst_mut Hsubst) bs bs' Hbs u u' k Huu').
Qed.

(* mueq substitution commutes with the TCase branch map, for reuse. *)
Lemma mueq_case_subst_glm : conv_subst_compatible ->
  forall M M' Q Q' bs bs' u u' k,
    mueq M M' -> mueq Q Q' -> mubeq bs bs' -> mueq u u' ->
    mueq (TCase (subst u k M) (subst u k Q) (subst_mubeq_branches u k bs))
         (TCase (subst u' k M') (subst u' k Q') (subst_mubeq_branches u' k bs')).
Proof.
  intros Hcompat M M' Q Q' bs bs' u u' k HM HQ Hbs Hu.
  apply me_case;
    [exact (mueq_subst_glm Hcompat _ _ _ _ k HM Hu)
    |exact (mueq_subst_glm Hcompat _ _ _ _ k HQ Hu)
    |exact (mubeq_subst_glm Hcompat _ _ _ _ k Hbs Hu)].
Qed.
