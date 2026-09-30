(* GLM worker 1 — neutral and desc_against are stable under                 *)
(* same-substituent substitution.                                           *)
(*                                                                          *)
(* neutral needs `neutral u`: subst u k (TVar k) = lift k 0 u, and that is   *)
(* neutral exactly by neutral_lift_glm applied to u itself.                 *)
(* desc_against needs only eval_subst_glm: every constructor inspects       *)
(* evaluated forms, never neutrals.                                         *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_subst_reduction_bundle_eval.
Require Import _glm_neutral_lift.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Theorem neutral_subst_glm : forall t, neutral t -> forall u k,
    neutral u -> neutral (subst u k t).
Proof.
  intros t H.
  induction H as
    [ n
    | f a Hf IHf
    | p Hp IHp
    | p Hp IHp
    | E P e x He IHe
    | R P stp i x Hx IHx
    | M Q bs HM IHM ]; intros u k Hu; cbn [subst].
  - (* ne_var *)
    destruct (Nat.ltb n k) eqn:Hlt; [apply ne_var |].
    destruct (Nat.eqb n k) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst n.
      exact (neutral_lift_glm u Hu k 0).
    + apply ne_var.
  - apply ne_app; auto.
  - apply ne_fst; auto.
  - apply ne_snd; auto.
  - apply ne_switch; auto.
  - apply ne_ind; auto.
  - apply ne_case; auto.
Qed.

Theorem desc_against_subst_glm : forall D, desc_against D -> forall u k,
    desc_against (subst u k D).
Proof.
  intros D H.
  induction H as
    [ D0 E T Hnil Hecons
    | D0 A B HprodL HdescL IHprodL
    | D0 A B HprodR HdescR IHprodR
    | D0 E T tg E' Hch Hecons Hzero IHzero Hcons IHcons ]; intros u k; cbn.
  - (* ag_choice_nil *)
    apply (@ag_choice_nil (subst u k D0) (subst u k E) (subst u k T)).
    + exact (eval_subst_glm _ _ Hnil u k).
    + exact (eval_subst_glm _ _ Hecons u k).
  - (* ag_prod_left *)
    apply (@ag_prod_left (subst u k D0) (subst u k A) (subst u k B)).
    + exact (eval_subst_glm _ _ HprodL u k).
    + exact (IHprodL u k).
  - (* ag_prod_right *)
    apply (@ag_prod_right (subst u k D0) (subst u k A) (subst u k B)).
    + exact (eval_subst_glm _ _ HprodR u k).
    + exact (IHprodR u k).
  - (* ag_choice_cons *)
    apply (@ag_choice_cons (subst u k D0) (subst u k E) (subst u k T)
                            (subst u k tg) (subst u k E')).
    + exact (eval_subst_glm _ _ Hch u k).
    + exact (eval_subst_glm _ _ Hecons u k).
    + exact (IHzero u k).
    + rewrite <- (subst_lift_one_zero T u k). exact (IHcons u k).
Qed.
