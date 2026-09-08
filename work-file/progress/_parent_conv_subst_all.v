(* Arbitrary-cutoff conversion substitution via fresh-variable lambda
   cancellation, avoiding induction over the cv_phi constructor. *)

Require Import Progress _glm_conv_lift_bundle_main _glm_conv_subst0
  _tmp_eta_cancel.
From Stdlib Require Import List Arith Lia.
Import ListNotations TypeRules.

Lemma conv_lam_inj_parent : forall b b',
    conv (TLam b) (TLam b') -> conv b b'.
Proof.
  intros b b' Hlam.
  pose proof (conv_lift_glm _ _ Hlam 1 0) as Hlift.
  cbn [lift] in Hlift.
  assert (Happ :
    conv (TApp (TLam (lift 1 1 b)) (TVar 0))
         (TApp (TLam (lift 1 1 b')) (TVar 0))).
  { apply cv_app; [exact Hlift | apply cv_refl]. }
  assert (Hbeta_left :
    conv (TApp (TLam (lift 1 1 b)) (TVar 0)) b).
  { assert (Hraw :
      conv (TApp (TLam (lift 1 1 b)) (TVar 0))
           (subst (TVar 0) 0 (lift 1 1 b))).
    { apply cv_step, st_beta. }
    rewrite (subst_eta_beta_cancel b) in Hraw. exact Hraw. }
  assert (Hbeta_right :
    conv (TApp (TLam (lift 1 1 b')) (TVar 0)) b').
  { assert (Hraw :
      conv (TApp (TLam (lift 1 1 b')) (TVar 0))
           (subst (TVar 0) 0 (lift 1 1 b'))).
    { apply cv_step, st_beta. }
    rewrite (subst_eta_beta_cancel b') in Hraw. exact Hraw. }
  eapply cv_trans.
  - apply cv_sym. exact Hbeta_left.
  - eapply cv_trans; [exact Happ | exact Hbeta_right].
Qed.

Theorem conv_subst_all_parent : forall k t t' a a',
    conv t t' -> conv a a' ->
    conv (subst a k t) (subst a' k t').
Proof.
  induction k as [|k IH]; intros t t' a a' Ht Ha.
  - exact (conv_subst0_glm t t' a a' Ht Ha).
  - apply conv_lam_inj_parent.
    change (conv (subst a k (TLam t)) (subst a' k (TLam t'))).
    apply IH.
    + apply cv_lam. exact Ht.
    + exact Ha.
Qed.

Corollary conv_subst_compatible_parent :
    forall t t' u u', conv t t' -> conv u u' -> forall k,
      conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu k.
  exact (conv_subst_all_parent k t t' u u' Ht Hu).
Qed.

Print Assumptions conv_lam_inj_parent.
Print Assumptions conv_subst_all_parent.
Print Assumptions conv_subst_compatible_parent.
