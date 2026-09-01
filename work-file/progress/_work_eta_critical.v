Require Import Progress _tmp_epstep _tmp_pstep_var_rigid _tmp_eta_cancel
  _work_pstep_lift_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Definition eta_app (f : term) : term :=
  TApp (lift 1 0 f) (TVar 0).

Lemma pstep_eta_app_cases : forall f q,
    pstep (eta_app f) q ->
    (exists g, q = eta_app g /\ pstep f g) \/
    (exists b b', f = TLam b /\ q = b' /\ pstep b b').
Proof.
  intros f q H. unfold eta_app in H.
  inversion H; subst.
  - assert (Ha : a' = TVar 0) by (eapply pstep_var_rigid; eassumption).
    subst a'.
    destruct (pstep_lift_inv f 0 f' H2) as [g [Hg Hfg]].
    subst f'. left. exists g. split; [reflexivity | exact Hfg].
  - destruct f; cbn [lift] in H0; try discriminate.
    inversion H0; subst b; clear H0.
    assert (Ha : a' = TVar 0) by (eapply pstep_var_rigid; eassumption).
    subst a'.
    destruct (pstep_lift_inv f 1 b' H2) as [bd [Hbd Hpbd]].
    subst b'. rewrite subst_eta_beta_cancel.
    right. exists f, bd. repeat split; assumption.
Qed.

Lemma rtc_epstep_lam : forall a b,
    rtc epstep a b -> rtc epstep (TLam a) (TLam b).
Proof.
  intros a b H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply eps_lam; exact H | exact IHrtc].
Qed.

Lemma eta_lambda_critical_rtc : forall f u b',
    epstep f u ->
    (forall z, epstep (eta_app f) z ->
      exists q, rtc epstep b' q /\ pstep z q) ->
    exists v, rtc epstep (TLam b') v /\ pstep u v.
Proof.
  intros f u b' Hfu IH.
  assert (Hbody : epstep (eta_app f) (eta_app u)).
  { unfold eta_app. constructor.
    - eapply epstep_lift. exact Hfu.
    - constructor. }
  destruct (IH _ Hbody) as [q [Hbq Huq]].
  destruct (pstep_eta_app_cases u q Huq) as
    [[g [Hq Hug]] | [body [body' [Hu [Hq Hbodycore]]]]].
  - subst q. exists g. split; [|exact Hug].
    eapply rtc_trans.
    + apply rtc_epstep_lam. exact Hbq.
    + apply rtc_one. unfold eta_app. apply eps_eta, epstep_refl.
  - subst u q. exists (TLam body'). split.
    + apply rtc_epstep_lam. exact Hbq.
    + apply ps_lam. exact Hbodycore.
Qed.
