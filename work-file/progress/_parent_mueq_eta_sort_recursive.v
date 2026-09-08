(* The root-eta case for a well-founded sort-transport proof. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cstep_invariants
  _luna_mueq _glm_mueq_eta_shape _luna_cjoin_congr
  _parent_mus_cstep_inv.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Definition mueq_sort_transport_below_parent (N : nat) : Prop :=
  forall t u j,
    tsize t < N -> mueq t u -> rtc cstep t (TSort j) ->
    rtc cstep u (TSort j).

Lemma rtc_cstep_lift_parent : forall t u,
    rtc cstep t u -> forall d k,
    rtc cstep (lift d k t) (lift d k u).
Proof.
  intros t u H d k.
  eapply rtc_cstep_congr1 with (F := fun q => lift d k q).
  - intros x y Hxy. eapply pstep_lift; eassumption.
  - intros x y Hxy. eapply epstep_lift; eassumption.
  - exact H.
Qed.

Lemma rtc_cstep_eta_context_parent : forall f j,
    rtc cstep f (TSort j) ->
    rtc cstep
      (TLam (TApp f (TVar 0)))
      (TLam (TApp (TSort j) (TVar 0))).
Proof.
  intros f j H.
  eapply rtc_cstep_congr1
    with (F := fun q => TLam (TApp q (TVar 0))).
  - intros x y Hxy. apply ps_lam, ps_app.
    + exact Hxy.
    + apply pstep_refl.
  - intros x y Hxy. apply eps_lam, eps_app.
    + exact Hxy.
    + apply epstep_refl.
  - exact H.
Qed.

Lemma eta_sort_contract_parent : forall j,
    cstep (TLam (TApp (TSort j) (TVar 0))) (TSort j).
Proof.
  intros j. apply cs_eta, rtc_one.
  change (epstep (TLam (TApp (lift 1 0 (TSort j)) (TVar 0))) (TSort j)).
  apply eps_eta, epstep_refl.
Qed.

Lemma eta_contractum_reaches_sort_parent : forall f j,
    rtc cstep
      (TLam (TApp (lift 1 0 f) (TVar 0)))
      (TSort j) ->
    rtc cstep f (TSort j).
Proof.
  intros f j Hsort.
  assert (Heta : rtc cstep
      (TLam (TApp (lift 1 0 f) (TVar 0))) f).
  { apply rtc_one, epstep_cstep, eps_eta, epstep_refl. }
  destruct (cstep_confluent _ _ _ Heta Hsort) as [w [Hfw Hsw]].
  rewrite (rtc_cstep_sort_id _ _ Hsw) in Hfw. exact Hfw.
Qed.

Theorem mueq_eta_root_sort_recursive_parent : forall f u j,
    mueq_sort_transport_below_parent
      (tsize (TLam (TApp (lift 1 0 f) (TVar 0)))) ->
    mueq (TLam (TApp (lift 1 0 f) (TVar 0))) u ->
    rtc cstep f (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros f u j IH Hm Hsort.
  destruct (mueq_lam_inv_glm _ _ Hm) as [b' [Hu Hb]].
  subst u.
  destruct (mueq_tapp_inv_glm (lift 1 0 f) (TVar 0) b' Hb)
    as [[S1 [S2 [i1 [i2 [Hhead [_ [_ _]]]]]]]
       | [f2 [a2 [Hb' [Hf2 Ha2]]]]].
  - destruct (lift1_tmus_head_inv_glm f S1 Hhead) as [S0 Hf].
    subst f. exfalso. exact (rtc_cstep_mus_not_sort_parent S0 j Hsort).
  - subst b'.
    rewrite (mueq_var0_inv_glm _ Ha2).
    assert (Hlift : rtc cstep (lift 1 0 f) (TSort j)).
    { change (rtc cstep (lift 1 0 f) (lift 1 0 (TSort j))).
      eapply rtc_cstep_lift_parent; exact Hsort. }
    assert (Hsmall :
      tsize (lift 1 0 f) <
      tsize (TLam (TApp (lift 1 0 f) (TVar 0)))).
    { cbn [tsize]. lia. }
    pose proof (IH (lift 1 0 f) f2 j Hsmall Hf2 Hlift) as Hf2sort.
    eapply rtc_trans.
    + exact (rtc_cstep_eta_context_parent f2 j Hf2sort).
    + apply rtc_one, eta_sort_contract_parent.
Qed.

Corollary mueq_eta_redex_sort_recursive_parent : forall f u j,
    mueq_sort_transport_below_parent
      (tsize (TLam (TApp (lift 1 0 f) (TVar 0)))) ->
    mueq (TLam (TApp (lift 1 0 f) (TVar 0))) u ->
    rtc cstep (TLam (TApp (lift 1 0 f) (TVar 0))) (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros f u j IH Hm Hsort.
  eapply mueq_eta_root_sort_recursive_parent; [exact IH | exact Hm |].
  eapply eta_contractum_reaches_sort_parent; exact Hsort.
Qed.

Print Assumptions rtc_cstep_lift_parent.
Print Assumptions mueq_eta_root_sort_recursive_parent.
Print Assumptions mueq_eta_redex_sort_recursive_parent.
