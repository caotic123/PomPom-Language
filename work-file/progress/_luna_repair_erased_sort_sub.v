Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.
Import TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants
  Progress._work_conv_whd_pos Progress._luna_phi_erase_shapes.

Definition erased_sort (T : term) : Prop :=
  exists j, cjoin (phi_erase T) (TSort j).

Lemma erased_sort_sub : forall G T U, sub G T U ->
    erased_sort T -> erased_sort U.
Proof.
  intros G T U Hsub. induction Hsub; intros [n Hn].
  - (* conversion *)
    exists n. eapply cjoin_trans.
    + apply cjoin_sym. apply conv_phi_cjoin. exact H.
    + exact Hn.
  - (* transitivity *)
    eapply IHHsub2. eapply IHHsub1. exists n. exact Hn.
  - (* sort *)
    exists k. apply cjoin_refl.
  - (* Pi subtyping cannot reach a sort *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HPi).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
  - (* forgetting μˢ to Carrier *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HMuSApp).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
  - (* signature subtyping *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HMuSApp).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
Qed.

Lemma erased_sort_whd : forall T U h,
    erased_sort T -> conv T U -> whd U h -> h = HSort.
Proof.
  intros T U h [j Htj] Hconv [U' [HU HUshape]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Htu.
  pose proof (phi_erase_eval_csteps _ _ HU) as Hured.
  destruct (cjoin_reduce_right _ _ _ Htu Hured) as [w [Htw Huw]].
  (* The left endpoint also joins the erased source to the sort. *)
  destruct (cjoin_reduce_left _ _ _ Htj Htw) as [z [Hz1 Hz2]].
  pose proof (rtc_cstep_sort_id j z Hz2) as ->.
  assert (HS : hshape (TSort j) HSort) by constructor.
  assert (HUh : hshape (TSort j) h).
  { eapply rtc_cstep_hshape; [eapply rtc_trans; [exact Huw | exact Hz1] |].
    apply phi_erase_hshape_luna, HUshape. }
  pose proof (hshape_tag_unique (TSort j) _ _ HS HUh) as K.
  destruct h; simpl in K; try discriminate; reflexivity.
Qed.

Print Assumptions erased_sort_sub.
Print Assumptions erased_sort_whd.
