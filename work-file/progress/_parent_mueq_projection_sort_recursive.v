(* Projection root cases for the well-founded mueq sort-transport proof. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _work_cstep_invariants _luna_mueq _glm_mueq_pstep_conditional_inv
  _parent_mueq_eta_sort_recursive.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma mueq_fst_inv_parent : forall p u,
    mueq (TFst p) u -> exists p', u = TFst p' /\ mueq p p'.
Proof.
  intros p u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma mueq_snd_inv_parent : forall p u,
    mueq (TSnd p) u -> exists p', u = TSnd p' /\ mueq p p'.
Proof.
  intros p u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma fst_contractum_reaches_sort_parent : forall a b j,
    rtc cstep (TFst (TPair a b)) (TSort j) ->
    rtc cstep a (TSort j).
Proof.
  intros a b j Hsort.
  assert (Hroot : rtc cstep (TFst (TPair a b)) a).
  { apply rtc_one, pstep_cstep.
    exact (ps_fst_pair a a b b (pstep_refl a) (pstep_refl b)). }
  destruct (cstep_confluent _ _ _ Hroot Hsort) as [w [Haw Hsw]].
  rewrite (rtc_cstep_sort_id _ _ Hsw) in Haw. exact Haw.
Qed.

Lemma snd_contractum_reaches_sort_parent : forall a b j,
    rtc cstep (TSnd (TPair a b)) (TSort j) ->
    rtc cstep b (TSort j).
Proof.
  intros a b j Hsort.
  assert (Hroot : rtc cstep (TSnd (TPair a b)) b).
  { apply rtc_one, pstep_cstep.
    exact (ps_snd_pair a a b b (pstep_refl a) (pstep_refl b)). }
  destruct (cstep_confluent _ _ _ Hroot Hsort) as [w [Hbw Hsw]].
  rewrite (rtc_cstep_sort_id _ _ Hsw) in Hbw. exact Hbw.
Qed.

Theorem mueq_fst_pair_sort_recursive_parent : forall a b u j,
    mueq_sort_transport_below_parent (tsize (TFst (TPair a b))) ->
    mueq (TFst (TPair a b)) u ->
    rtc cstep (TFst (TPair a b)) (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros a b u j IH Hm Hsort.
  destruct (mueq_fst_inv_parent _ _ Hm) as [p' [-> Hp]].
  destruct (mueq_pair_inv_glm _ _ _ Hp) as [a' [b' [-> [Ha Hb]]]].
  pose proof (fst_contractum_reaches_sort_parent a b j Hsort) as Hasort.
  assert (Hsmall : tsize a < tsize (TFst (TPair a b))).
  { pose proof (tsize_pos b). cbn [tsize]. lia. }
  pose proof (IH a a' j Hsmall Ha Hasort) as Ha'sort.
  eapply rtc_step.
  - apply pstep_cstep.
    exact (ps_fst_pair a' a' b' b' (pstep_refl a') (pstep_refl b')).
  - exact Ha'sort.
Qed.

Theorem mueq_snd_pair_sort_recursive_parent : forall a b u j,
    mueq_sort_transport_below_parent (tsize (TSnd (TPair a b))) ->
    mueq (TSnd (TPair a b)) u ->
    rtc cstep (TSnd (TPair a b)) (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros a b u j IH Hm Hsort.
  destruct (mueq_snd_inv_parent _ _ Hm) as [p' [-> Hp]].
  destruct (mueq_pair_inv_glm _ _ _ Hp) as [a' [b' [-> [Ha Hb]]]].
  pose proof (snd_contractum_reaches_sort_parent a b j Hsort) as Hbsort.
  assert (Hsmall : tsize b < tsize (TSnd (TPair a b))).
  { pose proof (tsize_pos a). cbn [tsize]. lia. }
  pose proof (IH b b' j Hsmall Hb Hbsort) as Hb'sort.
  eapply rtc_step.
  - apply pstep_cstep.
    exact (ps_snd_pair a' a' b' b' (pstep_refl a') (pstep_refl b')).
  - exact Hb'sort.
Qed.

Print Assumptions mueq_fst_pair_sort_recursive_parent.
Print Assumptions mueq_snd_pair_sort_recursive_parent.
