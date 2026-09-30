(* GLM worker 1 — cjoin-subst bundle, part 3: cstep and rtc cstep
   substitution under the SAME arbitrary substituent. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _glm_cjoin_subst_pstep _glm_cjoin_subst_epstep.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.

Lemma rtc_map_cstep_glm : forall (F : term -> term),
    (forall x y, cstep x y -> cstep (F x) (F y)) ->
    forall x y, rtc cstep x y -> rtc cstep (F x) (F y).
Proof.
  intros F HF x y H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact H | exact IHrtc].
Qed.

Lemma rtc_pstep_subst_same_glm : forall t v, rtc pstep t v -> forall u k,
    rtc pstep (subst u k t) (subst u k v).
Proof.
  intros t v H u k. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply pstep_subst_same_glm; exact H | exact IHrtc].
Qed.

Lemma rtc_epstep_subst_same_glm : forall t v, rtc epstep t v -> forall u k,
    rtc epstep (subst u k t) (subst u k v).
Proof.
  intros t v H u k. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply epstep_subst_same_glm; exact H | exact IHrtc].
Qed.

Lemma cstep_subst_same_glm : forall t v, cstep t v -> forall u k,
    cstep (subst u k t) (subst u k v).
Proof.
  intros t v H u k. destruct H as [t v Hp | t v He].
  - apply cs_core. apply rtc_pstep_subst_same_glm. exact Hp.
  - apply cs_eta. apply rtc_epstep_subst_same_glm. exact He.
Qed.

Lemma rtc_cstep_subst_same_glm : forall t v, rtc cstep t v -> forall u k,
    rtc cstep (subst u k t) (subst u k v).
Proof.
  intros t v H u k. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply cstep_subst_same_glm; exact H | exact IHrtc].
Qed.

Print Assumptions cstep_subst_same_glm.
Print Assumptions rtc_cstep_subst_same_glm.
