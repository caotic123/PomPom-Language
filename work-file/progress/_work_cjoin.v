Require Import Progress _tmp_epstep _work_mixed_closure
  _luna_fstep_split.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Definition cjoin (t u : term) : Prop :=
  exists w, rtc cstep t w /\ rtc cstep u w.

Lemma cjoin_refl : forall t, cjoin t t.
Proof. intros t. exists t. split; apply rtc_refl. Qed.

Lemma cjoin_sym : forall t u, cjoin t u -> cjoin u t.
Proof. intros t u [w [Htw Huw]]. exists w. auto. Qed.

Lemma cjoin_trans : forall t u v,
    cjoin t u -> cjoin u v -> cjoin t v.
Proof.
  intros t u v [q [Htq Huq]] [r [Hur Hvr]].
  destruct (cstep_confluent u q r Huq Hur) as [w [Hqw Hrw]].
  exists w. split; eapply rtc_trans; eassumption.
Qed.

Lemma cjoin_reduce_left : forall t u t',
    cjoin t u -> rtc cstep t t' -> cjoin t' u.
Proof.
  intros t u t' [q [Htq Huq]] Htt'.
  destruct (cstep_confluent t q t' Htq Htt') as [w [Hqw Ht'w]].
  exists w. split; [exact Ht'w |].
  eapply rtc_trans; eassumption.
Qed.

Lemma cjoin_reduce_right : forall t u u',
    cjoin t u -> rtc cstep u u' -> cjoin t u'.
Proof.
  intros t u u' Hjoin Huu'. apply cjoin_sym.
  eapply cjoin_reduce_left; [apply cjoin_sym; exact Hjoin | exact Huu'].
Qed.

Lemma fstep_cstep : forall t u, fstep t u -> cstep t u.
Proof.
  intros t u H.
  destruct (fstep_pstep_or_epstep _ _ H) as [Hp | He].
  - apply pstep_cstep, Hp.
  - apply epstep_cstep, He.
Qed.

Lemma fconv_cjoin : forall t u, fconv t u -> cjoin t u.
Proof.
  intros t u H. induction H.
  - exists u. split; [apply rtc_one, fstep_cstep, H | apply rtc_refl].
  - apply cjoin_refl.
  - apply cjoin_sym, IHfconv.
  - eapply cjoin_trans; eassumption.
Qed.

Lemma conv_phi_cjoin : forall t u, conv t u ->
    cjoin (phi_erase t) (phi_erase u).
Proof.
  intros t u H. apply fconv_cjoin, phi_erase_conv, H.
Qed.

