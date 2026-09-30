Require Import Progress _luna_repair_erased_sort_sub
  _luna_repair_erased_subst _luna_repair_app_origin.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep
  Progress._work_mixed_closure Progress._work_cjoin
  Progress._work_cstep_invariants Progress._luna_phi_erase_shapes.

Lemma cjoin_hshape_tags_parent : forall t u h k,
  cjoin t u -> hshape t h -> hshape u k -> h = k.
Proof.
  intros t u h k [w [Ht Hu]] HH HK.
  eapply hshape_tag_unique with (T:=w).
  - eapply rtc_cstep_hshape; [exact Ht | exact HH].
  - eapply rtc_cstep_hshape; [exact Hu | exact HK].
Qed.

Definition erased_pi_sort (T : term) : Prop :=
  forall A B, cjoin (phi_erase T) (TPi A B) ->
    exists j, cjoin B (TSort j).

Lemma erased_pi_sort_intro : forall A B,
  erased_sort B -> erased_pi_sort (TPi A B).
Proof.
  intros A B [j Hj] A' B' Hpi.
  cbn [phi_erase] in Hpi.
  destruct (cjoin_pi_inv _ _ _ _ Hpi) as [_ HB].
  exists j. eapply cjoin_trans; [apply cjoin_sym; exact HB | exact Hj].
Qed.

Lemma erased_pi_sort_sub : forall G T U,
  sub G T U -> erased_pi_sort T -> erased_pi_sort U.
Proof.
  intros G T U H. induction H; intros HT.
  - intros P Q Hpi. apply (HT P Q).
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact Hpi].
  - apply IHsub2, IHsub1, HT.
  - intros P Q Hj. exfalso.
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj (hs_sort k) (hs_pi P Q)).
    discriminate.
  - apply erased_pi_sort_intro.
    apply (erased_sort_sub _ _ _ H0).
    apply (HT (phi_erase A) (phi_erase B)). apply cjoin_refl.
  - intros P Q Hj. exfalso.
    assert (HH : hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp).
    { cbn [Carrier phi_erase]. constructor. }
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj HH (hs_pi P Q)).
    discriminate.
  - intros P Q Hj. exfalso.
    assert (HH : hshape (phi_erase (TApp (TMuS S2) i)) HMuSApp).
    { cbn [phi_erase]. constructor. }
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj HH (hs_pi P Q)).
    discriminate.
Qed.

Lemma sub_mu_pi_erased_codomain_sort : forall G IT A B,
  sub G (TPi IT (TSort 0)) (TPi A B) -> erased_sort B.
Proof.
  intros G IT A B HS.
  assert (HI : erased_pi_sort (TPi IT (TSort 0))).
  { apply erased_pi_sort_intro. exists 0. apply cjoin_refl. }
  exact (erased_pi_sort_sub _ _ _ HS HI
    (phi_erase A) (phi_erase B) (cjoin_refl _)).
Qed.

Theorem muapp_sort_erased_proved : forall f a T U h,
  check [] (TApp f a) T -> value (TApp f a) ->
  conv T U -> whd U h -> h = HSort.
Proof.
  intros f a T U h HC HV Hconv HW.
  destruct (check_app_origin _ _ _ HC eq_refl f a eq_refl)
    as [X [HO HS]].
  apply (erased_sort_whd T U h); [|exact Hconv|exact HW].
  apply (erased_sort_sub _ _ _ HS).
  destruct HO as [C HSYN | A B k Hformation HF HA].
  - pose proof (value_app_synth_sort f a C HV HSYN) as ->.
    exists 0. apply cjoin_refl.
  - assert (HFshape : (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf)).
    { inversion HV; subst; eauto. }
    destruct (mu_former_checked_erased_pi_origin_luna [] f A B HFshape HF)
      as [IT HPI].
    destruct (sub_mu_pi_erased_codomain_sort _ _ _ _ HPI) as [j Hj].
    exists j. apply erased_sort_cjoin_subst_luna, Hj.
Qed.

Print Assumptions muapp_sort_erased_proved.
