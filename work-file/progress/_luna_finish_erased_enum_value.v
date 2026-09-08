Require Import Progress.
Require Import SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma enum_cjoin_tag_luna : forall t u h k,
    cjoin t u -> hshape t h -> hshape u k -> h = k.
Proof.
  intros t u h k [w [Ht Hu]] HH HK.
  pose proof (rtc_cstep_hshape _ _ Ht h HH) as H1.
  pose proof (rtc_cstep_hshape _ _ Hu k HK) as H2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma enum_cjoin_inv_luna : forall E1 E2,
    cjoin (TEnumT E1) (TEnumT E2) -> cjoin E1 E2.
Proof.
  intros E1 E2 [w [H1 H2]].
  destruct (rtc_cstep_enumt_inv _ _ H1) as [W1 [HW1 HE1]].
  destruct (rtc_cstep_enumt_inv _ _ H2) as [W2 [HW2 HE2]].
  rewrite HW1 in HW2. inversion HW2; subst W2.
  exists W1. split; assumption.
Qed.

Lemma enum_cjoin_sub_back_luna : forall G X Y,
    sub G X Y -> forall E,
    cjoin (phi_erase Y) (TEnumT E) ->
    cjoin (phi_erase X) (TEnumT E).
Proof.
  intros G X Y Hsub. induction Hsub; intros E0 HJ.
  - eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact HJ].
  - exact (IHHsub1 E0 (IHHsub2 E0 HJ)).
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_sort _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_pi _ _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_muiapp _ _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_musapp _ _) (hs_enumt _)) as K; discriminate K.
Qed.

Print Assumptions enum_cjoin_inv_luna.
Print Assumptions enum_cjoin_sub_back_luna.

Lemma clash_enum_luna : forall T E h,
    cjoin (phi_erase T) (TEnumT E) ->
    hshape (phi_erase T) h -> h <> HEnumT -> False.
Proof.
  intros T E h HJ HH Hneq.
  pose proof (enum_cjoin_tag_luna _ _ _ _ HJ HH (hs_enumt E)) as K.
  exact (Hneq K).
Qed.

Lemma enum_cjoin_synth_value_absurd_luna : forall t T,
    synth [] t T -> value t -> forall E,
    cjoin (phi_erase T) (TEnumT E) -> False.
Proof.
  intros t T Hsyn HV E HJ.
  inversion Hsyn; subst; try solve [inversion HV].
  all: try solve [eapply clash_enum_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  pose proof (value_app_synth_sort _ _ _ HV Hsyn) as Hsort.
  rewrite Hsort in HJ.
  eapply clash_enum_luna; [exact HJ | apply hs_sort | discriminate].
Qed.

Print Assumptions enum_cjoin_synth_value_absurd_luna.

Lemma erased_enum_check_value_origin_luna : forall G t T,
    check G t T -> G = [] -> value t -> forall E,
    cjoin (phi_erase T) (TEnumT E) ->
    (exists tg E0, t = TEZero /\
       cjoin (TConsE (phi_erase tg) (phi_erase E0)) E) \/
    (exists n tg E0, t = TESucc n /\ check [] n (TEnumT E0) /\
       cjoin (TConsE (phi_erase tg) (phi_erase E0)) E).
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG HV E0 HJ; subst.
  all: try solve [inversion HV].
  all: try solve [exfalso; eapply clash_enum_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  - exfalso. eapply enum_cjoin_synth_value_absurd_luna;
      [exact H | exact HV |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact HJ].
  - exfalso. eapply enum_cjoin_synth_value_absurd_luna;
      [exact H | exact HV |].
    eapply enum_cjoin_sub_back_luna; [exact H0 | exact HJ].
  - apply (IHHcheck eq_refl HV E0).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact HJ].
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (SignatureLemmas.luna_check_app_erased_sort
      f a (subst a 0 B) HCapp HV) as [j Hj].
    assert (HJ' : cjoin (TSort j) (TEnumT E0)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact HJ]. }
    exfalso. eapply (clash_enum_luna (TSort j) E0 HSort);
      [exact HJ' | apply hs_sort | discriminate].
  - left. eexists; eexists; split; [reflexivity |].
    cbn [phi_erase] in HJ. eapply enum_cjoin_inv_luna; exact HJ.
  - right. exists n, tg, E. repeat split; try reflexivity; try exact Hcheck2.
    cbn [phi_erase] in HJ. eapply enum_cjoin_inv_luna; exact HJ.
Qed.

Print Assumptions erased_enum_check_value_origin_luna.
