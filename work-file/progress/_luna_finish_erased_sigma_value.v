Require Import Progress.
Require Import SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma sigma_cjoin_hshape_tag_luna : forall t u h1 h2,
    cjoin t u -> hshape t h1 -> hshape u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 [w [Ht Hu]] Htshape Hushape.
  pose proof (rtc_cstep_hshape _ _ Ht h1 Htshape) as Hw1.
  pose proof (rtc_cstep_hshape _ _ Hu h2 Hushape) as Hw2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma sigma_phi_erase_sort_luna : forall k, hshape (phi_erase (TSort k)) HSort.
Proof. intros; cbn; constructor. Qed.

Lemma sigma_phi_erase_pi_luna : forall A B,
    hshape (phi_erase (TPi A B)) HPi.
Proof. intros; cbn; constructor. Qed.

Lemma sigma_phi_erase_carrier_luna : forall E Sf i,
    hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp.
Proof. intros; cbn [phi_erase Carrier]; constructor. Qed.

Lemma sigma_phi_erase_musapp_luna : forall Sf i,
    hshape (phi_erase (TApp (TMuS Sf) i)) HMuSApp.
Proof. intros; cbn [phi_erase]; constructor. Qed.

Lemma erased_sigma_sub_back : forall G X Y,
    sub G X Y -> forall A B,
    cjoin (phi_erase Y) (TSigma A B) ->
    cjoin (phi_erase X) (TSigma A B).
Proof.
  intros G X Y Hsub. induction Hsub; intros A0 B0 Hjoin.
  - eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact Hjoin].
  - exact (IHHsub1 A0 B0 (IHHsub2 A0 B0 Hjoin)).
  - exfalso. assert (Heq : HSort = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_sort_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HPi = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_pi_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HMuIApp = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_carrier_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HMuSApp = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_musapp_luna.
      - constructor. }
    discriminate Heq.
Qed.

Print Assumptions erased_sigma_sub_back.

Lemma clash_sigma_luna : forall T A B h,
    cjoin (phi_erase T) (TSigma A B) ->
    hshape (phi_erase T) h -> h <> HSigma -> False.
Proof.
  intros T A B h HJ HH Hneq.
  pose proof (sigma_cjoin_hshape_tag_luna _ _ _ _ HJ HH
    (hs_sigma A B)) as E.
  exact (Hneq E).
Qed.

Lemma erased_sigma_synth_value_absurd : forall t T,
    synth [] t T -> value t -> forall A B,
    cjoin (phi_erase T) (TSigma A B) -> False.
Proof.
  intros t T Hsyn HV A B HJ.
  inversion Hsyn; subst; try solve [inversion HV].
  all: try solve [
    eapply clash_sigma_luna; [exact HJ | cbn [phi_erase]; constructor | discriminate] ].
  pose proof (value_app_synth_sort _ _ _ HV Hsyn) as Hsort.
  rewrite Hsort in HJ.
  eapply clash_sigma_luna; [exact HJ | apply sigma_phi_erase_sort_luna | discriminate].
Qed.

Print Assumptions erased_sigma_synth_value_absurd.

Lemma erased_sigma_check_value_pair : forall G t T,
    check G t T -> G = [] -> value t -> forall A B,
    cjoin (phi_erase T) (TSigma A B) -> exists a b, t = TPair a b.
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG HV A0 B0 HJ; subst.
  all: try solve [inversion HV].
  all: try solve [exfalso; eapply clash_sigma_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  - exfalso. eapply erased_sigma_synth_value_absurd; [exact H | exact HV |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact HJ].
  - exfalso. eapply erased_sigma_synth_value_absurd; [exact H | exact HV |].
    eapply erased_sigma_sub_back; [exact H0 | exact HJ].
  - apply (IHHcheck eq_refl HV A0 B0).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact HJ].
  - eexists; eexists; reflexivity.
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (SignatureLemmas.luna_check_app_erased_sort
      f a (subst a 0 B) HCapp HV) as [j Hj].
    assert (HJ' : cjoin (TSort j) (TSigma A0 B0)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact HJ]. }
    exfalso. eapply (clash_sigma_luna (TSort j) A0 B0 HSort);
      [exact HJ' | apply hs_sort | discriminate].
Qed.

Print Assumptions erased_sigma_check_value_pair.
