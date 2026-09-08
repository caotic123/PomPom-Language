Require Import Progress _luna_repair_empty_enum_sub
  _luna_repair_empty_enum_value _parent_repair_muapp
  _luna_repair_erased_sort_sub _luna_repair_erased_subst
  _luna_repair_app_origin _luna_repair_value_app_erased_sort.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import _work_cjoin _work_cstep_invariants.
Import Progress._luna_phi_erase_shapes.

Lemma luna_empty_enum_cons_nil : forall tg E,
    cjoin (TEnumT (TConsE tg E)) (TEnumT TNilE) -> False.
Proof.
  intros tg E [w [HL HR]].
  destruct (rtc_cstep_enumt_inv _ _ HL) as [L [EL HL']].
  destruct (rtc_cstep_enumt_inv _ _ HR) as [R [ER HR']].
  rewrite EL in ER. inversion ER; subst R.
  pose proof (rtc_cstep_hshape _ _ HL' HConsE (hs_conse _ _)) as HC2.
  pose proof (rtc_cstep_hshape _ _ HR' HNilE hs_nile) as HN2.
  pose proof (hshape_tag_unique _ _ _ HC2 HN2). discriminate.
Qed.

Lemma luna_check_app_erased_sort : forall f a T,
    check [] (TApp f a) T -> value (TApp f a) ->
    erased_sort T.
Proof.
  intros f a T HC HV.
  destruct (check_app_origin [] (TApp f a) T HC eq_refl f a eq_refl)
    as [X [HO HS]].
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

Lemma erased_empty_check_value_luna : forall G t T,
    check G t T -> G = [] -> value t -> erased_empty_enum T -> False.
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG Hv Hempty; subst.
  all: try solve [inversion Hv].
  all: try solve [eapply erased_enum_clash_luna;
    [exact Hempty | cbn [phi_erase]; constructor | discriminate]].
  all: try solve [eapply luna_empty_enum_cons_nil; exact Hempty].
  - eapply erased_empty_synth_value; [exact H | exact Hv |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact Hempty].
  - apply (erased_empty_synth_value _ _ H Hv).
    exact (erased_empty_enum_sub_back [] A B H0 Hempty).
  - apply (IHHcheck eq_refl Hv).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact Hempty].
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (luna_check_app_erased_sort f a (subst a 0 B) HCapp Hv)
      as [j Hj].
    assert (HJ : cjoin (TSort j) (TEnumT TNilE)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact Hempty]. }
    pose proof (luna_cjoin_hshape_tag _ _ _ _ HJ
      (hs_sort j) (hs_enumt TNilE)) as K.
    discriminate K.
Qed.

Print Assumptions erased_empty_check_value_luna.
