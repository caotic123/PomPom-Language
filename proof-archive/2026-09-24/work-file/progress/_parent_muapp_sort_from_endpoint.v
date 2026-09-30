(* The final mu-application progress consumer, requiring only the precise
   endpoint-directed Pi/sort representation transport interface. *)

Require Import Progress _work_conv_whd_pos _glm_muapp_sort_origin
  _glm_muapp_sort_close _glm_muapp_sort_from_pi
  _parent_pi_sort_rep_consumer.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pi_cod_sort_inv_intro_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall A0 B0 j,
      conv B0 (TSort j) -> pi_cod_sort_inv_glm (TPi A0 B0).
Proof.
  intros SIM A0 B0 j HB A B Hpi.
  exists j.
  apply (conv_pi_sort_codomain_from_endpoint_parent SIM A0 A B j).
  eapply cv_trans.
  - apply cv_pi.
    + apply cv_refl.
    + apply cv_sym. exact HB.
  - exact Hpi.
Qed.

Lemma sub_pi_cod_sort_inv_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall G X Y,
      sub G X Y -> pi_cod_sort_inv_glm X -> pi_cod_sort_inv_glm Y.
Proof.
  intros SIM G X Y Hsub.
  induction Hsub; intros Hinv.
  - intros P Q Hc. exact (Hinv P Q (cv_trans H Hc)).
  - exact (IHHsub2 (IHHsub1 Hinv)).
  - intros P Q Hc. exfalso. eapply glm_conv_sort_pi_l_glm; exact Hc.
  - destruct (pi_cod_sort_inv_pi_elim_glm _ _ Hinv) as [j Hj].
    destruct (glm_sub_sort_source_conv_glm _ B B' Hsub2 j Hj)
      as [j' Hj'].
    eapply pi_cod_sort_inv_intro_endpoint_parent; eassumption.
  - intros P Q Hc. exfalso. eapply glm_conv_carrierapp_pi_glm; exact Hc.
  - intros P Q Hc. exfalso. eapply glm_conv_musapp_pi_glm; exact Hc.
Qed.

Lemma sub_pisort0_cod_sort_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall G IT A B,
      sub G (TPi IT (TSort 0)) (TPi A B) ->
      exists j, conv B (TSort j).
Proof.
  intros SIM G IT A B Hsub.
  eapply pi_cod_sort_inv_pi_elim_glm.
  eapply sub_pi_cod_sort_inv_endpoint_parent;
    [exact SIM | exact Hsub |].
  eapply pi_cod_sort_inv_intro_endpoint_parent;
    [exact SIM | apply cv_refl].
Qed.

Lemma ao_chk_mui_sort_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall R a A B k T U h,
      check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
      check [] a A -> sub [] (subst a 0 B) T ->
      conv T U -> whd U h -> h = HSort.
Proof.
  intros SIM R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. apply subst0_sort_target_glm.
      exact (conv_pi_sort_codomain_from_endpoint_parent
        SIM IT A B 0 Hrel).
    - destruct (sub_pisort0_cod_sort_endpoint_parent
        SIM [] IT A B Hrel) as [j Hj].
      exists j. apply subst0_sort_target_glm. exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Lemma ao_chk_mus_sort_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall Sf a A B k T U h,
      check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
      check [] a A -> sub [] (subst a 0 B) T ->
      conv T U -> whd U h -> h = HSort.
Proof.
  intros SIM Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. apply subst0_sort_target_glm.
      exact (conv_pi_sort_codomain_from_endpoint_parent
        SIM IT A B 0 Hrel).
    - destruct (sub_pisort0_cod_sort_endpoint_parent
        SIM [] IT A B Hrel) as [j Hj].
      exists j. apply subst0_sort_target_glm. exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Theorem muapp_sort_from_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall f a T U h,
      check [] (TApp f a) T -> value (TApp f a) ->
      conv T U -> whd U h -> h = HSort.
Proof.
  intros SIM f a T U h Hchk Hv Hc Hw.
  destruct (check_app_origin [] (TApp f a) T Hchk eq_refl f a eq_refl)
    as [X [Hor Hsub]].
  destruct (app_origin_sort_split_glm f a X T U h Hor Hv Hsub Hc Hw)
    as [Hdone | [A [B [k [HX [Hk [Hf Ha]]]]]]].
  - exact Hdone.
  - subst X.
    destruct (value_app_mu_inv_glm _ _ Hv) as [[R Hf'] | [Sf Hf']].
    + rewrite Hf' in Hf.
      eapply ao_chk_mui_sort_endpoint_parent; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_endpoint_parent; eassumption.
Qed.

Print Assumptions pi_cod_sort_inv_intro_endpoint_parent.
Print Assumptions sub_pi_cod_sort_inv_endpoint_parent.
Print Assumptions sub_pisort0_cod_sort_endpoint_parent.
Print Assumptions ao_chk_mui_sort_endpoint_parent.
Print Assumptions ao_chk_mus_sort_endpoint_parent.
Print Assumptions muapp_sort_from_endpoint_parent.
