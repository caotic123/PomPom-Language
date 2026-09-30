(* ========================================================================== *)
(*  _glm_phi_erase_sort_pipeline.v — narrow stable-sort erasure pipeline.     *)
(*                                                                            *)
(*  Conditional pipeline built from THREE narrow theorem binders/Definitions  *)
(*  (Prop-valued Definitions used as premises — never axioms):                *)
(*                                                                            *)
(*    1. erase_pstep_reflect_glm        — full ONE-STEP pstep erasure         *)
(*       reflection.                                                          *)
(*    2. erase_epstep_sort_reflect_glm  — rtc epstep erasure reflection,      *)
(*       ONLY to a syntactic sort endpoint TSort j.  (The unrestricted        *)
(*       epstep reflection is refuted by _glm_phi_erase_epstep_counter-       *)
(*       example, so the endpoint restriction is essential.)                  *)
(*    3. cstep_sort_standardization_glm — standardization at sort endpoints:  *)
(*          rtc cstep x (TSort j) -> exists y,                                *)
(*            rtc pstep x y /\ rtc epstep y (TSort j).                        *)
(*                                                                            *)
(*  Stages (each a named lemma):                                              *)
(*    A. rtc lift of the one-step pstep reflection.                           *)
(*    B. stable_sort_erase_reflect_narrow_glm : the three binders ->          *)
(*          forall B j, rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j).*)
(*    C. Adaptation of _glm_phi_erase_reflect_close_codomain.v: ONLY the      *)
(*       sort-codomain transport (conv_pi_cod_sort_narrow_glm, its fixed      *)
(*       TPi IT (TSort 0) specialization, and the sub-level                   *)
(*       sub_pisort0_cod_sort_narrow_glm).  A full                            *)
(*       conv_pi_codomain_compatible_glm is deliberately NOT attempted:       *)
(*       stable-sort reflection cannot justify it — only sort-convertible     *)
(*       source codomains are transported.                                    *)
(*    D. Adaptation of _glm_phi_erase_reflect_close_muapp.v: the two ao_chk   *)
(*       closers and the final muapp_sort_narrow_glm, with cutoff-0           *)
(*       substitution transport via conv_subst0_glm, conditional on the       *)
(*       three narrow binders only.                                           *)
(*                                                                            *)
(*  No Axiom / Parameter / Conjecture / Admitted / admit / Abort.             *)
(* ========================================================================== *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep
  _work_conv_whd_pos _glm_muapp_sort_origin _glm_muapp_sort_close
  _glm_conv_subst0.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  0. The three narrow binders.                                              *)
(* ========================================================================== *)

(* Full one-step pstep erasure reflection. *)
Definition erase_pstep_reflect_glm : Prop :=
  forall t u, pstep (phi_erase t) u ->
    exists t', pstep t t' /\ phi_erase t' = u.

(* rtc epstep erasure reflection, only to a syntactic sort endpoint. *)
Definition erase_epstep_sort_reflect_glm : Prop :=
  forall t j, rtc epstep (phi_erase t) (TSort j) ->
    exists t', rtc epstep t t' /\ phi_erase t' = TSort j.

(* Standardization at sort endpoints: every cstep path into a sort
   standardizes to a pstep phase followed by an epstep phase into the sort. *)
Definition cstep_sort_standardization_glm : Prop :=
  forall x j, rtc cstep x (TSort j) ->
    exists y, rtc pstep x y /\ rtc epstep y (TSort j).

(* ========================================================================== *)
(*  A. rtc lift of the one-step pstep erasure reflection.                     *)
(* ========================================================================== *)

(* phi_erase preserves every head constructor except TMuS (erased to
   TMuS TUnit); hence a term erasing to a syntactic sort IS that sort. *)
Lemma phi_erase_sort_inv_narrow_glm : forall t j, phi_erase t = TSort j -> t = TSort j.
Proof.
  intros t j H. destruct t; simpl in H; try discriminate; congruence.
Qed.

Lemma rtc_pstep_erase_reflect_narrow_glm :
  erase_pstep_reflect_glm ->
  forall t u, rtc pstep (phi_erase t) u ->
  exists t', rtc pstep t t' /\ phi_erase t' = u.
Proof.
  intros Hp t u H.
  remember (phi_erase t) as s eqn:Hs. revert t Hs.
  induction H as [x | x y z Hxy Hrest IH]; intros t Hs.
  - (* rtc_refl : the preimage of the erased source is the source itself *)
    exists t. split.
    + apply rtc_refl.
    + symmetry. exact Hs.
  - (* rtc_step : lift the first step at the preimage, then induct *)
    assert (Hxy' : pstep (phi_erase t) y) by (rewrite <- Hs; exact Hxy).
    destruct (Hp t y Hxy') as [t1 [Ht1 He1]].
    destruct (IH t1 (eq_sym He1)) as [t2 [Ht2 He2]].
    exists t2. split.
    + eapply rtc_step; [exact Ht1 | exact Ht2].
    + exact He2.
Qed.

(* The two single-relations embed into rtc cstep. *)
Lemma rtc_pstep_incl_rtc_cstep_glm : forall t u,
    rtc pstep t u -> rtc cstep t u.
Proof.
  intros t u H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply pstep_cstep; exact H | exact IHrtc].
Qed.

Lemma rtc_epstep_incl_rtc_cstep_glm : forall t u,
    rtc epstep t u -> rtc cstep t u.
Proof.
  intros t u H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply epstep_cstep; exact H | exact IHrtc].
Qed.

(* ========================================================================== *)
(*  B. Stable sort reflection from the three narrow binders.                  *)
(* ========================================================================== *)

Theorem stable_sort_erase_reflect_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall B j, rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j).
Proof.
  intros Hp Hep Hstd B j H.
  (* standardize: pstep phase, then epstep phase into the sort *)
  destruct (Hstd _ _ H) as [y [Hy1 Hy2]].
  (* reflect the pstep phase through phi_erase *)
  destruct (rtc_pstep_erase_reflect_narrow_glm Hp _ _ Hy1) as [B1 [HB1 He1]].
  rewrite <- He1 in Hy2.
  (* reflect the epstep phase (sort-restricted binder) *)
  destruct (Hep B1 j Hy2) as [B2 [HB2 He2]].
  assert (He2' : B2 = TSort j) by (eapply phi_erase_sort_inv_narrow_glm; exact He2).
  rewrite He2' in HB2.
  (* re-enter conv through rtc cstep *)
  apply rtc_cstep_conv.
  eapply rtc_trans;
    [ apply rtc_pstep_incl_rtc_cstep_glm; exact HB1
    | apply rtc_epstep_incl_rtc_cstep_glm; exact HB2 ].
Qed.

(* ========================================================================== *)
(*  C. Sort-codomain transport and sub_pisort0 codomain-to-sort.              *)
(* ========================================================================== *)

(* cjoin against a stable sort endpoint re-enters conv via the narrow
   stable reflection. *)
Lemma cjoin_erase_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall B j, cjoin (TSort j) (phi_erase B) -> conv B (TSort j).
Proof.
  intros Hp Hep Hstd B j [w [Hw1 Hw2]].
  assert (Hw : w = TSort j) by (eapply rtc_cstep_sort_id; exact Hw1).
  subst w.
  eapply stable_sort_erase_reflect_narrow_glm; eassumption.
Qed.

(* Sort-codomain transport: if the source codomain is sort-convertible,
   so is the target codomain of any convertible Pi.  This is ONLY the
   sort-convertible-source case — not a full Pi-codomain compatibility. *)
Lemma conv_pi_cod_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall A0 B0 A1 B1 j,
    conv B0 (TSort j) ->
    conv (TPi A0 B0) (TPi A1 B1) ->
    conv B1 (TSort j).
Proof.
  intros Hp Hep Hstd A0 B0 A1 B1 j Hj Hc.
  pose proof (conv_phi_cjoin _ _ Hc) as Hcj.
  cbn [phi_erase] in Hcj.
  destruct (cjoin_pi_inv _ _ _ _ Hcj) as [_ Hd2].
  pose proof (conv_phi_cjoin _ _ Hj) as Hj2.
  cbn [phi_erase] in Hj2.
  assert (Hchain : cjoin (TSort j) (phi_erase B1)).
  { eapply cjoin_trans.
    - apply cjoin_sym; exact Hj2.
    - exact Hd2. }
  eapply cjoin_erase_sort_narrow_glm; eassumption.
Qed.

(* The fixed-source specialization required downstream. *)
Theorem conv_pisort0_codomain_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall IT A B,
    conv (TPi IT (TSort 0)) (TPi A B) -> conv B (TSort 0).
Proof.
  intros Hp Hep Hstd IT A B Hc.
  eapply conv_pi_cod_sort_narrow_glm;
    [exact Hp | exact Hep | exact Hstd | apply cv_refl | exact Hc].
Qed.

(* Introduction of the conv-side invariant at a syntactic Pi whose codomain
   is sort-convertible — the narrow replacement of pi_cod_sort_inv_intro. *)
Lemma pi_cod_sort_inv_intro_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall A0 B0 j, conv B0 (TSort j) -> pi_cod_sort_inv_glm (TPi A0 B0).
Proof.
  intros Hp Hep Hstd A0 B0 j Hj A B Hc.
  exists j.
  eapply conv_pi_cod_sort_narrow_glm; eassumption.
Qed.

(* The invariant is preserved by every sub rule; only the su_pi rebuild
   consumes an interface, discharged by the narrow binders. *)
Lemma sub_pi_cod_sort_inv_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall G X Y, sub G X Y -> pi_cod_sort_inv_glm X -> pi_cod_sort_inv_glm Y.
Proof.
  intros Hp Hep Hstd G X Y Hsub.
  induction Hsub; intros Hinv.
  - (* su_conv: conv X Y, so a Pi convertible to Y is convertible to X *)
    intros P Q Hc. exact (Hinv P Q (cv_trans H Hc)).
  - (* su_trans: chain the invariant through the middle *)
    exact (IHHsub2 (IHHsub1 Hinv)).
  - (* su_sort: the target is a sort; conv sort-vs-Pi is impossible *)
    intros P Q Hc. exfalso. eapply glm_conv_sort_pi_l_glm; exact Hc.
  - (* su_pi: rebuild from the rule's sub-promise on the codomain *)
    destruct (pi_cod_sort_inv_pi_elim_glm _ _ Hinv) as [j Hj].
    destruct (glm_sub_sort_source_conv_glm _ B B' Hsub2 j Hj) as [j' Hj'].
    eapply pi_cod_sort_inv_intro_narrow_glm;
      [exact Hp | exact Hep | exact Hstd | exact Hj'].
  - (* su_forget: the target is a stuck Carrier application *)
    intros P Q Hc. exfalso. eapply glm_conv_carrierapp_pi_glm; exact Hc.
  - (* su_sig: the target is a stuck mu-S application *)
    intros P Q Hc. exfalso. eapply glm_conv_musapp_pi_glm; exact Hc.
Qed.

(* Sub-level extraction at the fixed source TPi IT (TSort 0). *)
Theorem sub_pisort0_cod_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall G IT A B, sub G (TPi IT (TSort 0)) (TPi A B) ->
  exists j, conv B (TSort j).
Proof.
  intros Hp Hep Hstd G IT A B Hsub.
  eapply pi_cod_sort_inv_pi_elim_glm.
  eapply sub_pi_cod_sort_inv_narrow_glm;
    [exact Hp | exact Hep | exact Hstd | exact Hsub |].
  eapply pi_cod_sort_inv_intro_narrow_glm;
    [exact Hp | exact Hep | exact Hstd | apply cv_refl].
Qed.

(* ========================================================================== *)
(*  D. ao_chk closers and the final muapp_sort theorem.                       *)
(* ========================================================================== *)

(* Cutoff-0 substitution transports sort-convertibility of a codomain
   (closed, via conv_subst0_glm). *)
Lemma subst0_sort_target_narrow_glm : forall a B j,
    conv B (TSort j) -> conv (subst a 0 B) (TSort j).
Proof.
  intros a B j Hj.
  pose proof (conv_subst0_glm B (TSort j) a a Hj (cv_refl a)) as H.
  cbn [subst] in H. exact H.
Qed.

(* ao_chk closer for the value mu-I former. *)
Lemma ao_chk_mui_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall R a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hp Hep Hstd R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - (* conv case: exact extraction at the fixed source, then substitute *)
      exists 0. eapply subst0_sort_target_narrow_glm.
      eapply conv_pisort0_codomain_narrow_glm; eassumption.
    - (* sub case: the narrow sub-level extraction, then substitute *)
      destruct (sub_pisort0_cod_sort_narrow_glm Hp Hep Hstd [] IT A B Hrel)
        as [j Hj].
      exists j. eapply subst0_sort_target_narrow_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* ao_chk closer for the value mu-S former. *)
Lemma ao_chk_mus_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall Sf a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hp Hep Hstd Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. eapply subst0_sort_target_narrow_glm.
      eapply conv_pisort0_codomain_narrow_glm; eassumption.
    - destruct (sub_pisort0_cod_sort_narrow_glm Hp Hep Hstd [] IT A B Hrel)
        as [j Hj].
      exists j. eapply subst0_sort_target_narrow_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* The full typing theorem, conditional only on the three narrow binders. *)
Theorem muapp_sort_narrow_glm :
  erase_pstep_reflect_glm -> erase_epstep_sort_reflect_glm ->
  cstep_sort_standardization_glm ->
  forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros Hp Hep Hstd f a T U h Hchk Hv Hc Hw.
  destruct (check_app_origin [] (TApp f a) T Hchk eq_refl f a eq_refl)
    as [X [Hor Hsub]].
  destruct (app_origin_sort_split_glm f a X T U h Hor Hv Hsub Hc Hw)
    as [Hdone | [A [B [k [HX [Hk [Hf Ha]]]]]]].
  - (* ao_syn: the value application synthesizes Set_0 *)
    exact Hdone.
  - (* ao_chk: the value application's head is a mu-former *)
    subst X.
    destruct (value_app_mu_inv_glm _ _ Hv) as [[R Hf'] | [Sf Hf']].
    + rewrite Hf' in Hf.
      eapply ao_chk_mui_sort_narrow_glm; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_narrow_glm; eassumption.
Qed.

Print Assumptions stable_sort_erase_reflect_narrow_glm.
Print Assumptions conv_pi_cod_sort_narrow_glm.
Print Assumptions conv_pisort0_codomain_narrow_glm.
Print Assumptions sub_pisort0_cod_sort_narrow_glm.
Print Assumptions ao_chk_mui_sort_narrow_glm.
Print Assumptions ao_chk_mus_sort_narrow_glm.
Print Assumptions muapp_sort_narrow_glm.
