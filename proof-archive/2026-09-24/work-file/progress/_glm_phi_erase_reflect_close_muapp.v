(* ========================================================================== *)
(*  _glm_phi_erase_reflect_close_muapp.v — GLM worker 2: muapp_sort derived   *)
(*  from the erasure-reflection closing layer.                                *)
(*                                                                            *)
(*  Adapts the architecture of _glm_muapp_sort_from_pi.v to the NARROWER      *)
(*  fixed-source Pi property delivered by the closing layer:                  *)
(*                                                                            *)
(*    conv_pisort_codomain_from_erase_reflect_glm :                           *)
(*      erase_pstep_reflect -> erase_epstep_reflect -> forall IT A B,         *)
(*        conv (TPi IT (TSort 0)) (TPi A B) -> conv B (TSort 0).              *)
(*                                                                            *)
(*  The two consumers of Pi-codomain injectivity inside the muapp_sort        *)
(*  branches are each replaced by an erasure-reflection counterpart:          *)
(*    - conv branch:  pisort0_conv_cod_glm      ->  theorem 4 directly.       *)
(*    - sub branch:   sub_pisort0_cod_sort_glm  ->  sub_pisort0_cod_sort_     *)
(*                                                  erase_glm (close layer).  *)
(*  The cutoff-0 substitution transport reuses conv_subst0_glm (closed).      *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort; all premises are        *)
(*  theorem binders; Print Assumptions reports Closed under the global        *)
(*  context for every final theorem.                                          *)
(* ========================================================================== *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep
  _work_conv_whd_pos _glm_muapp_sort_origin _glm_muapp_sort_close
  _glm_conv_subst0
  _glm_phi_erase_reflect_close_reflect _glm_phi_erase_reflect_close_codomain.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  (1) Cutoff-0 substitution transports sort-convertibility of a codomain.   *)
(* ========================================================================== *)

Lemma subst0_sort_target_erase_glm : forall a B j,
    conv B (TSort j) -> conv (subst a 0 B) (TSort j).
Proof.
  intros a B j Hj.
  pose proof (conv_subst0_glm B (TSort j) a a Hj (cv_refl a)) as H.
  cbn [subst] in H. exact H.
Qed.

(* ========================================================================== *)
(*  (2) Replacement ao_chk branch closers for the two value mu-formers.       *)
(* ========================================================================== *)

Lemma ao_chk_mui_sort_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall R a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hp He R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - (* conv case: exact extraction at the fixed source, then substitute *)
      exists 0. eapply subst0_sort_target_erase_glm.
      eapply conv_pisort_codomain_from_erase_reflect_glm; eassumption.
    - (* sub case: the erasure-reflection extraction, then substitute *)
      destruct (sub_pisort0_cod_sort_erase_glm Hp He [] IT A B Hrel)
        as [j Hj].
      exists j. eapply subst0_sort_target_erase_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Lemma ao_chk_mus_sort_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall Sf a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hp He Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. eapply subst0_sort_target_erase_glm.
      eapply conv_pisort_codomain_from_erase_reflect_glm; eassumption.
    - destruct (sub_pisort0_cod_sort_erase_glm Hp He [] IT A B Hrel)
        as [j Hj].
      exists j. eapply subst0_sort_target_erase_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  (3) The full typing theorem, conditional only on the erasure interfaces.  *)
(* ========================================================================== *)

Theorem muapp_sort_from_erase_reflect_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros Hp He f a T U h Hchk Hv Hc Hw.
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
      eapply ao_chk_mui_sort_erase_glm; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_erase_glm; eassumption.
Qed.

Print Assumptions ao_chk_mui_sort_erase_glm.
Print Assumptions ao_chk_mus_sort_erase_glm.
Print Assumptions muapp_sort_from_erase_reflect_glm.
Print Assumptions conv_pisort_codomain_from_erase_reflect_glm.
Print Assumptions stable_sort_erase_reflect_glm.
