(* ========================================================================== *)
(*  _glm_phi_erase_reflect_close_codomain.v — GLM worker 2: Pi-codomain       *)
(*  extraction from the erasure reflection layer.                             *)
(*                                                                            *)
(*  Pipeline (small named lemmas, premises are binders):                      *)
(*    1. cjoin_erase_sort_reflect_glm — a cjoin against a stable sort          *)
(*       endpoint reduces, via stability (rtc_cstep_sort_id), to an rtc        *)
(*       cstep path into TSort j; the stable sort reflection of the           *)
(*       reflect layer converts the source.                                   *)
(*    2. conv_pi_cod_sort_from_erase_glm — Pi-codomain transport whenever      *)
(*       the source codomain is sort-convertible: conv_phi_cjoin +            *)
(*       cjoin_pi_inv put the two erasures in cjoin, the sort-convertible     *)
(*       side pins the common reduct to a sort, reflection converts back.     *)
(*    3. conv_pisort_codomain_from_erase_reflect_glm — the required exact     *)
(*       extraction at the fixed source TPi IT (TSort 0).                     *)
(*    4. The sub-level extraction sub_pisort0_cod_sort_erase_glm, mirroring   *)
(*       the close bundle's pi_cod_sort_inv architecture with the             *)
(*       erasure-reflection premises in place of Pi-codomain injectivity.     *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort.                         *)
(* ========================================================================== *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep
  _glm_muapp_sort_origin _glm_muapp_sort_close
  _glm_phi_erase_reflect_close_reflect.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. cjoin against a stable sort endpoint re-enters conv via reflection.    *)
(* ========================================================================== *)

Lemma cjoin_erase_sort_reflect_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall B j, cjoin (TSort j) (phi_erase B) -> conv B (TSort j).
Proof.
  intros Hp He B j [w [Hw1 Hw2]].
  assert (Hw : w = TSort j) by (eapply rtc_cstep_sort_id; exact Hw1).
  subst w.
  eapply stable_sort_erase_reflect_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  2. Pi-codomain transport at a sort-convertible source codomain.           *)
(* ========================================================================== *)

Lemma conv_pi_cod_sort_from_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall A0 B0 A1 B1 j,
    conv B0 (TSort j) ->
    conv (TPi A0 B0) (TPi A1 B1) ->
    conv B1 (TSort j).
Proof.
  intros Hp He A0 B0 A1 B1 j Hj Hc.
  pose proof (conv_phi_cjoin _ _ Hc) as Hcj.
  cbn [phi_erase] in Hcj.
  destruct (cjoin_pi_inv _ _ _ _ Hcj) as [_ Hd2].
  pose proof (conv_phi_cjoin _ _ Hj) as Hj2.
  cbn [phi_erase] in Hj2.
  assert (Hchain : cjoin (TSort j) (phi_erase B1)).
  { eapply cjoin_trans.
    - apply cjoin_sym; exact Hj2.
    - exact Hd2. }
  eapply cjoin_erase_sort_reflect_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  3. The required exact extraction at the fixed source TPi IT (TSort 0).    *)
(* ========================================================================== *)

Theorem conv_pisort_codomain_from_erase_reflect_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall IT A B,
    conv (TPi IT (TSort 0)) (TPi A B) -> conv B (TSort 0).
Proof.
  intros Hp He IT A B Hc.
  eapply conv_pi_cod_sort_from_erase_glm;
    [exact Hp | exact He | apply cv_refl | exact Hc].
Qed.

(* ========================================================================== *)
(*  4. The sub-level extraction, via the pi_cod_sort_inv architecture.        *)
(* ========================================================================== *)

(* Introduction of the conv-side invariant at a syntactic Pi whose codomain
   is sort-convertible — the erasure-reflection replacement of
   pi_cod_sort_inv_intro_glm. *)
Lemma pi_cod_sort_inv_intro_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall A0 B0 j, conv B0 (TSort j) -> pi_cod_sort_inv_glm (TPi A0 B0).
Proof.
  intros Hp He A0 B0 j Hj A B Hc.
  exists j.
  eapply conv_pi_cod_sort_from_erase_glm; eassumption.
Qed.

(* The invariant is preserved by every sub rule; only the su_pi rebuild
   consumes an interface, and it is discharged by the erasure binders. *)
Lemma sub_pi_cod_sort_inv_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall G X Y, sub G X Y -> pi_cod_sort_inv_glm X -> pi_cod_sort_inv_glm Y.
Proof.
  intros Hp He G X Y Hsub.
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
    eapply pi_cod_sort_inv_intro_erase_glm;
      [exact Hp | exact He | exact Hj'].
  - (* su_forget: the target is a stuck Carrier application *)
    intros P Q Hc. exfalso. eapply glm_conv_carrierapp_pi_glm; exact Hc.
  - (* su_sig: the target is a stuck mu-S application *)
    intros P Q Hc. exfalso. eapply glm_conv_musapp_pi_glm; exact Hc.
Qed.

Lemma sub_pisort0_cod_sort_erase_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall G IT A B, sub G (TPi IT (TSort 0)) (TPi A B) ->
  exists j, conv B (TSort j).
Proof.
  intros Hp He G IT A B Hsub.
  eapply pi_cod_sort_inv_pi_elim_glm.
  eapply sub_pi_cod_sort_inv_erase_glm;
    [exact Hp | exact He | exact Hsub |].
  eapply pi_cod_sort_inv_intro_erase_glm;
    [exact Hp | exact He | apply cv_refl].
Qed.

Print Assumptions conv_pisort_codomain_from_erase_reflect_glm.
Print Assumptions sub_pisort0_cod_sort_erase_glm.
