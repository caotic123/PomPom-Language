(* GLM worker 2 — quotient-conversion bundle, part 3 (main): every conv is a *)
(* quotient conversion.                                                      *)
(*                                                                           *)
(*   conv_qconv_glm : forall t u, conv t u -> qconv t u                      *)
(*                                                                           *)
(* by induction on conv: cv_step and cv_eta become single cjoin links (the   *)
(* combined phase carries fstep and eta: fstep_cstep), cv_phi becomes a      *)
(* single mueq link via me_muapp, and every congruence rule maps through the *)
(* corresponding qconv context of _glm_qconv_congr (cjoin halves from        *)
(* _luna_cjoin_congr, mueq halves from the structural me_ constructors);     *)
(* the TCase rules use the head/motive and one-branch-replacement contexts.  *)
(* EnumT injection is NOT attempted here.                                    *)

Require Import Progress.
Require Import _work_cjoin _luna_mueq _luna_mueq_equiv
               _glm_qconv_def _glm_qconv_congr.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Theorem conv_qconv_glm : forall t u, conv t u -> qconv t u.
Proof.
  intros t u H. induction H.
  - (* cv_step : a single cjoin link, via fstep_cstep *)
    apply step_qconv; assumption.
  - (* cv_refl *)
    apply qconv_refl.
  - (* cv_sym *)
    apply qconv_sym; assumption.
  - (* cv_trans *)
    eapply qconv_trans; eassumption.
  - (* cv_eta : a single cjoin link, via fs_eta *)
    apply eta_qconv.
  - (* cv_phi : a single mueq link, via me_muapp *)
    eapply phi_qconv; eauto.
  - (* cv_pi *)     apply qconv_pi; assumption.
  - (* cv_lam *)    apply qconv_lam; assumption.
  - (* cv_app *)    apply qconv_app; assumption.
  - (* cv_sigma *)  apply qconv_sigma; assumption.
  - (* cv_pair *)   apply qconv_pair; assumption.
  - (* cv_fst *)    apply qconv_fst; assumption.
  - (* cv_snd *)    apply qconv_snd; assumption.
  - (* cv_conse *)  apply qconv_conse; assumption.
  - (* cv_enumt *)  apply qconv_enumt; assumption.
  - (* cv_esucc *)  apply qconv_esucc; assumption.
  - (* cv_epi *)    apply qconv_epi; assumption.
  - (* cv_switch *) apply qconv_switch; assumption.
  - (* cv_idesc *)  apply qconv_idesc; assumption.
  - (* cv_ivar *)   apply qconv_ivar; assumption.
  - (* cv_iprod *)  apply qconv_iprod; assumption.
  - (* cv_ipi *)    apply qconv_ipi; assumption.
  - (* cv_isig *)   apply qconv_isig; assumption.
  - (* cv_ichoice *) apply qconv_ichoice; assumption.
  - (* cv_interp *) apply qconv_interp; assumption.
  - (* cv_mui *)    apply qconv_mui; assumption.
  - (* cv_mus *)    apply qconv_mus; assumption.
  - (* cv_in *)     apply qconv_in; assumption.
  - (* cv_ind *)    apply qconv_ind; assumption.
  - (* cv_iall *)   apply qconv_iall; assumption.
  - (* cv_hyps *)   apply qconv_hyps; assumption.
  - (* cv_list *)   apply qconv_list; assumption.
  - (* cv_lnil *)   apply qconv_lnil; assumption.
  - (* cv_lcons *)  apply qconv_lcons; assumption.
  - (* cv_case : head/motive congruence, branches fixed *)
    apply qconv_case_mq; assumption.
  - (* cv_case_br : one branch replacement, head/motive fixed *)
    apply qconv_case_br; assumption.
Qed.

Print Assumptions conv_qconv_glm.
