(* The fundamental lemma of the binary relational model. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelFundData.
Import ListNotations.

Theorem rel_fundamental : forall Gamma t A, typing Gamma t A -> FP Gamma t A.
Proof.
  intros Gamma t A H; induction H.
  all: first
    [ solve [eapply fund_var; eassumption]
    | solve [apply fund_sort]
    | solve [eapply fund_pi; eassumption]
    | solve [eapply fund_sigma; eassumption]
    | solve [eapply fund_lam; eassumption]
    | solve [eapply fund_app; eassumption]
    | solve [eapply fund_pair; eassumption]
    | solve [eapply fund_fst; eassumption]
    | solve [eapply fund_snd; eassumption]
    | solve [eapply fund_alpha; eassumption]
    | solve [eapply fund_conv; eassumption]
    | solve [eapply fund_cumul; eassumption]
    | solve [apply fund_unitT] | solve [apply fund_unit] | solve [apply fund_uid]
    | solve [apply fund_tag] | solve [apply fund_enumu] | solve [apply fund_nile]
    | solve [eapply fund_conse; eassumption]
    | solve [eapply fund_enumt; eassumption]
    | solve [eapply fund_zero; eassumption]
    | solve [eapply fund_succ; eassumption]
    | solve [eapply fund_epi; eassumption]
    | solve [eapply fund_switch; eassumption]
    | solve [eapply fund_idesc; eassumption]
    | solve [eapply fund_ivar; eassumption]
    | solve [eapply fund_i1; eassumption]
    | solve [eapply fund_ibot; eassumption]
    | solve [eapply fund_iprod; eassumption]
    | solve [eapply fund_ipi; eassumption]
    | solve [eapply fund_isig; eassumption]
    | solve [eapply fund_ichoice; eassumption]
    | solve [eapply fund_interp; eassumption]
    | solve [eapply fund_mui; eassumption]
    | solve [eapply fund_in_mui; eassumption]
    | solve [eapply fund_iall; eassumption]
    | solve [eapply fund_hyps; eassumption]
    | solve [eapply fund_ind; eassumption]
    | solve [eapply fund_close; eassumption]
    | solve [eapply fund_in_close; eassumption]
    | solve [eapply fund_close_case; eassumption]
    | solve [eapply fund_close_ind; eassumption]
    | solve [eapply fund_cumul_fun; eassumption]
    ].
Qed.

Print Assumptions rel_fundamental.
