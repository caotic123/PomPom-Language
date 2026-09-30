(* All root and congruence cases are checked here. The single explicit
   premise is general eta subject reduction; this is a factoring lemma,
   not a proof of full preservation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBOperatorFormations.
Import ListNotations.

Ltac full_computation_conversion :=
  first [assumption | apply cv_refl | apply cv_step; assumption |
    apply cv_sym, cv_step; assumption |
    apply reduction_conversion; assumption | apply cv_sym, reduction_conversion; assumption |
    apply conversion_lift; full_computation_conversion |
    apply substitution_argument_conversion; full_computation_conversion |
    apply conversion_subst; full_computation_conversion |
    apply cv_compatible; constructor; full_computation_conversion].

Ltac operator_conversion :=
  unfold arrow, product, Def, Family, total, motive, recursive_method,
    close_motive, close_case_method, close_ind_method, mu_ind_method,
    diagonal_motive, payload, carrier, CloseAt, MuAt;
  full_computation_conversion.

Create HintDb formation0.
Create HintDb formation1.
Create HintDb formation2.
Create HintDb formation3.
#[local] Hint Resolve ty_interp ty_iall ty_idesc ty_enumt def_application smart_close
   smart_mui close_at_formation mu_at_formation payload_formation total_formation
   motive_formation def_formation family_formation diagonal_motive_typing
   close_motive_application motive_application smart_in_close smart_in_mui
   family_application recursive_method_formation close_motive_formation
   mu_method_formation close_method_formation close_case_method_formation
   arrow_formation enum_motive_formation sort_codomain_formation ty_epi : formation0 formation1 formation2 formation3.

Ltac transport_from_existing solver :=
 match goal with |- typing ?Gamma ?t ?T =>
   match goal with H : typing Gamma t ?S |- _ =>
     let HC := fresh "Hconvert" in assert (HC : conv S T) by operator_conversion;
     eapply convert_type; [exact H|eexists; solve [solver]|exact HC]
   end
 end.
#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation0) : formation1.
#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation1) : formation2.
#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation2) : formation3.

Section FullPreservation.
Variable eta_preserve : forall Gamma f T,
  typing Gamma (TLam (TApp (lift 1 0 f) (TVar 0))) T -> typing Gamma f T.

Theorem full_preservation_from_eta : forall Gamma t T,
  typing Gamma t T -> forall u, reduction t u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros u Hr.
  all: try match goal with
    HC : conv ?A ?B, IH : forall u, reduction ?t u -> typing ?G u ?A |- typing ?G _ ?B =>
      eapply ty_conv; [eapply IH; exact Hr|eassumption|exact HC]
    end.
  all: try match goal with
    HL : ?j <= ?k, IH : forall u, reduction ?t u -> typing ?G u (TSort ?j) |- typing ?G _ (TSort ?k) =>
      eapply ty_cumul; [eapply IH; exact Hr|exact HL]
    end.
  all: try match goal with
    HA : universe_le ?C ?A, HB : universe_le ?B ?D,
    IH : forall u, reduction ?t u -> typing ?G u (TPi ?A ?B) |- typing ?G _ (TPi ?C ?D) =>
      eapply ty_cumul_fun; [eapply IH; exact Hr|eassumption|eassumption|exact HA|exact HB]
    end.
  all: inversion Hr; subst; clear Hr.
  all: try solve [match goal with HH : root_step ?src = Some ?dst |- _ =>
    eapply root_preservation with (t:=src); [eauto 2 using typing|exact HH] end].
  all: try solve [econstructor; eauto].
  all: try solve [match goal with |- typing ?G ?f ?T =>
    apply eta_preserve; eapply ty_lam; eassumption end].
  all: repeat match goal with
    IH : forall u, reduction ?src u -> typing ?G u ?T,
    Hr : reduction ?src ?dst |- _ =>
    let Hnew := fresh "Hreduced" in pose proof (IH dst Hr) as Hnew; clear IH
  end.
  all: try solve [eauto 8 using smart_ipi, smart_isig, smart_ichoice, ty_epi,
    smart_switch, ty_interp, ty_iall, smart_mui, smart_close with formation3].
  all: try solve [eapply ty_conv;
    [first [eapply smart_app|eapply smart_snd|eapply smart_switch|eapply smart_hyps|
      eapply smart_ind|eapply smart_close_case|eapply smart_close_ind|eapply smart_mui|eapply smart_close];
      solve [eauto 8 with formation3] | eassumption | operator_conversion]].
  - apply ty_pi; [assumption|].
    eapply context_conversion; [exact H|eassumption|apply reduction_conversion; eassumption|exact H0].
  - apply ty_sigma; [assumption|].
    eapply context_conversion; [exact H|eassumption|apply reduction_conversion; eassumption|exact H0].
  - destruct (sigma_components _ _ _ H _ _ eq_refl) as [j [l [HA HB]]].
    eapply ty_pair; [exact H|eassumption|].
    eapply ty_conv; [exact H1|exact (substitution _ _ _ _ _ HB Hreduced)|operator_conversion].
Qed.
End FullPreservation.
