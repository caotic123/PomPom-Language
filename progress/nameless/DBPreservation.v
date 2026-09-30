From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBRootPreservation.
Import ListNotations.

Ltac computation_conversion :=
  first [assumption | apply cv_refl | apply cv_step; assumption |
    apply cv_sym, cv_step; assumption |
    apply conversion_lift; computation_conversion |
    apply substitution_argument_conversion; computation_conversion |
    apply conversion_subst; computation_conversion |
    apply cv_compatible; constructor; computation_conversion].

Lemma enum_motive_formation : forall Gamma E k,
  typing Gamma E TEnumU -> typing Gamma (TPi (TEnumT E) (TSort k)) (TSort (S k)).
Proof.
  intros. change (TSort (S k)) with (TSort (Nat.max 0 (S k))).
  apply ty_pi; eauto using ty_enumt, ty_sort, wf_cons, typing_context.
Qed.
Lemma enum_motive_transport : forall Gamma E E' k P,
  typing Gamma P (TPi (TEnumT E) (TSort k)) -> typing Gamma E' TEnumU ->
  conv E E' -> typing Gamma P (TPi (TEnumT E') (TSort k)).
Proof.
  intros. eapply ty_conv; [eassumption|apply enum_motive_formation; eassumption|computation_conversion].
Qed.
Lemma enum_position_transport : forall Gamma E E' e,
  typing Gamma e (TEnumT E) -> typing Gamma E' TEnumU -> conv E E' -> typing Gamma e (TEnumT E').
Proof.
  intros. eapply ty_conv; [eassumption|apply ty_enumt; eassumption|computation_conversion].
Qed.
Lemma epi_transport : forall Gamma k E E' P p,
  typing Gamma p (TEPi k E P) -> typing Gamma E' TEnumU ->
  typing Gamma P (TPi (TEnumT E') (TSort k)) -> conv E E' -> typing Gamma p (TEPi k E' P).
Proof.
  intros. eapply ty_conv; [eassumption|apply ty_epi; eassumption|computation_conversion].
Qed.
Lemma interpretation_transport : forall Gamma IT D D' X xs,
  typing Gamma xs (TInterp IT D X) -> typing Gamma IT (TSort 0) ->
  typing Gamma D' (TIDesc IT) -> typing Gamma X (Family IT) -> conv D D' ->
  typing Gamma xs (TInterp IT D' X).
Proof.
  intros. eapply ty_conv; [eassumption|apply ty_interp; eassumption|computation_conversion].
Qed.

Theorem preservation : forall Gamma t T,
  typing Gamma t T -> forall u, step t u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros u Hr.
  all: try match goal with
    HC : conv ?A ?B, IH : forall u, step ?t u -> typing ?G u ?A |- typing ?G _ ?B =>
      eapply ty_conv; [eapply IH; exact Hr|eassumption|exact HC]
    end.
  all: try match goal with
    HL : ?j <= ?k, IH : forall u, step ?t u -> typing ?G u (TSort ?j) |- typing ?G _ (TSort ?k) =>
      eapply ty_cumul; [eapply IH; exact Hr|exact HL]
    end.
  all: try match goal with
    HA : universe_le ?C ?A, HB : universe_le ?B ?D,
    IH : forall u, step ?t u -> typing ?G u (TPi ?A ?B) |- typing ?G _ (TPi ?C ?D) =>
      eapply ty_cumul_fun; [eapply IH; exact Hr|eassumption|eassumption|exact HA|exact HB]
    end.
  all: inversion Hr; subst; clear Hr.
  all: try solve [match goal with HH : root_step ?src = Some ?dst |- _ =>
    eapply root_preservation with (t:=src); [eauto 2 using typing|exact HH] end].
  all: try solve [econstructor; eauto].
  - assert (Ha' : typing Gamma a' A) by auto.
    destruct (sigma_components _ _ _ H _ _ eq_refl) as [j [l [HA HB]]].
    eapply ty_pair; [exact H|exact Ha'|].
    eapply ty_conv; [exact H1|exact (substitution _ _ _ _ _ HB Ha')|computation_conversion].
  - eapply ty_conv; [eapply smart_snd; [eassumption|eauto]|eassumption|computation_conversion].
  - assert (HE' : typing Gamma E' TEnumU) by auto.
    apply ty_epi; [exact HE'|eapply enum_motive_transport; eauto using cv_step].
  - assert (HE' : typing Gamma E' TEnumU) by auto.
    assert (HP' : typing Gamma P (TPi (TEnumT E') (TSort k)))
      by (eapply enum_motive_transport; eauto using cv_step).
    eapply smart_switch; [exact HE'|exact HP'| |];
      eauto using epi_transport, enum_position_transport, cv_step.
  - eapply ty_conv; [eapply smart_switch; eauto|eassumption|computation_conversion].
  - apply ty_iall; eauto using interpretation_transport, cv_step.
  - eapply ty_conv; [eapply smart_hyps; eauto using interpretation_transport, cv_step|eassumption|computation_conversion].
  - eapply ty_conv; [eapply smart_hyps; eauto|eassumption|computation_conversion].
  - eapply ty_conv; [eapply smart_ind; eauto|eassumption|computation_conversion].
  - eapply ty_conv; [eapply smart_close_case; eauto|eassumption|computation_conversion].
  - eapply ty_conv; [eapply smart_close_ind; eauto|eassumption|computation_conversion].
Qed.
