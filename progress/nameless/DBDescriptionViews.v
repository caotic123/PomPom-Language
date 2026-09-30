(* Typed description views need computation preservation, not eta typing. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEtaPostponement.

Lemma psteps_conversion : forall t u, rtc pstep t u -> conv t u.
Proof.
  intros t u H; induction H; [apply cv_refl|].
  eapply cv_trans; [apply reductions_conversion, pstep_reductions; exact H|exact IHrtc].
Qed.
Lemma etas_conversion : forall t u, rtc epstep t u -> conv t u.
Proof.
  intros t u H; induction H; [apply cv_refl|].
  eapply cv_trans; [apply reductions_conversion, epstep_reductions; exact H|exact IHrtc].
Qed.
Lemma reduction_iprod : forall A B t, reduction (TIProd A B) t ->
  exists A' B', t = TIProd A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; inversion H; subst; cbn [root_step] in *; try discriminate; eauto 6 using rtc_refl, rtc_one. Qed.
Lemma reduction_ichoice : forall A B t, reduction (TIChoice A B) t ->
  exists A' B', t = TIChoice A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; inversion H; subst; cbn [root_step] in *; try discriminate; eauto 6 using rtc_refl, rtc_one. Qed.
Lemma reduces_nile : forall t, rtc reduction TNilE t -> t = TNilE.
Proof.
  intros t H; remember TNilE as src eqn:E; induction H; subst; auto.
  inversion H; subst; cbn [root_step] in *; discriminate.
Qed.

Section EtaBinary.
Variable C : term -> term -> term.
Hypothesis etaC : forall t A B, epstep t (C A B) -> not_lambda t = true ->
  exists A' B', t = C A' B' /\ epstep A' A /\ epstep B' B.
Lemma etas_binary_inverse : forall t u, rtc epstep t u -> forall A B,
  u = C A B -> not_lambda t = true ->
  exists A' B', t = C A' B' /\ rtc epstep A' A /\ rtc epstep B' B.
Proof.
  intros t u H; induction H; intros A B EQ Hnl; subst.
  - exists A,B; repeat split; auto using rtc_refl.
  - destruct (IHrtc _ _ eq_refl (epstep_not_lambda _ _ H Hnl))
      as [A1 [B1 [-> [HA HB]]]].
    destruct (etaC _ _ _ H Hnl) as [A0 [B0 [-> [HA0 HB0]]]].
    exists A0,B0; repeat split; eauto using rtc_step.
Qed.
End EtaBinary.

Lemma eta_iprod_inverse : forall t A B, epstep t (TIProd A B) -> not_lambda t = true ->
  exists A' B', t = TIProd A' B' /\ epstep A' A /\ epstep B' B.
Proof. intros; inversion H; subst; cbn [not_lambda] in *; try discriminate; eauto. Qed.
Lemma eta_ichoice_inverse : forall t A B, epstep t (TIChoice A B) -> not_lambda t = true ->
  exists A' B', t = TIChoice A' B' /\ epstep A' A /\ epstep B' B.
Proof. intros; inversion H; subst; cbn [not_lambda] in *; try discriminate; eauto. Qed.
Lemma etas_nile_inverse : forall t u, rtc epstep t u -> u = TNilE ->
  not_lambda t = true -> t = TNilE.
Proof.
  intros t u H; induction H; intros E Hnl; subst; auto.
  specialize (IHrtc eq_refl (epstep_not_lambda _ _ H Hnl)); subst y.
  inversion H; subst; cbn [not_lambda] in *; congruence.
Qed.

Theorem typed_iprod_view : forall Gamma IT D A B,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> conv D (TIProd A B) ->
  exists A' B', typing Gamma A' (TIDesc IT) /\ typing Gamma B' (TIDesc IT) /\
    conv A A' /\ conv B B' /\ conv D (TIProd A' B').
Proof.
  intros Gamma IT D A B HI HD HC.
  destruct (conversion_joinable _ _ HC) as [w [HDw HPw]].
  destruct (reduces_binary TIProd reduction_iprod _ _ _ HPw) as [U [V [-> [HU HV]]]].
  destruct (typed_reduction_factorization _ _ _ HD _ HDw) as [v [Hv [Hcore Heta]]].
  assert (Hnl : not_lambda v = true) by exclude_lambda.
  destruct (etas_binary_inverse TIProd eta_iprod_inverse _ _ Heta _ _ eq_refl Hnl)
    as [A' [B' [-> [HA HB]]]].
  destruct (description_inversion _ _ _ HI Hv) as [HA' HB'].
  exists A',B'; repeat split; try assumption.
  - eapply cv_trans; [exact (reductions_conversion _ _ HU)|].
    apply cv_sym, etas_conversion; exact HA.
  - eapply cv_trans; [exact (reductions_conversion _ _ HV)|].
    apply cv_sym, etas_conversion; exact HB.
  - now apply psteps_conversion.
Qed.

Theorem typed_empty_choice_view : forall Gamma IT D T,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> conv D (TIChoice TNilE T) ->
  exists T', typing Gamma T' (arrow (TEnumT TNilE) (TIDesc IT)) /\ conv D (TIChoice TNilE T').
Proof.
  intros Gamma IT D T HI HD HC.
  destruct (conversion_joinable _ _ HC) as [w [HDw HPw]].
  destruct (reduces_binary TIChoice reduction_ichoice _ _ _ HPw) as [E [U [-> [HE HU]]]].
  apply reduces_nile in HE; subst E.
  destruct (typed_reduction_factorization _ _ _ HD _ HDw) as [v [Hv [Hcore Heta]]].
  assert (Hnl : not_lambda v = true) by exclude_lambda.
  destruct (etas_binary_inverse TIChoice eta_ichoice_inverse _ _ Heta _ _ eq_refl Hnl)
    as [E [T' [-> [HE HT]]]].
  destruct (description_inversion _ _ _ HI Hv) as [HEtype HTtype].
  assert (HEnl : not_lambda E = true) by exclude_lambda.
  pose proof (etas_nile_inverse _ _ HE eq_refl HEnl) as ->.
  exists T'; split; [exact HTtype|now apply psteps_conversion].
Qed.

Print Assumptions typed_iprod_view.
Print Assumptions typed_empty_choice_view.
