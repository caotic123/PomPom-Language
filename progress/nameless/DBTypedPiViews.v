(* Recover a well-typed Pi representative using computation preservation.
   This does not require subject reduction for eta. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDescriptionViews.

Lemma eta_pi_inverse : forall t A B, epstep t (TPi A B) -> not_lambda t = true ->
  exists A' B', t = TPi A' B' /\ epstep A' A /\ epstep B' B.
Proof. intros; inversion H; subst; cbn [not_lambda] in *; try discriminate; eauto. Qed.

Theorem typed_pi_view : forall Gamma T k A B,
  typing Gamma T (TSort k) -> conv T (TPi A B) ->
  exists A' B', typing Gamma (TPi A' B') (TSort k) /\
    conv A A' /\ conv B B' /\ conv T (TPi A' B').
Proof.
  intros Gamma T k A B HT HC.
  destruct (conversion_joinable _ _ HC) as [w [HTw HPw]].
  destruct (reduces_binary TPi reduction_pi _ _ _ HPw) as [U [V [-> [HU HV]]]].
  destruct (typed_reduction_factorization _ _ _ HT _ HTw) as [v [Hv [Hcore Heta]]].
  assert (Hnl : not_lambda v = true) by exclude_lambda.
  destruct (etas_binary_inverse TPi eta_pi_inverse _ _ Heta _ _ eq_refl Hnl)
    as [A' [B' [-> [HA HB]]]].
  exists A',B'; repeat split; try assumption.
  - eapply cv_trans; [exact (reductions_conversion _ _ HU)|].
    apply cv_sym, etas_conversion; exact HA.
  - eapply cv_trans; [exact (reductions_conversion _ _ HV)|].
    apply cv_sym, etas_conversion; exact HB.
  - now apply psteps_conversion.
Qed.

Print Assumptions typed_pi_view.
