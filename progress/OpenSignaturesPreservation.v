(* Execution preservation is independent of full beta/eta preservation. *)
From Stdlib Require Import List.
Require Export OpenSignaturesTypingEncoding.
Require nameless.DBPreservation.

Lemma encode_step : forall t u, step t u -> forall env,
  nameless.DBCore.step (encode env t) (encode env u).
Proof.
  intros t u H; induction H; intros env; cbn [encode];
    try solve [constructor; auto].
  apply nameless.DBCore.st_root; now apply encode_root_step.
Qed.

Theorem named_preservation : forall Gamma t u T,
  typing Gamma t T -> step t u -> typing Gamma u T.
Proof.
  intros Gamma t u T Ht Hr.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [Delta [env [HC HD]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HD) as HT.
  pose proof (nameless.DBPreservation.preservation _ _ _ HT _ (encode_step _ _ Hr env)) as Hu.
  eapply typing_reflection_given; [exact Hu|exact HC|reflexivity|reflexivity].
Qed.
