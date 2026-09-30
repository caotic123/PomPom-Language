(* Checked type changes for annotated terms reuse the raw comparison proof;
   they never change the annotated program being checked. *)
From Stdlib Require Import List Arith.
Require Export annotated.ASubstitution.
Require nameless.DBTypeComparison.
Module RC := nameless.DBTypeComparison.
Module RCh := nameless.DBCumulativeTyping.

Lemma universe_le_typing : forall Gamma t A B,
  typing Gamma t A -> RT.universe_le A B -> RT.type_wf Gamma B ->
  typing Gamma t B.
Proof.
  intros Gamma t A B Ht HU HB; destruct HU; [exact Ht| |].
  - eapply ty_cumul; eassumption.
  - destruct (type_correctness _ _ _ Ht) as [j HA], HB as [k HB].
    eapply ty_cumul_fun; eassumption.
Qed.

Lemma type_change_typing : forall Gamma A B,
  RCh.type_change Gamma A B -> forall t, typing Gamma t A -> typing Gamma t B.
Proof.
  intros Gamma A B H; induction H; intros t HT.
  - destruct H0 as [k HB]; eapply ty_conv; eassumption.
  - eapply universe_le_typing; eassumption.
  - auto.
Qed.

Theorem comparison_typing : forall Gamma t A B,
  typing Gamma t A -> RC.type_comparison A B -> RT.type_wf Gamma B ->
  typing Gamma t B.
Proof.
  intros Gamma t A B HT HC HB.
  eapply type_change_typing; [apply RC.comparison_realization; [exact HC| |exact HB]|exact HT].
  exact (type_correctness _ _ _ HT).
Qed.

Print Assumptions comparison_typing.
