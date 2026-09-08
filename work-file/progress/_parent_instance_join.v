Require Import Progress _parent_instance_pruning _parent_pruning_diamond
  _parent_pruning_commute _luna_instance_core_paths _luna_instance_union
  _luna_instance_conversion.
Import TypeRules.

Definition instance_reduce := block_union term fstep prune_term.
Definition instance_join t u := exists w, rtc instance_reduce t w /\ rtc instance_reduce u w.

Lemma instance_reduce_confluent : confluent instance_reduce.
Proof.
  apply block_union_confluent; [apply fstep_confluent_instance|
    apply prune_term_confluent|exact fstep_prune_commute].
Qed.
Lemma instance_join_refl : forall t, instance_join t t.
Proof. intro t; exists t; split; apply rtc_refl. Qed.
Lemma instance_join_sym : forall t u, instance_join t u -> instance_join u t.
Proof. intros t u [w [H1 H2]]; exists w; auto. Qed.
Lemma instance_join_trans : forall t u v,
  instance_join t u -> instance_join u v -> instance_join t v.
Proof.
  intros t u v [w [Htw Huw]] [z [Huz Hvz]].
  destruct (instance_reduce_confluent u w z Huw Huz) as [q [Hwq Hzq]].
  exists q; split; eapply rtc_trans; eassumption.
Qed.
Lemma fconv_instance_join : forall t u, fconv t u -> instance_join t u.
Proof.
  intros t u H; induction H.
  - exists u. split; [apply rtc_one, bu_left, rtc_one; exact H|apply rtc_refl].
  - apply instance_join_refl.
  - apply instance_join_sym; assumption.
  - eapply instance_join_trans; eassumption.
Qed.
Lemma instance_conv_join : forall t u, instance_conv t u -> instance_join t u.
Proof.
  intros t u H; induction H.
  - apply fconv_instance_join; assumption.
  - exists u. split; [apply rtc_one, bu_right, rtc_one; exact H|apply rtc_refl].
  - apply instance_join_refl.
  - apply instance_join_sym; assumption.
  - eapply instance_join_trans; eassumption.
Qed.
Print Assumptions instance_conv_join.
