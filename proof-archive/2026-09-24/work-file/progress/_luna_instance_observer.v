Require Import Progress SignatureInstances SignatureConversion _parent_instance_join
  _parent_instance_pruning _luna_instance_shape.
Import TypeRules Progress._tmp_epstep Progress._work_cjoin.

Section Observer.
Variable B0 : term.
Variable O : term -> Prop.
Variable Hcore : forall L L', cjoin (phi_erase L) (phi_erase L') -> O L -> O L'.
Variable Hprune : forall B L L', cjoin (phi_erase B0) (phi_erase B) ->
  prune_labels B L L' -> O L -> O L'.

Definition instance_observation (t : term) : Prop :=
  exists B L i, t = signature_instance B L i /\
    cjoin (phi_erase B0) (phi_erase B) /\ O L.

Lemma fstep_observation : forall t u,
  fstep t u -> instance_observation t -> instance_observation u.
Proof.
  intros t u Hred [B [L [i [-> [HB HO]]]]].
  destruct (fstep_instance_inv B L i u Hred)
    as [[B' [-> H]] | [[L' [-> H]] | [i' [-> H]]]].
  - exists B', L, i. split; [reflexivity|]. split.
    + eapply cjoin_trans; [exact HB|apply conv_phi_cjoin; apply fstep_conv; exact H].
    + exact HO.
  - exists B, L', i. split; [reflexivity|]. split; [exact HB|].
    apply Hcore with (L := L) (L' := L');
      [apply conv_phi_cjoin; apply fstep_conv; exact H|exact HO].
  - exists B, L, i'. repeat split; assumption.
Qed.

Lemma prune_observation : forall t u,
  prune_term t u -> instance_observation t -> instance_observation u.
Proof.
  intros t u Hpr [B [L [i [-> [HB HO]]]]].
  destruct (prune_instance_inv B L i u Hpr) as [B' [L' [i' [-> [HPB [HPL HPI]]]]]].
  exists B', L', i'. split; [reflexivity|]. split.
  - rewrite (prune_erase _ _ HPB) in HB; exact HB.
  -
  apply Hprune with (B := B) (L := L) (L' := L'); assumption.
Qed.

Lemma instance_path_observation : forall t u,
  rtc instance_reduce t u -> instance_observation t -> instance_observation u.
Proof.
  assert (Hf : forall t u, rtc fstep t u ->
      instance_observation t -> instance_observation u).
  { intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
    - exact Ho.
    - apply IH. exact (fstep_observation t v Htv Ho). }
  assert (Hp : forall t u, rtc prune_term t u ->
      instance_observation t -> instance_observation u).
  { intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
    - exact Ho.
    - apply IH. exact (prune_observation t v Htv Ho). }
  intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
  - exact Ho.
  - apply IH. destruct Htv as [t v Hfv|t v Hpv].
    + apply (Hf t v); assumption.
    + apply (Hp t v); assumption.
Qed.

End Observer.

Print Assumptions fstep_observation.
Print Assumptions prune_observation.
Print Assumptions instance_path_observation.
