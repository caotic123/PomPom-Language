Require Import Progress SignatureConversion SignatureInstances _parent_instance_pruning.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules Progress._work_cjoin.

Definition prune_diamond_at t := forall u v,
  prune_term t u -> prune_term t v ->
  exists w, prune_term u w /\ prune_term v w.
Definition prune_cross_at t := forall B u v,
  prune_labels B t u -> prune_term t v ->
  exists w, prune_term u w /\ prune_labels B v w.
Definition labels_diamond_at t := forall B u v,
  prune_labels B t u -> prune_labels B t v ->
  exists w, prune_labels B u w /\ prune_labels B v w.

Lemma prune_branches_diamond_from : forall bs,
  (forall c b, In (c,b) bs -> prune_diamond_at c /\ prune_diamond_at b) ->
  forall us vs, prune_branches bs us -> prune_branches bs vs ->
  exists ws, prune_branches us ws /\ prune_branches vs ws.
Proof.
  induction bs as [|[c b] bs IH]; intros HP us vs H1 H2;
    inversion H1; subst; inversion H2; subst.
  - exists []; split; constructor.
  - destruct (HP c b (or_introl eq_refl)) as [HC HB].
    unfold prune_diamond_at in HC, HB.
    destruct (HC _ _ H4 H5) as [cw [HC1 HC2]].
    destruct (HB _ _ H6 H9) as [bw [HB1 HB2]].
    assert (Htail : forall cx bx, In (cx,bx) bs ->
      prune_diamond_at cx /\ prune_diamond_at bx).
    { intros cx bx Hin. apply HP. right; exact Hin. }
    destruct (IH Htail _ _ H7 H10) as [ws [HS1 HS2]].
    exists ((cw,bw)::ws); split; constructor; assumption.
Qed.

Ltac pruning_size := cbn; lia.

Ltac pruning_join_children IH :=
  repeat match goal with
  | H1 : prune_term ?x ?y, H2 : prune_term ?x ?z |- _ =>
    first [constr_eq H1 H2; fail 1 |
      let Hp := fresh "Hp" in
      let w := fresh "w" in let Hy := fresh "Hy" in let Hz := fresh "Hz" in
      pose proof (proj1 (IH x ltac:(pruning_size))) as Hp;
      destruct (Hp _ _ H1 H2) as [w [Hy Hz]];
      clear H1 H2 Hp]
  end.

Ltac pruning_plain IH :=
  intros u v H1 H2; inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
  pruning_join_children IH;
  eexists; split; constructor; eassumption.

Lemma prune_diamonds_mut : forall t,
  prune_diamond_at t /\ prune_cross_at t /\ labels_diamond_at t.
Proof.
  apply (tsize_strong_ind (fun t =>
    prune_diamond_at t /\ prune_cross_at t /\ labels_diamond_at t)).
  intros t IH.
  assert (HP : prune_diamond_at t).
  { unfold prune_diamond_at. destruct t;
      try solve [pruning_plain IH].
    - (* MuS; only a pair payload permits an instance-pruning rule. *)
      destruct t; try solve [pruning_plain IH].
      intros u v H1 H2.
      destruct (prune_mus_pair_inv _ _ _ H1) as [B1 [L1 [-> [HB1 HL1]]]].
      destruct (prune_mus_pair_inv _ _ _ H2) as [B2 [L2 [-> [HB2 HL2]]]].
      destruct (proj1 (IH t1 ltac:(cbn; lia)) _ _ HB1 HB2)
        as [B3 [HB13 HB23]].
      destruct (proj2 (proj2 (IH t2 ltac:(cbn; lia))) t1 _ _ HL1 HL2)
        as [L3 [HL13 HL23]].
      exists (TMuS (TPair B3 L3)). split; apply pt_instance; try assumption.
      + eapply prune_labels_rebase; [exact HL13|].
        rewrite (prune_erase _ _ HB1). apply cjoin_refl.
      + eapply prune_labels_rebase; [exact HL23|].
        rewrite (prune_erase _ _ HB2). apply cjoin_refl.
    - (* Case branches. *)
      intros u v H1 H2. inversion H1; subst; clear H1.
      inversion H2; subst; clear H2. pruning_join_children IH.
      assert (HB : forall c b, In (c,b) bs ->
        prune_diamond_at c /\ prune_diamond_at b).
      { intros c b Hin. split.
        - apply (proj1 (IH c ltac:(eapply tsize_case_bs; exact Hin))).
        - apply (proj1 (IH b ltac:(eapply tsize_case_bs_body; exact Hin))). }
      destruct (prune_branches_diamond_from bs HB _ _ H7 H9)
        as [ws [HS1 HS2]].
      exists (TCase w0 w ws). split; constructor; eassumption. }
  assert (HC : prune_cross_at t).
  { unfold prune_cross_at. intros B u v HL HT.
    inversion HL; subst.
    - destruct (HP _ _ ltac:(eassumption) HT) as [w [Hw1 Hw2]].
      exists w. split; [exact Hw1|apply pl_stop; exact Hw2].
    - inversion HT; subst; clear HT.
      destruct (proj1 (IH A ltac:(cbn; lia)) _ _ H H5)
        as [Aw [HA1 HA2]].
      destruct (proj1 (IH c ltac:(cbn; lia)) _ _ H0 H7)
        as [cw [Hc1 Hc2]].
      destruct (proj1 (proj2 (IH L ltac:(cbn; lia))) B _ _ H1 H8)
        as [Lw [HL1 HL2]].
      exists (TLCons Aw cw Lw). split; [apply pt_lcons|apply pl_keep]; assumption.
    - inversion HT; subst; clear HT.
      destruct (proj1 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H7)
        as [Lw [HL1 HL2]].
      exists Lw. split; [exact HL1|]. apply pl_drop; [|exact HL2].
      eapply instance_dead_join; [|exact H].
      cbn. rewrite (prune_erase _ _ H6). apply cjoin_refl. }
  split; [exact HP|]. split; [exact HC|].
  unfold labels_diamond_at. intros B u v H1 H2.
  inversion H1; subst.
  - destruct (HC B _ _ H2 ltac:(eassumption)) as [w [Hv Hu]].
    exists w. split; [exact Hu|apply pl_stop; exact Hv].
  - inversion H2; subst.
    + destruct (HC B _ _ H1 ltac:(eassumption)) as [w [Hu Hv]].
      exists w. split; [apply pl_stop; exact Hu|exact Hv].
    + destruct (proj1 (IH A ltac:(cbn; lia)) _ _ H H8)
        as [Aw [HA1 HA2]].
      destruct (proj1 (IH c ltac:(cbn; lia)) _ _ H0 H10)
        as [cw [Hc1 Hc2]].
      destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H3 H11)
        as [Lw [HL1 HL2]].
      exists (TLCons Aw cw Lw). split; apply pl_keep; assumption.
    + destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H3 H10)
        as [Lw [HL1 HL2]].
      exists Lw. split; [|exact HL2]. apply pl_drop; [|exact HL1].
      eapply instance_dead_join; [|exact H9].
      cbn. rewrite (prune_erase _ _ H0). apply cjoin_refl.
  - inversion H2; subst.
    + destruct (HC B _ _ H1 ltac:(eassumption)) as [w [Hu Hv]].
      exists w. split; [apply pl_stop; exact Hu|exact Hv].
    + destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H10)
        as [Lw [HL1 HL2]].
      exists Lw. split; [exact HL1|]. apply pl_drop; [|exact HL2].
      eapply instance_dead_join; [|exact H].
      cbn. rewrite (prune_erase _ _ H9). apply cjoin_refl.
    + exact (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H9).
Qed.

Theorem prune_term_diamond : diamond prune_term.
Proof. intros t u v H1 H2. exact (proj1 (prune_diamonds_mut t) u v H1 H2). Qed.
Theorem prune_term_confluent : confluent prune_term.
Proof. apply diamond_rtc_confluent, prune_term_diamond. Qed.

Print Assumptions prune_term_diamond.
Print Assumptions prune_term_confluent.
