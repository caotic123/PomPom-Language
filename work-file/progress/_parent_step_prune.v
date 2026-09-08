Require Import Progress _parent_instance_pruning _luna_instance_step_prune.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.

Ltac pruning_inv_data :=
  repeat match goal with
  | H : prune_term (TLam _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TPair _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIn _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TConsE _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TNilE _ |- _ => inversion H; subst; clear H
  | H : prune_term TEZero _ |- _ => inversion H; subst; clear H
  | H : prune_term (TESucc _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIVar _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TI1 _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIProd _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIPi _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TISig _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIChoice _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TUnit _ |- _ => inversion H; subst; clear H
  end.

Ltac pruning_use_step_ih :=
  match goal with
  | IH : forall v, prune_term ?src v -> exists w, step v w /\ prune_term ?dst w,
    Hp : prune_term ?src ?v |- _ =>
    destruct (IH v Hp) as [w [Hw HPw]];
    eexists; split; [constructor; exact Hw|constructor; eassumption]
  end.

Lemma step_prune_sim_parent : forall t u, step t u -> forall v,
  prune_term t v -> exists w, step v w /\ prune_term u w.
Proof.
  intros t u H. induction H; intros v Hp; inversion Hp; subst; clear Hp;
    pruning_inv_data;
    try solve [pruning_use_step_ih];
    try solve [eexists; split; [constructor|
      eauto 10 using prune_term, prune_lift, prune_subst]].
  - eexists. split; [apply st_ind|].
    repeat first [assumption | apply prune_lift; assumption | constructor].
  - destruct (prune_branches_nth_fwd bs bs' k c b H9 H)
      as [c1 [b1 [Hnth [Hpc Hpb]]]].
    pose proof (prune_enum_pos c n c1 H0 Hpc) as Ec. subst c1.
    pose proof (prune_enum_pos a n a' H1 H6) as Ea. subst a'.
    exists (subst b' 0 b1). split.
    + eapply st_case with (k:=k) (c:=c) (b:=b1) (n:=n);
        [exact Hnth|exact H0|exact H1|].
      intros j cj bj Hj Hnj.
      destruct (prune_branches_nth_bwd bs bs' j cj bj H9 Hnj)
        as [cj0 [bj0 [Hnj0 [Hcj Hbj]]]].
      destruct (H2 j cj0 bj0 Hj Hnj0) as [nj [HPj Hneq]].
      exists nj. split; [|exact Hneq].
      rewrite (prune_enum_pos cj0 nj cj HPj Hcj). exact HPj.
    + apply prune_subst; assumption.
  - destruct (prune_branches_app_inv bs1 ((c,b)::bs2) bs' H6)
      as [pre [suf [-> [Hpre Hsuf]]]].
    inversion Hsuf as [|cx cy bx bv ts us Hpc Hpb Htail]; subst; clear Hsuf.
    destruct (IHstep cy Hpc) as [cw [Hcw Hpcw]].
    exists (TCase M' Q' (pre ++ (cw,bv)::us)). split.
    + apply st_case_lbl; exact Hcw.
    + apply pt_case; [exact H3|exact H5|].
      apply prune_branches_app; [exact Hpre|]. constructor; assumption.
Qed.
Print Assumptions step_prune_sim_parent.
