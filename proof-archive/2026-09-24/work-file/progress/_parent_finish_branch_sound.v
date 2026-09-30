Require Import Progress _luna_finish_branch_erase _parent_finish_fconv_lift.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma branch_erase_enum_pos : forall c n, enum_pos c n ->
    enum_pos (branch_erase c) n.
Proof. intros c n H. induction H; cbn; constructor; assumption. Qed.

Lemma branch_erase_nth_error : forall bs k c b,
    nth_error bs k = Some (c,b) ->
    nth_error (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs) k =
      Some (branch_erase c, branch_erase b).
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH]; intros [|k] c b H;
    cbn in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma branch_erase_nth_inv : forall bs k c b,
    nth_error (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs) k =
      Some (c,b) ->
    exists c0 b0, nth_error bs k = Some (c0,b0) /\
      branch_erase c0 = c /\ branch_erase b0 = b.
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH];
    intros [|k] c b H; cbn in *; try discriminate.
  - inversion H; subst. eexists; eexists; repeat split; reflexivity.
  - destruct (IH k c b H) as [c1 [b1 [H1 [H2 H3]]]].
    exists c1, b1. repeat split; cbn; assumption.
Qed.

Lemma branch_erase_step : forall t u,
    step t u -> step (branch_erase t) (branch_erase u).
Proof.
  intros t u H; induction H.
  all: cbn; try constructor; eauto.
  - rewrite branch_erase_subst. apply st_beta.
  - repeat rewrite branch_erase_lift. apply st_epi_cons.
  - repeat rewrite branch_erase_lift. apply st_switch_succ.
  - repeat rewrite branch_erase_lift. apply st_interp_prod.
  - repeat rewrite branch_erase_lift. apply st_interp_pi.
  - repeat rewrite branch_erase_lift. apply st_interp_sig.
  - repeat rewrite branch_erase_lift. apply st_interp_choice.
  - repeat rewrite branch_erase_lift. apply st_iall_prod.
  - repeat rewrite branch_erase_lift. apply st_iall_pi.
  - repeat rewrite branch_erase_lift. apply st_hyps_pi.
  - repeat rewrite branch_erase_lift. apply st_ind.
  - rewrite branch_erase_subst.
    apply st_case with
      (a := branch_erase a) (xs := branch_erase xs) (Q := branch_erase Q)
      (bs := map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)
      (k := k) (c := branch_erase c) (b := branch_erase b) (n := n).
    + apply branch_erase_nth_error. exact H.
    + apply branch_erase_enum_pos. exact H0.
    + apply branch_erase_enum_pos. exact H1.
    + intros j cj bj Hj Hnth.
      destruct (branch_erase_nth_inv _ _ _ _ Hnth)
        as [cj0 [bj0 [Hsrc [Hc Hb]]]].
      destruct (H2 j cj0 bj0 Hj Hsrc) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite <- Hc. apply branch_erase_enum_pos. exact Hpos.
      * exact Hneq.
  - repeat rewrite map_app. cbn.
    apply st_case_lbl. exact IHstep.
Qed.

Lemma branch_erase_conv : forall t u, conv t u ->
    fconv (branch_erase t) (branch_erase u).
Proof.
  intros t u H. induction H; cbn; eauto using fconv, fstep, branch_erase_step.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (rewrite branch_erase_lift; apply fc_step, fs_eta).
  all: try (repeat rewrite map_app; cbn;
    eapply fconv_map2; eauto using fstep).
  - cbn [branches branch_erase] in IHconv1.
    repeat rewrite branch_erase_lift in IHconv1.
    eapply fconv_map; [intros; apply fs_mus; eassumption | exact IHconv1].
  - apply fc_refl.
  - apply (fconv_map TLam); [intros; apply fs_lam; assumption |].
    apply (fconv_map TFst); [intros; apply fs_fst; assumption |].
    apply (fconv_map (fun z => TApp z (TVar 0)));
      [intros; apply fs_app1; assumption |].
    apply fconv_lift_parent. exact IHconv.
  - eapply (fconv_map2
      (fun x y => TCase x y
        (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)));
      eauto using fstep.
  - repeat rewrite map_app. cbn.
    eapply (fconv_map2
      (fun x y => TCase (branch_erase M) (branch_erase Q)
        (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs1 ++
         (x,y) :: map (fun '(c,b) => (branch_erase c, branch_erase b)) bs2)));
      eauto using fstep.
Qed.


Print Assumptions branch_erase_conv.
