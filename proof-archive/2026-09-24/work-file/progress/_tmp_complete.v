Require Import Progress.
From Stdlib Require Import List.
Import ListNotations.

#[local] Hint Constructors pstep pbranches : pdev.
#[local] Hint Resolve pstep_lift pstep_subst : pdev.

Lemma try_complete :
  (forall t u (H : pstep t u), pstep u (pdev t)) /\
  (forall bs bs' (H : pbranches bs bs'),
      pbranches bs' (map (fun '(c,b) => (pdev c, pdev b)) bs)).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl, pstep_lift, pstep_subst].
  - destruct f; cbn;
      try solve [eapply ps_app; eauto].
    inversion p; subst. inversion H; subst.
    eapply ps_beta; eauto.
  - destruct p; cbn;
      try solve [eapply ps_fst; eauto].
    match goal with Hr : pstep (TypeRules.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_fst_pair; eauto.
  - destruct p; cbn;
      try solve [eapply ps_snd; eauto].
    match goal with Hr : pstep (TypeRules.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_snd_pair; eauto.
  - destruct E; cbn;
      try solve [eapply ps_epi; eauto].
    + match goal with Hr : pstep TypeRules.TNilE _ |- _ =>
        inversion Hr; clear Hr; subst
      end.
      eapply ps_epi_nil; eauto.
    + match goal with Hr : pstep (TypeRules.TConsE _ _) _ |- _ =>
        inversion Hr; clear Hr; subst
      end.
      cbn in H. inversion H; subst.
      eapply ps_epi_cons; eauto using pstep_lift.
  - destruct E; cbn;
      try solve [eapply ps_switch; eauto].
    destruct p; cbn;
      try solve [eapply ps_switch; eauto].
    destruct e; cbn;
      try solve [eapply ps_switch; eauto].
    + inversion p0; subst. inversion p2; subst. inversion p3; subst.
      cbn in H, H1, H2.
      inversion H; subst. inversion H1; subst. inversion H2; subst.
      eapply ps_switch_zero; eauto.
    + inversion p0; subst. inversion p2; subst. inversion p3; subst.
      cbn in H, H1, H2.
      inversion H; subst. inversion H1; subst. inversion H2; subst.
      eapply ps_switch_succ; eauto using pstep_lift.
  - destruct D; cbn;
      try solve [eapply ps_interp; eauto].
    all: inversion p; subst; cbn in H; inversion H; subst;
      eauto using pstep, pstep_lift.
  - destruct x; cbn;
      try solve [eapply ps_ind; eauto].
    inversion p3; subst. cbn in H3. inversion H3; subst.
    eapply ps_ind_red; eauto using pstep_lift.
  - destruct D; cbn;
      try solve [eapply ps_iall; eauto].
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_iall_var; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_one; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_prod; eauto using pstep_lift.
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_iall_pi; eauto using pstep_lift.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_sig; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_choice; eauto.
  - destruct D; cbn;
      try solve [eapply ps_hyps; eauto].
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_hyps_var; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_one; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_prod; eauto.
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_hyps_pi; eauto using pstep_lift.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_sig; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_choice; eauto.
  - eapply pstep_case_complete_aux; eauto.
  - exact (pstep_subst b' (pdev b) H a' (pdev a) 0 H0).
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - match goal with
    | Hnth : nth_error ?bs0 ?kk = Some (?cc,?bb),
      Hcpos : TypeRules.enum_pos ?cc ?nn,
      Hapos : TypeRules.enum_pos ?aa ?nn |- _ =>
        cbn;
        rewrite (enum_index_complete aa nn Hapos);
        erewrite (first_branch_selected_pdev_body nn bs0 kk cc bb)
          by eauto;
        eapply pstep_subst; eauto
    end.
Qed.
