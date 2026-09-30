Require Import Progress SignatureConversion _parent_instance_pruning _parent_pruning_lower _luna_instance_step_prune _parent_step_prune.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_cjoin.

Lemma pruning_fstep_pair_inv : forall B L u, fstep (TPair B L) u ->
  (exists B', u = TPair B' L /\ fstep B B') \/
  (exists L', u = TPair B L' /\ fstep L L').
Proof.
  intros B L u H. inversion H; subst;
    try solve [match goal with Hs : step (TPair _ _) _ |- _ =>
      inversion Hs; subst; eauto using fstep end]; eauto.
Qed.

Definition prune_core_at t := forall u, fstep t u -> forall v,
  prune_term t v -> exists w, rtc fstep v w /\ prune_term u w.
Definition labels_core_at t := forall B u, fstep t u -> forall v,
  prune_labels B t v -> exists w, rtc fstep v w /\ prune_labels B u w.

Ltac pruning_rtc_context :=
  match goal with
  | HR : rtc fstep ?a ?b |- exists w, rtc fstep ?v w /\ _ =>
    let p := eval pattern a in v in
    lazymatch p with
    | ?F _ => exists (F b); split;
      [apply (rtc_map_parent fstep fstep F); [intros; constructor; assumption|exact HR]
      |constructor; eassumption]
    end
  end.

Ltac pruning_fstep_plain IH Hpr :=
  inversion Hpr; subst; clear Hpr;
  match goal with
  | Hf : fstep ?x ?y, HP : prune_term ?x ?v |- _ =>
    destruct (proj1 (IH x ltac:(cbn; lia)) y Hf v HP) as [w [HR HPw]];
    pruning_rtc_context
  end.

Section WithWeakSimulation.
Variable Hweak : forall t u, step t u -> forall v,
  prune_term t v -> exists w, step v w /\ prune_term u w.

Lemma pruning_core_commute_mut : forall t,
  prune_core_at t /\ labels_core_at t.
Proof.
  apply (tsize_strong_ind (fun t => prune_core_at t /\ labels_core_at t)).
  intros t IH.
  assert (HP : prune_core_at t).
  { unfold prune_core_at. intros u Hf v Hpr. destruct Hf;
      try solve [pruning_fstep_plain IH Hpr].
    - destruct (Hweak _ _ H v Hpr) as [w [Hw HPw]].
      exists w. split; [apply rtc_one, fs_step; exact Hw|exact HPw].
    - inversion Hpr; subst; clear Hpr.
      match goal with HH : prune_term (TApp _ _) _ |- _ => inversion HH; subst; clear HH end.
      match goal with HH : prune_term (TVar 0) _ |- _ => inversion HH; subst; clear HH end.
      match goal with HH : prune_term (lift 1 0 ?f) ?g |- _ =>
        destruct (prune_lift1_descent f g HH) as [g0 [-> Hg0]];
        exists g0; split; [apply rtc_one, fs_eta|exact Hg0]
      end.
    - inversion Hpr; subst; clear Hpr.
      + match goal with Hq : prune_term ?S ?V |- _ =>
          destruct (proj1 (IH S ltac:(cbn; lia)) _ Hf V Hq)
            as [w [HR HPw]];
          exists (TMuS w); split;
          [eapply (rtc_map_parent fstep fstep TMuS); [intros; apply fs_mus; eassumption|exact HR]
          |apply pt_mus; exact HPw]
        end.
      + destruct (pruning_fstep_pair_inv B L S' Hf)
          as [[Bnew [-> HB]]|[Lnew [-> HL]]].
        * destruct (proj1 (IH B ltac:(cbn; lia)) _ HB B' H0)
            as [Bw [HR HPw]].
          exists (TMuS (TPair Bw L')). split.
          -- eapply (rtc_map_parent fstep fstep (fun z => TMuS (TPair z L')));
               [intros; apply fs_mus, fs_pair1; eassumption|exact HR].
          -- apply pt_instance; [exact HPw|].
             eapply prune_labels_rebase; [exact H1|].
             apply conv_phi_cjoin, fstep_conv; exact HB.
        * destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL L' H1)
            as [Lw [HR HPw]].
          exists (TMuS (TPair B' Lw)). split.
          -- eapply (rtc_map_parent fstep fstep (fun z => TMuS (TPair B' z)));
               [intros; apply fs_mus, fs_pair2; eassumption|exact HR].
          -- apply pt_instance; assumption.
    - inversion Hpr; subst; clear Hpr.
      match goal with Hb : prune_branches (bs1 ++ (c,b)::bs2) ?out |- _ =>
        destruct (prune_branches_app_inv bs1 ((c,b)::bs2) out Hb)
          as [pre [suf [-> [Hpre Hsuf]]]];
        inversion Hsuf; subst; clear Hsuf
      end.
      assert (Hszc : tsize c < tsize (TCase M Q (bs1 ++ (c,b)::bs2))).
      { eapply tsize_case_bs. apply in_or_app. right; left; reflexivity. }
      destruct (proj1 (IH c Hszc) _ Hf _ H3) as [cw [HR HPw]].
      exists (TCase M' Q' (pre ++ (cw,b')::bs')). split.
      + eapply (rtc_map_parent fstep fstep
          (fun z => TCase M' Q' (pre ++ (z,b')::bs')));
          [intros; apply fs_case_br1; eassumption|exact HR].
      + apply pt_case; [exact H2|exact H4|].
        apply prune_branches_app; [exact Hpre|]. constructor; assumption.
    - inversion Hpr; subst; clear Hpr.
      destruct (prune_branches_app_inv bs1 ((c,b)::bs2) bs' H5)
        as [pre [suf [-> [Hpre Hsuf]]]].
      inversion Hsuf as [|cx cy bx bv ts us Hpc Hpb Htail]; subst; clear Hsuf.
      assert (Hszb : tsize b < tsize (TCase M Q (bs1 ++ (c,b)::bs2))).
      { eapply tsize_case_bs_body. apply in_or_app. right; left; reflexivity. }
      destruct (proj1 (IH b Hszb) _ Hf _ Hpb) as [bw [HR HPw]].
      exists (TCase M' Q' (pre ++ (cy,bw)::us)). split.
      + eapply (rtc_map_parent fstep fstep
          (fun z => TCase M' Q' (pre ++ (cy,z)::us)));
          [intros; apply fs_case_br2; eassumption|exact HR].
      + apply pt_case; [exact H2|exact H4|].
        apply prune_branches_app; [exact Hpre|]. constructor; assumption. }
  split; [exact HP|].
  unfold labels_core_at. intros B u Hf v Hpl. inversion Hpl; subst.
  - destruct (HP _ Hf _ ltac:(eassumption)) as [w [HR HPw]].
    exists w. split; [exact HR|apply pl_stop; exact HPw].
  - destruct (fstep_lcons_inv A c L u Hf)
      as [[An [-> HA]]|[[cn [-> HC]]|[Ln [-> HL]]]].
    + destruct (proj1 (IH A ltac:(cbn; lia)) _ HA _ H) as [w [HR Hw]].
      exists (TLCons w c' L'). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons z c' L'));
          [intros; apply fs_lcons1; eassumption|exact HR].
      * apply pl_keep; assumption.
    + destruct (proj1 (IH c ltac:(cbn; lia)) _ HC _ H0) as [w [HR Hw]].
      exists (TLCons A' w L'). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons A' z L'));
          [intros; apply fs_lcons2; eassumption|exact HR].
      * apply pl_keep; assumption.
    + destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL _ H1) as [w [HR Hw]].
      exists (TLCons A' c' w). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons A' c' z));
          [intros; apply fs_lcons3; eassumption|exact HR].
      * apply pl_keep; assumption.
  - destruct (fstep_lcons_inv A c L u Hf)
      as [[An [-> HA]]|[[cn [-> HC]]|[Ln [-> HL]]]].
    + exists v. split; [apply rtc_refl|apply pl_drop; assumption].
    + exists v. split; [apply rtc_refl|]. apply pl_drop; [|assumption].
      eapply instance_dead_join; [|exact H].
      apply conv_phi_cjoin, cv_app; [apply cv_refl|apply fstep_conv; exact HC].
    + destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL _ H0) as [w [HR Hw]].
      exists w. split; [exact HR|apply pl_drop; assumption].
Qed.
End WithWeakSimulation.

Theorem fstep_prune_commute : forall t u v,
  fstep t u -> prune_term t v ->
  exists w, prune_term u w /\ rtc fstep v w.
Proof.
  intros t u v Hf Hp.
  destruct (proj1 (pruning_core_commute_mut step_prune_sim_parent t) u Hf v Hp)
    as [w [HR HP]]. exists w; auto.
Qed.
Print Assumptions fstep_prune_commute.
