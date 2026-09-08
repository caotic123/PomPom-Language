(* A minimal counterexample to core-before-eta sort standardization. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _glm_phi_erase_sort_pipeline _tmp_pstep_var_rigid
  _parent_inert_cstep_inv.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition std_pair_parent : term := TPair TUnit (TSort 0).
Definition std_lam_parent : term :=
  TLam (TApp std_pair_parent (TVar 0)).
Definition std_source_parent : term := TSnd std_lam_parent.

Lemma std_lam_eta_parent : epstep std_lam_parent std_pair_parent.
Proof.
  unfold std_lam_parent, std_pair_parent.
  change (epstep
    (TLam (TApp (lift 1 0 (TPair TUnit (TSort 0))) (TVar 0)))
    (TPair TUnit (TSort 0))).
  apply eps_eta, epstep_refl.
Qed.

Lemma std_source_eta_parent :
    epstep std_source_parent (TSnd std_pair_parent).
Proof.
  unfold std_source_parent. apply eps_snd, std_lam_eta_parent.
Qed.

Lemma std_snd_pair_core_parent :
    pstep (TSnd std_pair_parent) (TSort 0).
Proof.
  unfold std_pair_parent.
  exact (ps_snd_pair TUnit TUnit (TSort 0) (TSort 0)
    (pstep_refl TUnit) (pstep_refl (TSort 0))).
Qed.

Lemma std_source_reaches_sort_parent :
    rtc cstep std_source_parent (TSort 0).
Proof.
  eapply rtc_step.
  - apply epstep_cstep, std_source_eta_parent.
  - eapply rtc_step.
    + apply pstep_cstep, std_snd_pair_core_parent.
    + apply rtc_refl.
Qed.

Lemma pstep_unit_id_one_parent : forall u,
    pstep TUnit u -> u = TUnit.
Proof. intros u H; inversion H; reflexivity. Qed.

Lemma pstep_sort_id_one_parent : forall k u,
    pstep (TSort k) u -> u = TSort k.
Proof. intros k u H; inversion H; reflexivity. Qed.

Lemma pstep_std_pair_id_parent : forall u,
    pstep std_pair_parent u -> u = std_pair_parent.
Proof.
  intros u H.
  destruct (pstep_pair_inv_parent _ _ _ H) as [a' [b' [-> [Ha Hb]]]].
  rewrite (pstep_unit_id_one_parent _ Ha).
  rewrite (pstep_sort_id_one_parent _ _ Hb). reflexivity.
Qed.

Lemma pstep_std_body_id_parent : forall u,
    pstep (TApp std_pair_parent (TVar 0)) u ->
    u = TApp std_pair_parent (TVar 0).
Proof.
  intros u H. inversion H; subst.
  rewrite (pstep_std_pair_id_parent _ H2).
  rewrite (pstep_var_rigid _ _ H4). reflexivity.
Qed.

Lemma pstep_std_lam_id_parent : forall u,
    pstep std_lam_parent u -> u = std_lam_parent.
Proof.
  intros u H. unfold std_lam_parent in *.
  inversion H; subst.
  rewrite (pstep_std_body_id_parent _ H1). reflexivity.
Qed.

Lemma pstep_std_source_id_parent : forall u,
    pstep std_source_parent u -> u = std_source_parent.
Proof.
  intros u H. unfold std_source_parent in *.
  inversion H; subst.
  rewrite (pstep_std_lam_id_parent _ H1). reflexivity.
Qed.

Lemma rtc_pstep_std_source_id_parent : forall u,
    rtc pstep std_source_parent u -> u = std_source_parent.
Proof.
  intros u H. remember std_source_parent as x eqn:Hx.
  induction H; subst; [reflexivity |].
  pose proof (pstep_std_source_id_parent _ H) as Hy. subst y.
  apply IHrtc. reflexivity.
Qed.

Lemma epstep_snd_inv_parent : forall p u,
    epstep (TSnd p) u -> exists p', u = TSnd p' /\ epstep p p'.
Proof.
  intros p u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma rtc_epstep_snd_inv_parent : forall p u,
    rtc epstep (TSnd p) u -> exists p', u = TSnd p'.
Proof.
  intros p u H. remember (TSnd p) as x eqn:Hx. revert p Hx.
  induction H; intros p0 Heq; subst.
  - eauto.
  - destruct (epstep_snd_inv_parent _ _ H) as [p1 [-> _]].
    exact (IHrtc p1 eq_refl).
Qed.

Lemma no_epsteps_std_source_sort_parent : forall j,
    ~ rtc epstep std_source_parent (TSort j).
Proof.
  intros j H. unfold std_source_parent in H.
  destruct (rtc_epstep_snd_inv_parent _ _ H) as [p' Heq].
  discriminate Heq.
Qed.

Theorem no_core_eta_factor_std_source_parent :
    ~ exists y,
      rtc pstep std_source_parent y /\ rtc epstep y (TSort 0).
Proof.
  intros [y [Hcore Heta]].
  rewrite (rtc_pstep_std_source_id_parent _ Hcore) in Heta.
  exact (no_epsteps_std_source_sort_parent 0 Heta).
Qed.

Theorem cstep_sort_standardization_false_parent :
    ~ cstep_sort_standardization_glm.
Proof.
  intros Hstd.
  destruct (Hstd std_source_parent 0 std_source_reaches_sort_parent)
    as [y [Hcore Heta]].
  exact (no_core_eta_factor_std_source_parent
    (ex_intro _ y (conj Hcore Heta))).
Qed.

Print Assumptions std_source_reaches_sort_parent.
Print Assumptions no_core_eta_factor_std_source_parent.
Print Assumptions cstep_sort_standardization_false_parent.
