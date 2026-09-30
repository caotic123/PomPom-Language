(* Full normalization follows from computation normalization for typed terms.
   Computation normalization for all well-typed terms is still unproved. *)
From Stdlib Require Import Arith Lia Wf_nat.
Require Export nameless.DBActivePostponement.

Lemma epstep_size : forall t u, epstep t u ->
  tsize u <= tsize t /\ (tsize u = tsize t -> u = t).
Proof.
  intros t u H; induction H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [tsize]; try rewrite tsize_lift.
  all: split; [lia | let Eqsize := fresh "Eqsize" in intro Eqsize;
    try reflexivity; try lia; f_equal;
    match goal with H : _ -> ?u = ?t |- ?u = ?t => apply H; lia end].
Qed.

Definition eta_step t u := epstep t u /\ tsize u < tsize t.

Theorem eta_normalization : forall t,
  Acc (fun u v => eta_step v u) t.
Proof.
  apply (well_founded_lt_compat term tsize).
  intros x y [_ H]; exact H.
Qed.

Lemma reduction_computation_eta : forall t u, reduction t u ->
  computation t u \/ eta_step t u.
Proof.
  intros t u H; induction H.
  all: try solve [left; now apply cmp_root].
  all: try solve [right; split; [apply eps_eta, epstep_refl|];
    cbn [tsize]; rewrite tsize_lift; lia].
  all: destruct IHreduction as [HC|[HE HS]].
  all: try solve [left; constructor; exact HC].
  all: right; split;
    [solve [constructor; auto using epstep_refl] | cbn [tsize]; lia].
Qed.

(* A phase performs finitely many eta contractions followed by one
   computation. No termination premise is built into either relation. *)
Definition computation_phase t u :=
  exists v, rtc eta_step t v /\ computation v u.

Theorem normalization_from_phases : forall t,
  Acc (fun u v => computation_phase v u) t ->
  Acc (fun u v => reduction v u) t.
Proof.
  intros t H; induction H as [t Hacc IH].
  assert (Heta : forall u, rtc eta_step t u ->
    Acc (fun v w => reduction w v) u).
  { apply (tsize_strong_ind (fun u => rtc eta_step t u ->
      Acc (fun v w => reduction w v) u)).
    intros u IHu Htu. constructor; intros v Huv.
    destruct (reduction_computation_eta _ _ Huv) as [HC|[HE HS]].
    - apply IH. exists u; auto.
    - apply IHu; [exact HS|].
      eapply rtc_trans; [exact Htu|apply rtc_one; split; assumption]. }
  apply Heta, rtc_refl.
Qed.

Print Assumptions eta_normalization.
Print Assumptions normalization_from_phases.

Lemma accessible_computations : forall t,
  Acc (fun u v => computation v u) t ->
  forall u, rtc computation t u -> Acc (fun u v => computation v u) u.
Proof.
  intros t H u HR; induction HR; [exact H|].
  apply IHHR. exact (Acc_inv H H0).
Qed.
Lemma accessible_positive_computations : forall t,
  Acc (fun u v => computation v u) t ->
  Acc (fun u v => positive_computations v u) t.
Proof.
  intros t H; induction H as [t Hacc IH]. constructor.
  intros u [v [Htv Hvu]].
  pose proof (IH v Htv) as Hv.
  clear IH Hacc Htv t. induction Hvu; [exact Hv|].
  apply IHHvu. apply (Acc_inv Hv).
  exists y; split; [exact H|constructor].
Qed.
Lemma accessible_apstep : forall t,
  Acc (fun u v => computation v u) t ->
  Acc (fun u v => apstep true v u) t.
Proof.
  intros t H. pose proof (accessible_positive_computations _ H) as HP.
  clear H; induction HP as [t HP IH]. constructor; intros u HU.
  apply IH. exact (apstep_positive _ _ _ HU eq_refl).
Qed.

Theorem normalization_from_computation : forall Gamma t T,
  typing Gamma t T -> Acc (fun u v => computation v u) t ->
  Acc (fun u v => reduction v u) t.
Proof.
  intros Gamma t T HT HC.
  pose proof (accessible_apstep _ HC) as HA; clear HC.
  assert (HS : forall s, Acc (fun u v => apstep true v u) s ->
    typing Gamma s T -> forall u, rtc epstep s u ->
    Acc (fun v w => reduction w v) u).
  { intros s H; induction H as [s Hacc IH]; intro Hs.
    apply (tsize_strong_ind (fun u => rtc epstep s u ->
      Acc (fun v w => reduction w v) u)).
    intros u IHu Hsu. constructor; intros v Huv.
    destruct (reduction_computation_eta _ _ Huv) as [HC|[HE Hsize]].
    - destruct (safe_etas_apstep_postpone _ _ Hsu (typing_eta_safe _ _ _ Hs)
        true _ (computation_apstep _ _ HC)) as [w [HP HW]].
      apply (IH w HP).
      + eapply pstep_preservation; [eapply apstep_pstep; exact HP|exact Hs].
      + exact HW.
    - apply IHu; [exact Hsize|].
      eapply rtc_trans; [exact Hsu|apply rtc_one; exact HE]. }
  exact (HS t HA HT t rtc_refl).
Qed.

Print Assumptions normalization_from_computation.
