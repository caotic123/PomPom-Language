From Stdlib Require Import Lia.
Require Import ActivePostponementWork ActiveParallelWork.

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
