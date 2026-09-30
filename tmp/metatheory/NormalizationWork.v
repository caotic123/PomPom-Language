(* Separate the finite eta work from computation in normalization proofs.
   The normalization theorem for all well-typed terms is still open. *)
From Stdlib Require Import Arith Lia Wf_nat.
Require Export nameless.DBParallelPreservation.

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
  { apply tsize_strong_ind. intros u IHu Htu. constructor; intros v Huv.
    destruct (reduction_computation_eta _ _ Huv) as [HC|[HE HS]].
    - apply IH. exists u; auto. Show.
    - apply IHu; [exact HS|].
      eapply rtc_trans; [exact Htu|apply rtc_one; split; assumption]. }
  apply Heta, rtc_refl.
Qed.

Print Assumptions eta_normalization.
Print Assumptions normalization_from_phases.
