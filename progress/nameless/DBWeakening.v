From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBTyping.
Import ListNotations.

Lemma universe_le_lift : forall A B, universe_le A B -> forall d c,
  universe_le (lift d c A) (lift d c B).
Proof. intros A B H; induction H; intros; cbn [lift]; auto using universe_le. Qed.

Lemma reduction_conversion : forall t u, reduction t u -> conv t u.
Proof.
  intros t u H; induction H.
  { apply cv_step, st_root; assumption. }
  { apply cv_eta. }
  all: apply cv_compatible; constructor; auto using cv_refl.
Qed.
Lemma reductions_conversion : forall t u, rtc reduction t u -> conv t u.
Proof. intros t u H; induction H; eauto using cv_refl, cv_trans, reduction_conversion. Qed.
Lemma conversion_lift : forall t u, conv t u -> forall d c, conv (lift d c t) (lift d c u).
Proof.
  fix IH 3; intros t u H d c; destruct H.
  - apply reductions_conversion, pstep_reductions, pstep_lift, step_pstep; assumption.
  - apply cv_refl.
  - apply cv_sym, IH; assumption.
  - eapply cv_trans; apply IH; eassumption.
  - cbn [lift]. rewrite lift_lift_one_zero. apply cv_eta.
  - destruct H; cbn [lift]; try apply cv_refl; apply cv_compatible; constructor; auto using IH.
Qed.

Lemma typing_context : forall Gamma t A, typing Gamma t A -> wf Gamma.
Proof. intros Gamma t A H; induction H; assumption. Qed.
Lemma typing_pi_domain : forall Gamma t T, typing Gamma t T -> forall A B,
  t = TPi A B -> exists k, typing Gamma A (TSort k).
Proof. intros Gamma t T H; induction H; intros AA BB Heq; try discriminate; eauto.
  inversion Heq; subst; eauto. Qed.

Lemma lift_arrow : forall A B d c, lift d c (arrow A B) = arrow (lift d c A) (lift d c B).
Proof. intros; unfold arrow; cbn [lift]; now rewrite lift_lift_one_zero. Qed.
Lemma lift_Def : forall IT d c, lift d c (Def IT) = Def (lift d c IT).
Proof. intros; unfold Def; cbn [lift]; now rewrite lift_lift_one_zero. Qed.
Lemma lift_Family : forall IT d c, lift d c (Family IT) = Family (lift d c IT).
Proof. reflexivity. Qed.
Lemma lift_total : forall IT X d c, lift d c (total IT X) = total (lift d c IT) (lift d c X).
Proof. intros; unfold total; cbn [lift]; now rewrite lift_lift_one_zero. Qed.
Lemma lift_motive : forall IT X d c, lift d c (motive IT X) = motive (lift d c IT) (lift d c X).
Proof. intros; unfold motive; cbn [lift]; now rewrite lift_total. Qed.
Lemma lift_recursive_method : forall IT X P d c,
  lift d c (recursive_method IT X P) = recursive_method (lift d c IT) (lift d c X) (lift d c P).
Proof. intros; unfold recursive_method; cbn [lift]; now rewrite lift_lift_one_zero, lift_lift_two_zero. Qed.
Lemma lift_close_case_method : forall IT F G i Q d c,
  lift d c (close_case_method IT F G i Q) =
    close_case_method (lift d c IT) (lift d c F) (lift d c G) (lift d c i) (lift d c Q).
Proof. intros; unfold close_case_method, payload, carrier; cbn [lift]; now rewrite lift_lift_one_zero. Qed.
Lemma lift_close_motive : forall IT G d c,
  lift d c (close_motive IT G) = close_motive (lift d c IT) (lift d c G).
Proof.
  intros; unfold close_motive, CloseAt; cbn [lift].
  now rewrite lift_Def, lift_lift_one_zero, !lift_lift_two_zero.
Qed.
Lemma lift_diagonal_motive : forall G P d c,
  lift d c (diagonal_motive G P) = diagonal_motive (lift d c G) (lift d c P).
Proof. intros; unfold diagonal_motive; cbn [lift]; now rewrite !lift_lift_one_zero. Qed.
Lemma lift_lift_three_zero : forall t d c,
  lift d (S (S (S c))) (lift 3 0 t) = lift 3 0 (lift d c t).
Proof. intros; exact (lift_lift_zero_comm t d 3 c). Qed.
Lemma lift_lift_four_zero : forall t d c,
  lift d (S (S (S (S c)))) (lift 4 0 t) = lift 4 0 (lift d c t).
Proof. intros; exact (lift_lift_zero_comm t d 4 c). Qed.
Lemma lift_close_ind_method : forall IT G P d c,
  lift d c (close_ind_method IT G P) = close_ind_method (lift d c IT) (lift d c G) (lift d c P).
Proof.
  intros; unfold close_ind_method, payload, carrier; cbn [lift].
  rewrite lift_Def, lift_lift_one_zero, !lift_lift_two_zero, lift_diagonal_motive.
  rewrite !lift_lift_three_zero, lift_lift_four_zero. reflexivity.
Qed.
Lemma lift_mu_ind_method : forall IT D P d c,
  lift d c (mu_ind_method IT D P) = mu_ind_method (lift d c IT) (lift d c D) (lift d c P).
Proof.
  intros; unfold mu_ind_method; cbn [lift].
  rewrite !lift_lift_one_zero, !lift_lift_two_zero.
  now rewrite lift_lift_three_zero.
Qed.

Definition shift_index c n := if Nat.ltb n c then n else S n.
Definition environment_lift c (Gamma Delta : ctx) := forall n A,
  nth_error Gamma n = Some A -> exists B,
  nth_error Delta (shift_index c n) = Some B /\
  lift 1 c (lift (S n) 0 A) = lift (S (shift_index c n)) 0 B.

Lemma shift_index_succ : forall c n, shift_index (S c) (S n) = S (shift_index c n).
Proof. intros; unfold shift_index.
  change ((if Nat.ltb n c then S n else S (S n)) = S (if Nat.ltb n c then n else S n)).
  now destruct (Nat.ltb n c). Qed.
Lemma environment_lift_cons : forall c Gamma Delta A,
  environment_lift c Gamma Delta -> environment_lift (S c) (A::Gamma) ((lift 1 c A)::Delta).
Proof.
  intros c Gamma Delta A Henv [|n] B Hn; cbn [nth_error] in Hn.
  - inversion Hn; subst. exists (lift 1 c B); split; [reflexivity|apply lift_lift_one_zero].
  - destruct (Henv _ _ Hn) as [C [HC Heq]]. exists C.
    rewrite shift_index_succ; split; [exact HC|].
    replace (lift (S (S n)) 0 B) with (lift 1 0 (lift (S n) 0 B))
      by (apply lift_fuse_zero;lia).
    rewrite lift_lift_one_zero, Heq, lift_fuse_zero by lia. reflexivity.
Qed.

Local Ltac lift_macros := repeat first
  [rewrite lift_arrow in * | rewrite lift_Def in * | rewrite lift_Family in * |
   rewrite lift_motive in * | rewrite lift_recursive_method in * |
   rewrite lift_close_case_method in * | rewrite lift_close_motive in * |
   rewrite lift_mu_ind_method in * | rewrite lift_close_ind_method in *].

Theorem typing_lift : forall Gamma t A, typing Gamma t A ->
  forall c Delta, wf Delta -> environment_lift c Gamma Delta ->
  typing Delta (lift 1 c t) (lift 1 c A).
Proof.
  intros Gamma t A H; induction H; intros c Delta Hctx Henv.
  all: repeat match goal with
    | IH : forall (n : nat) (Theta : ctx), wf Theta -> environment_lift n ?G Theta -> _,
      HE : environment_lift ?c ?G ?Delta, HW : wf ?Delta |- _ => specialize (IH c Delta HW HE)
    end.
  all: lift_macros; cbn [lift MuAt CloseAt payload carrier] in *.
  all: try solve [econstructor; eauto using conversion_lift, universe_le_lift].
  - destruct (Henv _ _ H0) as [B [HB Heq]]. rewrite Heq in IHtyping. rewrite Heq.
    unfold shift_index in *; destruct (Nat.ltb n c); eapply ty_var; eauto.
  - eapply ty_pi; [eapply IHtyping1; eassumption|].
    eapply IHtyping2; [eapply wf_cons;[exact Hctx|eapply IHtyping1;eassumption]|now apply environment_lift_cons].
  - eapply ty_sigma; [eapply IHtyping1; eassumption|].
    eapply IHtyping2; [eapply wf_cons;[exact Hctx|eapply IHtyping1;eassumption]|now apply environment_lift_cons].
  - assert (HPi : typing Delta (TPi (lift 1 c A) (lift 1 (S c) B)) (TSort k)) by (eapply IHtyping1; eassumption).
    destruct (typing_pi_domain _ _ _ HPi _ _ eq_refl) as [j HA].
    eapply ty_lam; [exact HPi|]. eapply IHtyping2;
      [eapply wf_cons; eassumption|now apply environment_lift_cons].
  - rewrite lift_subst_zero_comm in IHtyping4. rewrite lift_subst_zero_comm. eapply ty_app; eauto.
  - eapply ty_pair; eauto. rewrite <- lift_subst_zero_comm. eauto.
  - rewrite lift_subst_zero_comm in IHtyping3. rewrite lift_subst_zero_comm. eapply ty_snd; eauto.
Qed.

Lemma environment_lift_head : forall Gamma A, environment_lift 0 Gamma (A::Gamma).
Proof.
  intros Gamma A n B Hn. exists B; split; [exact Hn|].
  unfold shift_index; cbn. now rewrite lift_fuse_zero by lia.
Qed.
Theorem weakening : forall Gamma t A B k,
  typing Gamma t A -> typing Gamma B (TSort k) -> typing (B::Gamma) (lift 1 0 t) (lift 1 0 A).
Proof.
  intros; eapply typing_lift; [eassumption|eapply wf_cons; eauto using typing_context|apply environment_lift_head].
Qed.

Lemma lookup_formation : forall Gamma, wf Gamma -> forall n A,
  nth_error Gamma n = Some A -> type_wf Gamma (lift (S n) 0 A).
Proof.
  intros Gamma Hwf; induction Hwf; intros [|n] B HB; cbn [nth_error] in HB; try discriminate.
  - inversion HB; subst. exists k. exact (weakening _ _ _ _ _ H H).
  - destruct (IHHwf _ _ HB) as [j Hform]. exists j.
    pose proof (weakening _ _ _ _ _ Hform H) as Hnew.
    rewrite lift_fuse_zero in Hnew by lia. exact Hnew.
Qed.
Theorem type_correctness : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Proof.
  intros Gamma t A H; induction H; unfold type_wf in *;
    eauto using ty_sort, typing_context.
Qed.
