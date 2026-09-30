From Stdlib Require Import List Arith Bool Lia.
Require Export DBWeakWork.
Import ListNotations.

Lemma subst_arrow : forall A B u c, subst u c (arrow A B) = arrow (subst u c A) (subst u c B).
Proof. intros; unfold arrow; cbn [subst]; now rewrite subst_lift_one_zero. Qed.
Lemma subst_Def : forall IT u c, subst u c (Def IT) = Def (subst u c IT).
Proof. intros; unfold Def; cbn [subst]; now rewrite subst_lift_one_zero. Qed.
Lemma subst_Family : forall IT u c, subst u c (Family IT) = Family (subst u c IT).
Proof. reflexivity. Qed.
Lemma subst_total : forall IT X u c, subst u c (total IT X) = total (subst u c IT) (subst u c X).
Proof. intros; unfold total; cbn [subst]; now rewrite subst_lift_one_zero. Qed.
Lemma subst_motive : forall IT X u c, subst u c (motive IT X) = motive (subst u c IT) (subst u c X).
Proof. intros; unfold motive; cbn [subst]; now rewrite subst_total. Qed.
Lemma subst_recursive_method : forall IT X P u c,
  subst u c (recursive_method IT X P) = recursive_method (subst u c IT) (subst u c X) (subst u c P).
Proof. intros; unfold recursive_method; cbn [subst]; now rewrite subst_lift_one_zero, subst_lift_two_zero. Qed.
Lemma subst_close_case_method : forall IT F G i Q u c,
  subst u c (close_case_method IT F G i Q) =
    close_case_method (subst u c IT) (subst u c F) (subst u c G) (subst u c i) (subst u c Q).
Proof. intros; unfold close_case_method, payload, carrier; cbn [subst]; now rewrite subst_lift_one_zero. Qed.
Lemma subst_close_motive : forall IT G u c,
  subst u c (close_motive IT G) = close_motive (subst u c IT) (subst u c G).
Proof.
  intros; unfold close_motive, CloseAt; cbn [subst].
  now rewrite subst_Def, subst_lift_one_zero, !subst_lift_two_zero.
Qed.
Lemma subst_diagonal_motive : forall G P u c,
  subst u c (diagonal_motive G P) = diagonal_motive (subst u c G) (subst u c P).
Proof. intros; unfold diagonal_motive; cbn [subst]; now rewrite !subst_lift_one_zero. Qed.
Lemma subst_lift_three_zero : forall t u c,
  subst u (S (S (S c))) (lift 3 0 t) = lift 3 0 (subst u c t).
Proof. intros; exact (subst_lift_offset t u 3 0 c ltac:(lia)). Qed.
Lemma subst_lift_four_zero : forall t u c,
  subst u (S (S (S (S c)))) (lift 4 0 t) = lift 4 0 (subst u c t).
Proof. intros; exact (subst_lift_offset t u 4 0 c ltac:(lia)). Qed.
Lemma subst_close_ind_method : forall IT G P u c,
  subst u c (close_ind_method IT G P) = close_ind_method (subst u c IT) (subst u c G) (subst u c P).
Proof.
  intros; unfold close_ind_method, payload, carrier; cbn [subst].
  rewrite subst_Def, subst_lift_one_zero, !subst_lift_two_zero, subst_diagonal_motive.
  rewrite !subst_lift_three_zero, subst_lift_four_zero. reflexivity.
Qed.
Lemma subst_mu_ind_method : forall IT D P u c,
  subst u c (mu_ind_method IT D P) = mu_ind_method (subst u c IT) (subst u c D) (subst u c P).
Proof.
  intros; unfold mu_ind_method; cbn [subst].
  rewrite !subst_lift_one_zero, !subst_lift_two_zero.
  now rewrite subst_lift_three_zero.
Qed.

Lemma conversion_subst : forall t v, conv t v -> forall u c, conv (subst u c t) (subst u c v).
Proof.
  fix IH 3; intros t v H u c; destruct H.
  - apply reductions_conversion, pstep_reductions, pstep_subst; auto using step_pstep, pstep_refl.
  - apply cv_refl.
  - apply cv_sym, IH; assumption.
  - eapply cv_trans; apply IH; eassumption.
  - cbn [subst]. rewrite subst_lift_one_zero. apply cv_eta.
  - destruct H; cbn [subst]; try apply cv_refl; apply cv_compatible; constructor; auto using IH.
Qed.

Definition environment_subst c u (Gamma Delta : ctx) := forall n A,
  nth_error Gamma n = Some A ->
  typing Delta (subst u c (TVar n)) (subst u c (lift (S n) 0 A)).

Lemma environment_subst_cons : forall c u Gamma Delta A k,
  environment_subst c u Gamma Delta -> typing Delta (subst u c A) (TSort k) ->
  environment_subst (S c) u (A::Gamma) ((subst u c A)::Delta).
Proof.
  intros c u Gamma Delta A k Henv HA [|n] B HB; cbn [nth_error] in HB.
  - inversion HB; subst. rewrite subst_lift_one_zero.
    change (typing (subst u c B :: Delta) (TVar 0) (lift 1 0 (subst u c B))).
    apply ty_var; [eapply wf_cons; eauto using typing_context|reflexivity].
  - replace (TVar (S n)) with (lift 1 0 (TVar n)) by reflexivity.
    replace (lift (S (S n)) 0 B) with (lift 1 0 (lift (S n) 0 B)) by (apply lift_fuse_zero;lia).
    rewrite !subst_lift_one_zero. eapply weakening; [eapply Henv;exact HB|exact HA].
Qed.

Local Ltac subst_macros := repeat first
  [rewrite subst_arrow in * | rewrite subst_Def in * | rewrite subst_Family in * |
   rewrite subst_motive in * | rewrite subst_recursive_method in * |
   rewrite subst_close_case_method in * | rewrite subst_close_motive in * |
   rewrite subst_mu_ind_method in * | rewrite subst_close_ind_method in *].

Theorem typing_subst : forall Gamma t A, typing Gamma t A ->
  forall c u Delta, wf Delta -> environment_subst c u Gamma Delta ->
  typing Delta (subst u c t) (subst u c A).
Proof.
  intros Gamma t A H; induction H; intros c u Delta Hctx Henv.
  all: repeat match goal with
    | IH : forall (n : nat) (v : term) (Theta : ctx), wf Theta -> environment_subst n v ?G Theta -> _,
      HE : environment_subst ?c ?u ?G ?Delta, HW : wf ?Delta |- _ => specialize (IH c u Delta HW HE)
    end.
  all: subst_macros; cbn [subst MuAt CloseAt payload carrier] in *.
  all: try solve [econstructor; eauto using conversion_subst].
  - exact (Henv _ _ H0).
  - eapply ty_pi; [exact IHtyping1|].
    eapply IHtyping2; [eapply wf_cons; eassumption|eapply environment_subst_cons;eassumption].
  - eapply ty_sigma; [exact IHtyping1|].
    eapply IHtyping2; [eapply wf_cons; eassumption|eapply environment_subst_cons;eassumption].
  - destruct (typing_pi_domain _ _ _ IHtyping1 _ _ eq_refl) as [j HA].
    eapply ty_lam; [exact IHtyping1|]. eapply IHtyping2;
      [eapply wf_cons;eassumption|eapply environment_subst_cons;eassumption].
  - rewrite subst_subst_zero_comm. eapply ty_app; eauto.
  - eapply ty_pair; eauto. rewrite <- subst_subst_zero_comm. eauto.
  - rewrite subst_subst_zero_comm. eapply ty_snd; eauto.
Qed.

Lemma environment_subst_head : forall Gamma A u,
  typing Gamma u A -> environment_subst 0 u (A::Gamma) Gamma.
Proof.
  intros Gamma A u Hu [|n] B HB; cbn [nth_error] in HB.
  - inversion HB; subst. rewrite subst_lift_zero. cbn [subst]. now rewrite lift_zero_id.
  - replace (lift (S (S n)) 0 B) with (lift 1 0 (lift (S n) 0 B)) by (apply lift_fuse_zero;lia).
    rewrite subst_lift_zero. cbn [subst]. apply ty_var; eauto using typing_context.
Qed.
Theorem substitution : forall Gamma A t B u,
  typing (A::Gamma) t B -> typing Gamma u A -> typing Gamma (subst u 0 t) (subst u 0 B).
Proof.
  intros; eapply typing_subst; [eassumption|eauto using typing_context|now apply environment_subst_head].
Qed.
