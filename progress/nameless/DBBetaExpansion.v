(* Fixed-argument beta expansion for every full-reduction candidate. *)
Require Export nameless.DBSemanticTypes.
Import Full.

Theorem candidate_beta_expansion : forall R, candidate R -> forall b a,
  full_SN b -> full_SN a -> R (subst a 0 b) -> R (TApp (TLam b) a).
Proof.
  intros R CR b a HB; revert a.
  induction HB as [b HB IHb]; intros a HA.
  induction HA as [a HA IHa]; intro Hbody.
  apply (candidate_neutral CR); [exact I|].
  intros u HU; inversion HU; subst.
  - cbn [root_step] in H; inversion H; subst; exact Hbody.
  - match goal with HR : reduction (TLam b) ?g |- _ =>
      inversion HR; subst; [discriminate| |] end.
    + now rewrite subst_eta_app in Hbody.
    + eapply IHb; [eassumption|constructor; exact HA|].
      eapply candidate_reducts; [exact CR|apply reductions_substitute; eassumption|exact Hbody].
  - eapply IHa; [eassumption|].
    eapply candidate_reducts; [exact CR|apply reduction_subst_argument; eassumption|exact Hbody].
Qed.

Print Assumptions candidate_beta_expansion.

Theorem dependent_double_lambda_computable : forall A B C,
  candidate A -> (forall i, A i -> candidate (B i)) ->
  (forall i x, A i -> B i x -> candidate (C i x)) ->
  (forall i, A i -> stable_family (B i) (C i)) ->
  forall body,
  (forall i x, A i -> B i x -> C i x (subst x 0 (subst i 1 body))) ->
  full_SN (TLam (TLam body)) /\
  forall i x, A i -> B i x -> C i x (TApp (TApp (TLam (TLam body)) i) x).
Proof.
  intros A B C CA CB CC CS body HF.
  assert (HI : forall i, A i -> dependent_function (B i) (C i) (TLam (subst i 1 body))).
  { intros i Hi; apply dependent_lambda_computable;
      [exact (CB i Hi)|intros x Hx; exact (CC i x Hi Hx)|exact (CS i Hi)|].
    intros x Hx; exact (HF i x Hi Hx). }
  pose proof (candidate_variable A CA 0) as Hvar.
  assert (HS : full_SN (TLam body)).
  { exact (full_SN_subst_reflection (TLam body) (TVar 0) 0 (proj1 (HI _ Hvar))). }
  split; [now apply normalizing_lambda|].
  intros i x Hi Hx.
  assert (HA : dependent_function (B i) (C i) (TApp (TLam (TLam body)) i)).
  { apply candidate_beta_expansion;
      [apply dependent_function_candidate; [exact (CB i Hi)|intros y Hy; exact (CC i y Hi Hy)|exact (CS i Hi)]
      |exact HS|exact (candidate_normalizing CA Hi)|exact (HI i Hi)]. }
  exact (proj2 HA x Hx).
Qed.

Print Assumptions dependent_double_lambda_computable.
