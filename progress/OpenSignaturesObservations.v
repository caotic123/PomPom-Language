(* Closing substitutions and contextual Boolean observations, independent of
   the public conjecture declarations. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesContextInclusion OpenSignaturesClosedSubstitution
  OpenSignaturesBeta OpenSignaturesNamedCanonical OpenSignaturesPreservation
  OpenSignaturesNormalization.
Import ListNotations.

(* Closing substitutions are necessary for a meaningful open-context
   coherence statement: an inconsistent context need not have a closing
   substitution, and evaluating its free bottom variable is not an
   observation of a closed program. Entries pair stable binding IDs with
   closed core terms. *)
Fixpoint instantiate (env : list (nat * term)) (t : term) : term :=
  match env with
  | [] => t
  | (x, u) :: env => instantiate env (subst u x t)
  end.
Inductive closing : ctx -> list (nat * term) -> Prop :=
| closing_nil : closing empty_ctx []
| closing_cons : forall Gamma env x A u,
    fresh_in Gamma x -> wf (extend Gamma x A) -> closing Gamma env ->
    typing empty_ctx u (instantiate env A) ->
    closing (extend Gamma x A) ((x, u) :: env).

Lemma closing_context : forall Gamma env, closing Gamma env -> wf Gamma.
Proof. intros Gamma env H; destruct H; auto using wf_nil. Qed.
Lemma closing_entries : forall Gamma env, closing Gamma env ->
  Forall (fun entry => (exists A, lookup Gamma (fst entry) = Some A) /\ free_vars (snd entry) = []) env.
Proof.
  intros Gamma env H; induction H; [constructor|].
  constructor.
  - cbn; split; [eexists;apply lookup_extend_same|eapply typed_closed;eassumption].
  - eapply Forall_impl; [|exact IHclosing]. intros [y t] [[B HB] Hclosed]; cbn in *.
    split; [exists B;eapply ctx_included_extend;eassumption|exact Hclosed].
Qed.
Definition closed_away (env : list (nat * term)) x :=
  Forall (fun entry => fst entry <> x /\ free_vars (snd entry) = []) env.
Lemma closing_away : forall Gamma env x,
  closing Gamma env -> fresh_in Gamma x -> closed_away env x.
Proof.
  intros Gamma env x H Hx. eapply Forall_impl; [|exact (closing_entries _ _ H)].
  intros [y t] [[A HA] HC]; cbn in *; split; [|exact HC].
  unfold fresh_in in Hx; intro E; subst; congruence.
Qed.

Lemma instantiate_alpha : forall env t u,
  alpha_equiv t u -> alpha_equiv (instantiate env t) (instantiate env u).
Proof.
  induction env as [|[x a] env IH]; intros t u H; cbn [instantiate]; [exact H|].
  apply IH, substitute_alpha; [exact H|intros; reflexivity].
Qed.
Lemma instantiate_lam : forall env x t, closed_away env x ->
  instantiate env (TLam x t) = TLam x (instantiate env t).
Proof.
  intros env x t H; revert t. induction H as [|[y u] env [Hne Hu] Henv IH]; intros t;
    cbn [instantiate]; [reflexivity|].
  rewrite subst_closed_lam by assumption. apply IH.
Qed.
Lemma instantiate_pi : forall env x A B, closed_away env x ->
  instantiate env (TPi x A B) = TPi x (instantiate env A) (instantiate env B).
Proof.
  intros env x A B H; revert A B. induction H as [|[y u] env [Hne Hu] Henv IH]; intros A B;
    cbn [instantiate]; [reflexivity|].
  rewrite subst_closed_pi by assumption. apply IH.
Qed.
Lemma instantiate_sort : forall env k, instantiate env (TSort k) = TSort k.
Proof. induction env as [|[x t] env IH]; intros; cbn [instantiate subst substitute]; auto. Qed.
Lemma instantiate_commute : forall env x u t,
  closed_away env x -> free_vars u = [] ->
  alpha_equiv (instantiate env (subst u x t)) (subst u x (instantiate env t)).
Proof.
  intros env x u t Henv Hu; revert t. induction Henv as [|[y v] env [Hne Hv] Henv IH]; intro t;
    cbn [instantiate]; [reflexivity|].
  etransitivity; [apply instantiate_alpha, subst_closed_commute; cbn in *; try assumption; congruence|apply IH].
Qed.

Section ClosingTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable regular : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Variable beta_preserve : forall Gamma x b a T,
  typing Gamma (TApp (TLam x b) a) T -> typing Gamma (subst a x b) T.

Theorem closing_from_rules : forall Gamma env t A,
  closing Gamma env -> typing Gamma t A ->
  typing empty_ctx (instantiate env t) (instantiate env A).
Proof.
  intros Gamma env t A Hclosing; revert t A.
  induction Hclosing as [|Gamma env x A u Hfresh Hwf Hclosing IH Hu]; intros t B Ht;
    cbn [instantiate]; [exact Ht|].
  pose proof (closing_context _ _ Hclosing) as Hctx.
  pose proof (closing_away _ _ _ Hclosing Hfresh) as Haway.
  pose proof (typed_closed _ _ Hu) as Hclosed.
  destruct (extension_domain_formation weaken regular beta_preserve _ _ _ Hctx Hfresh Hwf) as [j HA].
  destruct (regular _ _ _ Ht) as [k HB].
  assert (HPi : typing Gamma (TPi x A B) (TSort (Nat.max j k))) by (eapply ty_pi; eassumption).
  assert (Hlam : typing Gamma (TLam x t) (TPi x A B)) by (eapply ty_lam; eassumption).
  pose proof (IH _ _ HPi) as HPi'; pose proof (IH _ _ Hlam) as Hlam'.
  rewrite instantiate_pi, instantiate_sort in HPi' by exact Haway.
  rewrite instantiate_lam, instantiate_pi in Hlam' by exact Haway.
  pose proof (@ty_app empty_ctx x (instantiate env A) (instantiate env B)
    (TLam x (instantiate env t)) u _ HPi' Hlam' Hu) as Happ.
  assert (Hsub : typing empty_ctx (subst u x (instantiate env t)) (subst u x (instantiate env B)))
    by (eapply beta_preserve; exact Happ).
  destruct (regular _ _ _ Hsub) as [l Hform].
  pose proof (instantiate_commute env x u t Haway Hclosed) as Hterm.
  pose proof (instantiate_commute env x u B Haway Hclosed) as Htype.
  eapply ty_conv with (A:=subst u x (instantiate env B)).
  - eapply ty_alpha; [exact Hsub|now symmetry].
  - eapply ty_alpha; [exact Hform|now symmetry].
  - apply cv_alpha; now symmetry.
Qed.
End ClosingTyping.

Theorem named_closing_substitution : forall Gamma env t A,
  closing Gamma env -> typing Gamma t A ->
  typing empty_ctx (instantiate env t) (instantiate env A).
Proof. exact (closing_from_rules named_weakening named_type_correctness named_beta_preservation). Qed.

Lemma observation_next_step_sound : forall t u, next_step t = Some u -> step t u.
Proof.
  induction t; intros u H; cbn [next_step] in H;
    destruct (root_step _) eqn:Hr;
    try solve [inversion H; subst; now apply st_root].
  all: repeat match type of H with
    | context [match next_step ?t with _ => _ end] =>
        destruct (next_step t) eqn:?
    end; try discriminate; inversion H; subst; eauto using step.
Qed.
Lemma observation_run_sound : forall fuel t, eval t (run fuel t).
Proof.
  induction fuel; intro t; cbn [run]; [constructor|].
  destruct (next_step t) eqn:H; eauto using eval, observation_next_step_sound.
Qed.
Lemma observation_eval_preservation : forall Gamma t u A,
  typing Gamma t A -> eval t u -> typing Gamma u A.
Proof. intros Gamma t u A HT HE; revert HT; induction HE; eauto using named_preservation. Qed.
Lemma observation_termination : forall t A,
  typing empty_ctx t A -> exists v, eval t v /\ value v.
Proof.
  intros t A HT.
  destruct (accessible_run t (named_full_normalization _ _ _ HT)) as [fuel Hnone].
  exists (run fuel t); split; [apply observation_run_sound|].
  assert (Htyped : typing empty_ctx (run fuel t) A)
    by (eapply observation_eval_preservation; [exact HT|apply observation_run_sound]).
  assert (Hprogress : value (run fuel t) \/ exists u, step (run fuel t) u).
  { eapply progress_from_conversion; [intros; now apply raw_conversion_joinability|exact Htyped|reflexivity]. }
  destruct Hprogress as [HV|[u HU]]; [exact HV|].
  destruct (step_has_next _ _ HU) as [v HV]; congruence.
Qed.

Definition observation_type :=
  TEnumT (TConsE (TTag "true"%string)
    (TConsE (TTag "false"%string) TNilE)).
Definition observation (t : term) :=
  t = TEZero \/ t = TESucc TEZero.
Definition closed_observational_eq A t u :=
  typing empty_ctx t A /\ typing empty_ctx u A /\
  forall x context result,
    typing (extend empty_ctx x A) context observation_type -> observation result ->
    (eval (subst t x context) result <-> eval (subst u x context) result).
Definition observational_eq Gamma A t u :=
  typing Gamma t A /\ typing Gamma u A /\
  forall env, closing Gamma env ->
    closed_observational_eq (instantiate env A)
      (instantiate env t) (instantiate env u).

Lemma substitution_argument_conversion : forall b x t u,
  conv t u -> conv (subst t x b) (subst u x b).
Proof.
  intros b x t u H. eapply cv_trans with (u:=TApp (TLam x b) t).
  - apply cv_sym, cv_step, st_root; reflexivity.
  - eapply cv_trans with (u:=TApp (TLam x b) u).
    + apply cv_compatible, cp_TApp; auto using cv_refl.
    + apply cv_step, st_root;reflexivity.
Qed.
Lemma instantiate_conversion : forall env t u,
  conv t u -> conv (instantiate env t) (instantiate env u).
Proof.
  induction env as [|[x a] env IH]; intros t u H; cbn [instantiate]; [exact H|].
  now apply IH, conv_subst.
Qed.
Lemma instantiate_app : forall env f a,
  instantiate env (TApp f a) = TApp (instantiate env f) (instantiate env a).
Proof. induction env as [|[x u] env IH]; intros; cbn [instantiate subst substitute]; auto. Qed.
Lemma instantiate_close : forall env IT F G,
  instantiate env (TClose IT F G) = TClose (instantiate env IT) (instantiate env F) (instantiate env G).
Proof. induction env as [|[x u] env IH]; intros; cbn [instantiate subst substitute]; auto. Qed.
Lemma instantiate_in : forall env t, instantiate env (TIn t) = TIn (instantiate env t).
Proof. induction env as [|[x u] env IH]; intros; cbn [instantiate subst substitute]; auto. Qed.
Lemma instantiate_case : forall env k IT F G i Q b t,
  instantiate env (TCloseCase k IT F G i Q b t) =
  TCloseCase k (instantiate env IT) (instantiate env F) (instantiate env G)
    (instantiate env i) (instantiate env Q) (instantiate env b) (instantiate env t).
Proof. induction env as [|[x u] env IH]; intros; cbn [instantiate subst substitute]; auto. Qed.
Lemma instantiate_closed : forall env t, free_vars t = [] -> instantiate env t = t.
Proof.
  induction env as [|[x u] env IH]; intros t H; cbn [instantiate]; [reflexivity|].
  rewrite subst_fresh by (rewrite H;tauto). now apply IH.
Qed.

Lemma observations_separate : forall t u,
  observation t -> observation u -> conv t u -> t = u.
Proof.
  intros t u [Ht|Ht] [Hu|Hu] HC; subst t u; try reflexivity;
    exfalso; pose proof (raw_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.
Lemma observation_normal_form : forall t,
  typing empty_ctx t observation_type -> exists v, eval t v /\ observation v.
Proof.
  intros t Ht.
  change (typing empty_ctx t (TEnumT (row_enum [("true"%string,TI1);("false"%string,TI1)]))) in Ht.
  destruct (enum_normal_form named_preservation observation_termination _ _ Ht)
    as [n [name [D [Hnth He]]]].
  destruct n as [|[|[|n]]]; cbn [nth_error] in Hnth; try discriminate;
    (eexists; split; [exact He|unfold observation;cbn [enum_position];auto]).
Qed.
Lemma observation_evaluation_conversion : forall t u result,
  typing empty_ctx t observation_type -> typing empty_ctx u observation_type ->
  conv t u -> observation result -> eval t result -> eval u result.
Proof.
  intros t u result Ht Hu HC Hr Het.
  destruct (observation_normal_form _ Hu) as [v [Hev Hv]].
  assert (result = v).
  { apply observations_separate; [exact Hr|exact Hv|].
    eapply cv_trans; [apply cv_sym;exact (eval_conversion _ _ Het)|].
    eapply cv_trans; [exact HC|exact (eval_conversion _ _ Hev)]. }
  now subst result.
Qed.

Lemma closed_observational_conversion : forall A t u,
  typing empty_ctx t A -> typing empty_ctx u A -> conv t u -> closed_observational_eq A t u.
Proof.
  intros A t u Ht Hu HC. split; [exact Ht|]. split; [exact Hu|].
  intros x context result Hctx Hr.
  assert (HT : typing empty_ctx (subst t x context) observation_type).
  { change observation_type with (subst t x observation_type).
    eapply named_substitution; [reflexivity|exact Hctx|exact Ht]. }
  assert (HU : typing empty_ctx (subst u x context) observation_type).
  { change observation_type with (subst u x observation_type).
    eapply named_substitution; [reflexivity|exact Hctx|exact Hu]. }
  assert (Hsub : conv (subst t x context) (subst u x context)) by now apply substitution_argument_conversion.
  split; intro He.
  - exact (observation_evaluation_conversion _ _ _ HT HU Hsub Hr He).
  - exact (observation_evaluation_conversion _ _ _ HU HT (cv_sym Hsub) Hr He).
Qed.

Lemma observational_conversion : forall Gamma A t u,
  typing Gamma t A -> typing Gamma u A -> conv t u -> observational_eq Gamma A t u.
Proof.
  intros Gamma A t u Ht Hu HC. split; [exact Ht|]. split; [exact Hu|].
  intros env Hclosing. apply closed_observational_conversion.
  - eapply named_closing_substitution; eassumption.
  - eapply named_closing_substitution; eassumption.
  - now apply instantiate_conversion.
Qed.

Print Assumptions named_closing_substitution.
Print Assumptions closed_observational_conversion.
Print Assumptions observational_conversion.
