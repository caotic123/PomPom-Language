From Stdlib Require Import List Arith Bool String Lia.
Require Import OpenSignaturesTheorems.
Import ListNotations.

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
  now apply IH, conversion_substitution.
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
  destruct (enum_normal_form full_preservation normalization_eval _ _ Ht)
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
    eapply substitution; [reflexivity|exact Hctx|exact Ht]. }
  assert (HU : typing empty_ctx (subst u x context) observation_type).
  { change observation_type with (subst u x observation_type).
    eapply substitution; [reflexivity|exact Hctx|exact Hu]. }
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
  - eapply closing_substitution; eassumption.
  - eapply closing_substitution; eassumption.
  - now apply instantiate_conversion.
Qed.

Theorem close_roll_unroll_proof : forall Gamma IT F G i x,
  close_input Gamma IT F G i -> typing Gamma x (CloseAt IT F G i) ->
  observational_eq Gamma (CloseAt IT F G i) (TIn (unroll IT F G i x)) x.
Proof.
  intros Gamma IT F G i x Hinput Hx.
  assert (Hroll : typing Gamma (TIn (unroll IT F G i x)) (CloseAt IT F G i)).
  { destruct Hinput as [HIT [HF [HG Hi]]]. apply ty_in_close; try assumption.
    apply unroll_typing; [repeat split;assumption|exact Hx]. }
  split; [exact Hroll|]. split; [exact Hx|]. intros env Hclosing.
  pose proof (closing_substitution _ _ _ _ Hclosing Hx) as Hclosed.
  apply closed_observational_conversion.
  - eapply closing_substitution; eassumption.
  - exact Hclosed.
  - unfold CloseAt in Hclosed; rewrite instantiate_app, instantiate_close in Hclosed.
    destruct (normalization_eval _ _ Hclosed) as [v [He Hv]].
    pose proof (preservation_eval _ _ _ _ Hclosed He) as Hvt.
    destruct (close_value_shape _ _ _ _ _ _ Hvt Hv) as [xs ->].
    eapply cv_trans with (u:=TIn xs); [|apply cv_sym;now apply eval_conversion].
    unfold unroll. rewrite instantiate_in, instantiate_case.
    rewrite (instantiate_closed env identity) by reflexivity.
    apply eval_conversion, (eval_congruence TIn); [auto using st_TIn_x|].
    eapply eval_transitive.
    + apply (eval_congruence (fun t => TCloseCase 0 (instantiate env IT) (instantiate env F)
        (instantiate env G) (instantiate env i) _ identity t)); [auto using st_TCloseCase_x|exact He].
    + eapply ev_step; [apply st_root;reflexivity|].
      eapply ev_step; [apply st_root;reflexivity|constructor].
Qed.
