From Stdlib Require Import List Arith Bool Lia.
Require Import OpenSignaturesTheorems InclusionWork ClosedSubWork.
Import ListNotations.

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
Variable preserve : forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A.

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
  destruct (extension_domain_formation weaken regular preserve _ _ _ Hctx Hfresh Hwf) as [j HA].
  destruct (regular _ _ _ Ht) as [k HB].
  assert (HPi : typing Gamma (TPi x A B) (TSort (Nat.max j k))) by (eapply ty_pi; eassumption).
  assert (Hlam : typing Gamma (TLam x t) (TPi x A B)) by (eapply ty_lam; eassumption).
  pose proof (IH _ _ HPi) as HPi'; pose proof (IH _ _ Hlam) as Hlam'.
  rewrite instantiate_pi, instantiate_sort in HPi' by exact Haway.
  rewrite instantiate_lam, instantiate_pi in Hlam' by exact Haway.
  pose proof (@ty_app empty_ctx x (instantiate env A) (instantiate env B)
    (TLam x (instantiate env t)) u _ HPi' Hlam' Hu) as Happ.
  assert (Hsub : typing empty_ctx (subst u x (instantiate env t)) (subst u x (instantiate env B)))
    by (eapply preserve; [exact Happ|apply red_root;reflexivity]).
  destruct (regular _ _ _ Hsub) as [l Hform].
  pose proof (instantiate_commute env x u t Haway Hclosed) as Hterm.
  pose proof (instantiate_commute env x u B Haway Hclosed) as Htype.
  eapply ty_conv with (A:=subst u x (instantiate env B)).
  - eapply ty_alpha; [exact Hsub|now symmetry].
  - eapply ty_alpha; [exact Hform|now symmetry].
  - apply cv_alpha; now symmetry.
Qed.
End ClosingTyping.
