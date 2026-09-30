(* Derived typing rules. StructuralTyping takes weakening explicitly;
   no metatheory conjectures are imported here. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesSubstitution OpenSignaturesProgress.
Import ListNotations.

Lemma universe_le_typing_formed : forall Gamma t A B j k,
  typing Gamma t A -> typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  universe_le A B -> typing Gamma t B.
Proof.
  intros Gamma t A B j k Ht HA HB HU; destruct HU;
    eauto using ty_cumul, ty_cumul_fun.
Qed.

Lemma fresh_not_free : forall ts t,
  In t ts -> ~ In (fresh ts) (free_vars t).
Proof.
  intros ts t Hin Hfree. apply (fresh_id_not_in (flat_map vars ts)).
  apply in_flat_map. exists t. split; [exact Hin|now apply free_vars_in_vars].
Qed.

Lemma in_lt_fresh_id : forall ids x, In x ids -> x < fresh_id ids.
Proof.
  unfold fresh_id. induction ids as [|a ids IH]; intros x Hin; cbn in *.
  - contradiction.
  - destruct Hin as [<-|Hin]; specialize (Nat.le_max_l a (fold_right Nat.max 0 ids));
      specialize (Nat.le_max_r a (fold_right Nat.max 0 ids));
      try specialize (IH x Hin); lia.
Qed.

Lemma above_fresh_not_free : forall ts t x,
  In t ts -> fresh ts <= x -> ~ In x (free_vars t).
Proof.
  intros ts t x Ht Hbound Hin.
  assert (Hin' : In x (flat_map vars ts)).
  { apply in_flat_map. exists t. split; [exact Ht|now apply free_vars_in_vars]. }
  pose proof (in_lt_fresh_id _ _ Hin'). unfold fresh in Hbound. lia.
Qed.

Lemma constant_pi_alpha : forall A B x y,
  ~ In x (free_vars B) -> ~ In y (free_vars B) ->
  alpha_equiv (TPi x A B) (TPi y A B).
Proof.
  intros A B x y Hx Hy. unfold alpha_equiv, alpha_eqb. cbn [alpha_eqb_in].
  rewrite alpha_eqb_in_refl. apply alpha_env_fresh; auto using alpha_eqb_in_refl.
Qed.

Lemma constant_sigma_alpha : forall A B x y,
  ~ In x (free_vars B) -> ~ In y (free_vars B) ->
  alpha_equiv (TSigma x A B) (TSigma y A B).
Proof.
  intros A B x y Hx Hy. unfold alpha_equiv, alpha_eqb. cbn [alpha_eqb_in].
  rewrite alpha_eqb_in_refl. apply alpha_env_fresh; auto using alpha_eqb_in_refl.
Qed.

Lemma constant_free_vars : forall A x,
  In x (free_vars (constant A)) <-> In x (free_vars A).
Proof.
  intros A x. unfold constant. cbn [free_vars]. rewrite in_remove_iff.
  split; [tauto|]. intro H. split; [exact H|]. intro E. subst x.
  exact (fresh_not_free [A] A ltac:(cbn; auto) H).
Qed.

Lemma product_conversion : forall A B C D,
  conv A C -> conv B D -> conv (product A B) (product C D).
Proof.
  intros A B C D HAC HBD. pose (x := fresh [B; D]).
  eapply cv_trans with (u := TSigma x A B).
  - apply cv_alpha, constant_sigma_alpha; apply fresh_not_free; cbn; auto.
  - eapply cv_trans with (u := TSigma x C D).
    + apply cv_compatible, cp_TSigma; assumption.
    + apply cv_alpha, constant_sigma_alpha; apply fresh_not_free; cbn; auto.
Qed.

Lemma arrow_conversion : forall A B C D,
  conv A C -> conv B D -> conv (arrow A B) (arrow C D).
Proof.
  intros A B C D HAC HBD. pose (x := fresh [B; D]).
  eapply cv_trans with (u := TPi x A B).
  - apply cv_alpha, constant_pi_alpha; apply fresh_not_free; cbn; auto.
  - eapply cv_trans with (u := TPi x C D).
    + apply cv_compatible, cp_TPi; assumption.
    + apply cv_alpha, constant_pi_alpha; apply fresh_not_free; cbn; auto.
Qed.

Lemma substitute_constant_pi : forall sigma A B x,
  (forall v, In v (free_vars B) -> sigma v = TVar v) ->
  substitute sigma (TPi x A B) = TPi x (substitute sigma A) B.
Proof.
  intros sigma A B x H. cbn [substitute].
  rewrite substitution_binder_identity by (intros v Hv; apply H; now apply in_remove in Hv).
  f_equal. apply substitute_identity_on. intros v Hv. unfold bind_substitution.
  destruct (v =? x) eqn:E; [apply Nat.eqb_eq in E; now subst|now apply H].
Qed.

Lemma subst_constant_pi : forall A B x u y,
  ~ In y (free_vars B) -> subst u y (TPi x A B) = TPi x (subst u y A) B.
Proof.
  intros A B x u y Hy. apply substitute_constant_pi. intros v Hv.
  destruct (v =? y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|reflexivity].
Qed.

Lemma constant_lambda_conversion : forall A x b,
  ~ In x (free_vars A) -> conv b A -> conv (TLam x b) (constant A).
Proof.
  intros A x b Hx Hb. eapply cv_trans with (u := TLam x A).
  - apply cv_compatible, cp_TLam. exact Hb.
  - apply cv_alpha, alpha_env_fresh; [apply alpha_eqb_in_refl|exact Hx|].
    apply fresh_not_free; cbn; auto.
Qed.

Lemma constant_application : forall A t, conv (TApp (constant A) t) A.
Proof.
  intros. replace A with (subst t (fresh [A]) A) at 2.
  - apply cv_step, st_root. reflexivity.
  - apply subst_fresh. apply fresh_not_free; cbn; auto.
Qed.

Lemma pi_formation_fresh : forall Gamma x A B j k,
  typing Gamma A (TSort j) ->
  (forall y, fresh_in Gamma y -> ~ In y (remove Nat.eq_dec x (free_vars B)) ->
    typing (extend Gamma y A) (subst (TVar y) x B) (TSort k)) ->
  typing Gamma (TPi x A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma x A B j k HA HB.
  destruct (exists_fresh_id Gamma (remove Nat.eq_dec x (free_vars B))) as [y [Hy Hfree]].
  eapply ty_alpha with (t := TPi y A (subst (TVar y) x B)).
  - eapply ty_pi; eauto.
  - symmetry. now apply alpha_rename_pi.
Qed.

Lemma sigma_formation_fresh : forall Gamma x A B j k,
  typing Gamma A (TSort j) ->
  (forall y, fresh_in Gamma y -> ~ In y (remove Nat.eq_dec x (free_vars B)) ->
    typing (extend Gamma y A) (subst (TVar y) x B) (TSort k)) ->
  typing Gamma (TSigma x A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma x A B j k HA HB.
  destruct (exists_fresh_id Gamma (remove Nat.eq_dec x (free_vars B))) as [y [Hy Hfree]].
  eapply ty_alpha with (t := TSigma y A (subst (TVar y) x B)).
  - eapply ty_sigma; eauto.
  - symmetry. now apply alpha_rename_sigma.
Qed.

Section StructuralTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma constant_pi_formation : forall Gamma x A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  ~ In x (free_vars B) ->
  typing Gamma (TPi x A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma x A B j k HA HB Hx.
  destruct (exists_fresh_id Gamma []) as [y [Hy _]].
  eapply ty_alpha with (t := TPi y A B).
  - eapply ty_pi; eauto using weaken.
  - apply constant_pi_alpha; eauto using typing_fresh_not_free.
Qed.

Lemma arrow_formation : forall Gamma A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (arrow A B) (TSort (Nat.max j k)).
Proof.
  intros. apply constant_pi_formation; try assumption.
  apply fresh_not_free; cbn; auto.
Qed.

Lemma product_formation : forall Gamma A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (product A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma A B j k HA HB.
  destruct (exists_fresh_id Gamma []) as [y [Hy _]].
  eapply ty_alpha with (t := TSigma y A B).
  - eapply ty_sigma; eauto using weaken.
  - apply constant_sigma_alpha; [eapply typing_fresh_not_free; eassumption|].
    apply fresh_not_free; cbn; auto.
Qed.

Lemma product_pair : forall Gamma A B a b j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma a A -> typing Gamma b B ->
  typing Gamma (TPair a b) (product A B).
Proof.
  intros Gamma A B a b j k HA HB Ha Hb.
  eapply ty_pair; [eapply product_formation; eassumption|exact Ha|].
  rewrite subst_fresh; [exact Hb|apply fresh_not_free; cbn; auto].
Qed.

Lemma arrow_intro : forall Gamma x A B b j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  fresh_in Gamma x -> typing (extend Gamma x A) b B ->
  typing Gamma (TLam x b) (arrow A B).
Proof.
  intros Gamma x A B b j k HA HB Hx Hb.
  eapply ty_conv with (A := TPi x A B).
  - eapply ty_lam; [exact Hx| |exact Hb].
    eapply constant_pi_formation; eauto using typing_fresh_not_free.
  - eapply arrow_formation; eassumption.
  - apply cv_alpha, constant_pi_alpha.
    + eapply typing_fresh_not_free; eassumption.
    + apply fresh_not_free; cbn; auto.
Qed.

Lemma constant_typing : forall Gamma t A B j k,
  typing Gamma t B -> typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (constant t) (arrow A B).
Proof.
  intros Gamma t A B j k Ht HA HB.
  destruct (exists_fresh_id Gamma []) as [x [Hx _]].
  eapply ty_alpha with (t := TLam x t).
  - eapply arrow_intro; eauto using weaken.
  - apply alpha_env_fresh; [apply alpha_eqb_in_refl| |].
    + eapply typing_fresh_not_free; eassumption.
    + apply fresh_not_free; cbn; auto.
Qed.

Lemma constant_lambda_typing : forall Gamma x t A B j k,
  typing Gamma t B -> typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  ~ In x (free_vars t) -> typing Gamma (TLam x t) (arrow A B).
Proof.
  intros Gamma x t A B j k Ht HA HB Hx.
  eapply ty_alpha with (t := constant t).
  - eapply constant_typing; eassumption.
  - apply alpha_env_fresh; [apply alpha_eqb_in_refl| |exact Hx].
    apply fresh_not_free; cbn; auto.
Qed.

Lemma arrow_intro_fresh : forall Gamma x A B b j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  (forall y, fresh_in Gamma y -> ~ In y (remove Nat.eq_dec x (free_vars b)) ->
    typing (extend Gamma y A) (subst (TVar y) x b) B) ->
  typing Gamma (TLam x b) (arrow A B).
Proof.
  intros Gamma x A B b j k HA HB Hb.
  destruct (exists_fresh_id Gamma (remove Nat.eq_dec x (free_vars b))) as [y [Hy Hfree]].
  eapply ty_alpha with (t := TLam y (subst (TVar y) x b)).
  - eapply arrow_intro; eauto.
  - symmetry. now apply alpha_rename_lam.
Qed.

Lemma arrow_app : forall Gamma A B f a j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma f (arrow A B) -> typing Gamma a A ->
  typing Gamma (TApp f a) B.
Proof.
  intros Gamma A B f a j k HA HB Hf Ha.
  pose proof (@ty_app Gamma (fresh [A; B]) A B f a (Nat.max j k)
    (arrow_formation Gamma A B j k HA HB) Hf Ha) as H.
  rewrite subst_fresh in H; [exact H|apply fresh_not_free; cbn; auto].
Qed.

Lemma identity_typing : forall Gamma A k,
  typing Gamma A (TSort k) -> typing Gamma identity (arrow A A).
Proof.
  intros Gamma A k HA. destruct (exists_fresh_id Gamma []) as [x [Hx _]].
  eapply ty_alpha with (t := TLam x (TVar x)).
  - eapply arrow_intro; try eassumption. apply ty_var.
    + eapply wf_cons; eauto using typing_context.
    + apply lookup_extend_same.
  - apply alpha_lam_identity.
Qed.

Lemma def_formation : forall Gamma IT,
  typing Gamma IT (TSort 0) -> typing Gamma (Def IT) (TSort 1).
Proof.
  intros Gamma IT HIT. change (TSort 1) with (TSort (Nat.max 0 1)).
  apply constant_pi_formation; auto using ty_idesc.
  cbn [free_vars]. apply fresh_not_free; cbn; auto.
Qed.

Lemma def_application : forall Gamma IT D i,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) -> typing Gamma i IT ->
  typing Gamma (TApp D i) (TIDesc IT).
Proof.
  intros Gamma IT D i HIT HD Hi.
  replace (TIDesc IT) with (subst i (fresh [IT]) (TIDesc IT)) at 1.
  - eapply ty_app; eauto using def_formation.
  - apply subst_fresh. cbn [free_vars]. apply fresh_not_free; cbn; auto.
Qed.

Lemma payload_formation : forall Gamma IT F G i,
  close_input Gamma IT F G i -> typing Gamma (payload IT F G i) (TSort 0).
Proof.
  intros Gamma IT F G i [HIT [HF [HG Hi]]].
  apply ty_interp; eauto using def_application, ty_close.
Qed.

Theorem abort_from_weakening : forall Gamma k A z,
  typing Gamma A (TSort k) -> typing Gamma z Bot ->
  typing Gamma (abort k A z) A.
Proof.
  intros Gamma k A z HA Hz. pose proof (typing_context _ _ _ HA) as Hctx.
  assert (Hbot : typing Gamma Bot (TSort 0)) by (apply ty_enumt, ty_nile; exact Hctx).
  assert (HP : typing Gamma (constant A) (arrow Bot (TSort k))).
  { eapply constant_typing; eauto using ty_sort. }
  eapply ty_conv with (A := TApp (constant A) z); [|exact HA|apply constant_application].
  apply ty_switch; eauto using ty_nile.
  eapply ty_conv with (A := TUnitT); [auto using ty_unit| |].
  - apply ty_epi; eauto using ty_nile.
  - apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Theorem unroll_from_weakening : forall Gamma IT F G i t,
  close_input Gamma IT F G i -> typing Gamma t (CloseAt IT F G i) ->
  typing Gamma (unroll IT F G i t) (payload IT F G i).
Proof.
  intros Gamma IT F G i t Hinput Ht.
  destruct Hinput as [HIT [HF [HG Hi]]].
  pose (C := payload IT F G i).
  assert (HC : typing Gamma C (TSort 0)) by (apply payload_formation; repeat split; assumption).
  assert (HB : typing Gamma (CloseAt IT F G i) (TSort 0))
    by (apply close_at_formation; assumption).
  assert (Hctx : wf Gamma) by (eapply typing_context; exact HIT).
  assert (HQ : typing Gamma (constant C) (arrow (CloseAt IT F G i) (TSort 0)))
    by (eapply constant_typing; eauto using ty_sort).
  pose (x := fresh [IT; F; G; i; constant C]).
  assert (HxQ : ~ In x (free_vars (constant C)))
    by (apply fresh_not_free; cbn; tauto).
  assert (HxC : ~ In x (free_vars C)).
  { intro Hin. apply HxQ. apply in_in_remove; [|exact Hin].
    intro E. rewrite E in Hin. exact (fresh_not_free [C] C ltac:(cbn; auto) Hin). }
  assert (Hmethod : typing Gamma (close_case_method IT F G i (constant C)) (TSort 0)).
  { change (typing Gamma (TPi x C (TApp (constant C) (TIn (TVar x))))
      (TSort (Nat.max 0 0))).
    apply pi_formation_fresh; [exact HC|]. intros y Hy Hfree.
    change (typing (extend Gamma y C)
      (TApp (subst (TVar y) x (constant C))
        (TIn (if x =? x then TVar y else TVar x))) (TSort 0)).
    rewrite Nat.eqb_refl, subst_fresh by exact HxQ.
    eapply arrow_app with (A := CloseAt IT F G i).
    - eapply weaken; eassumption.
    - apply ty_sort. eapply wf_cons; eassumption.
    - eapply weaken; eassumption.
    - apply ty_in_close; try solve [eapply weaken; eassumption].
      apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same]. }
  assert (Hidentity : typing Gamma identity (close_case_method IT F G i (constant C))).
  { eapply ty_conv with (A := arrow C C); [eapply identity_typing; exact HC|exact Hmethod|].
    eapply cv_trans with (u := TPi x C C).
    - apply cv_alpha, constant_pi_alpha; [apply fresh_not_free; cbn; auto|exact HxC].
    - apply cv_compatible, cp_TPi; [apply cv_refl|]. apply cv_sym, constant_application. }
  eapply ty_conv with (A := TApp (constant C) t); [|exact HC|apply constant_application].
  apply ty_close_case; assumption.
Qed.

End StructuralTyping.
