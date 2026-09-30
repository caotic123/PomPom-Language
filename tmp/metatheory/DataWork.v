From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesDerivedTyping.
Import ListNotations.

Section DescriptionTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma interp_sig_pair : forall Gamma IT A D X a b,
  typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma a A -> typing Gamma b (TInterp IT (TApp D a) X) ->
  typing Gamma (TPair a b) (TInterp IT (TISig A D) X).
Proof.
  intros Gamma IT A D X a b HIT HA HD HX Ha Hb.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  destruct (exists_fresh_id Gamma []) as [y [Hy _]].
  assert (Hyi : ~ In y (free_vars IT)) by (eapply typing_fresh_not_free; eassumption).
  assert (Hyd : ~ In y (free_vars D)) by (eapply typing_fresh_not_free; eassumption).
  assert (Hyx : ~ In y (free_vars X)) by (eapply typing_fresh_not_free; eassumption).
  assert (Hdom : typing (extend Gamma y A) A (TSort 0)) by (eapply weaken; eassumption).
  assert (HIT' : typing (extend Gamma y A) IT (TSort 0)) by (eapply weaken; eassumption).
  assert (Hbody : typing (extend Gamma y A)
    (TInterp IT (TApp D (TVar y)) X) (TSort 0)).
  { apply ty_interp; [exact HIT'| |eapply weaken; eassumption].
    eapply arrow_app; [exact weaken|exact Hdom|now apply ty_idesc| |].
    - eapply weaken; eassumption.
    - apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same]. }
  eapply ty_conv with (A := TSigma y A (TInterp IT (TApp D (TVar y)) X)).
  - eapply ty_pair; [eapply ty_sigma; eassumption|exact Ha|].
    change (typing Gamma b (TInterp (subst a y IT)
      (TApp (subst a y D) (if y =? y then a else TVar y)) (subst a y X))).
    rewrite Nat.eqb_refl, !subst_fresh by assumption. exact Hb.
  - apply ty_interp; [exact HIT|now apply ty_isig|exact HX].
  - eapply cv_trans with
      (u := TSigma (fresh [IT; A; D; X]) A
        (TInterp IT (TApp D (TVar (fresh [IT; A; D; X]))) X)).
    + apply cv_alpha. unfold alpha_equiv, alpha_eqb. cbn [alpha_eqb_in].
      repeat rewrite Bool.andb_true_iff. repeat split; try apply alpha_eqb_in_refl.
      all: try solve [apply alpha_env_fresh; [apply alpha_eqb_in_refl|assumption|
        apply fresh_not_free; cbn; tauto]].
      cbn [alpha_var]. now rewrite !Nat.eqb_refl.
    + apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Lemma interp_choice_pair : forall Gamma IT E D X e b,
  typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
  typing Gamma D (arrow (TEnumT E) (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma e (TEnumT E) -> typing Gamma b (TInterp IT (TApp D e) X) ->
  typing Gamma (TPair e b) (TInterp IT (TIChoice E D) X).
Proof.
  intros Gamma IT E D X e b HIT HE HD HX He Hb.
  eapply ty_conv with (A := TInterp IT (TISig (TEnumT E) D) X).
  - apply interp_sig_pair; auto using ty_enumt.
  - apply ty_interp; [exact HIT|now apply ty_ichoice|exact HX].
  - eapply cv_trans; [apply cv_step, st_root; reflexivity|].
    apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Lemma interp_unit : forall Gamma IT X,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing Gamma TUnit (TInterp IT TI1 X).
Proof.
  intros Gamma IT X HIT HX. eapply ty_conv with (A := TUnitT).
  - apply ty_unit. eapply typing_context; exact HIT.
  - apply ty_interp; auto using ty_i1.
  - apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Lemma interp_variable : forall Gamma IT X i t,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing Gamma i IT -> typing Gamma t (TApp X i) ->
  typing Gamma t (TInterp IT (TIVar i) X).
Proof.
  intros Gamma IT X i t HIT HX Hi Ht. eapply ty_conv; [exact Ht| |].
  - apply ty_interp; auto using ty_ivar.
  - apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Lemma interp_product_pair : forall Gamma IT A B X a b,
  typing Gamma IT (TSort 0) -> typing Gamma A (TIDesc IT) ->
  typing Gamma B (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma a (TInterp IT A X) -> typing Gamma b (TInterp IT B X) ->
  typing Gamma (TPair a b) (TInterp IT (TIProd A B) X).
Proof.
  intros Gamma IT A B X a b HIT HA HB HX Ha Hb.
  eapply ty_conv with (A := product (TInterp IT A X) (TInterp IT B X)).
  - eapply product_pair; eauto using ty_interp.
  - apply ty_interp; auto using ty_iprod.
  - apply cv_sym, cv_step, st_root. reflexivity.
Qed.

End DescriptionTyping.
