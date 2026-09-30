(* Checked constructor inversion and derived typing rules. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesConstructorInversion OpenSignaturesCoercionTyping.
Import ListNotations.

Lemma interp_conversion : forall IT A B X,
  conv A B -> conv (TInterp IT A X) (TInterp IT B X).
Proof. intros; apply cv_compatible, cp_TInterp; auto using cv_refl. Qed.

Section DeadTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma product_projection_typing : forall Gamma A B p (first : bool),
  typing Gamma A (TSort 0) -> typing Gamma B (TSort 0) ->
  typing Gamma p (product A B) ->
  typing Gamma (if first then TFst p else TSnd p) (if first then A else B).
Proof.
  intros Gamma A B p first HA HB Hp.
  pose proof (product_formation weaken _ _ _ 0 0 HA HB) as Hprod.
  destruct first.
  - eapply ty_fst; eassumption.
  - pose proof (@ty_snd Gamma (fresh [A; B]) A B p 0 Hprod Hp) as H.
    rewrite subst_fresh in H; [exact H|apply fresh_not_free; cbn; auto].
Qed.

Lemma dead_nil_typing : forall Gamma IT D X T,
  description_input Gamma IT D X -> conv D (TIChoice TNilE T) ->
  typing Gamma (TLam (fresh [IT; D; X; T]) (TFst (TVar (fresh [IT; D; X; T]))))
    (arrow (TInterp IT D X) Bot).
Proof.
  intros Gamma IT D X T [HIT [HD HX]] HC.
  destruct (typed_empty_choice_view _ _ _ _ HIT HD HC) as [T' [HT HC']].
  assert (HA : typing Gamma (TInterp IT D X) (TSort 0)) by now apply ty_interp.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  eapply arrow_intro_fresh; [exact weaken|exact HA|apply ty_enumt, ty_nile;exact Hctx|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (TInterp IT D X))
    (TFst (if Nat.eqb (fresh [IT; D; X; T]) (fresh [IT; D; X; T])
      then TVar y else TVar (fresh [IT; D; X; T]))) Bot).
  rewrite Nat.eqb_refl.
  pose (Delta := extend Gamma y (TInterp IT D X)).
  assert (HDelta : wf Delta) by (eapply wf_cons; eassumption).
  assert (HIT' : typing Delta IT (TSort 0)) by (eapply weaken; eassumption).
  assert (HX' : typing Delta X (Family IT)) by (eapply weaken; eassumption).
  assert (HT' : typing Delta T' (arrow (TEnumT TNilE) (TIDesc IT))) by (eapply weaken; eassumption).
  eapply interp_choice_fst with (IT:=IT) (D:=T') (X:=X); try eassumption.
  - now apply ty_nile.
  - eapply ty_conv with (A:=TInterp IT D X).
    + apply ty_var; [exact HDelta|apply lookup_extend_same].
    + apply ty_interp; [exact HIT'|apply ty_ichoice;auto using ty_nile|exact HX'].
    + now apply interp_conversion.
Qed.

Lemma dead_product_typing : forall Gamma IT D X A B d (first : bool),
  description_input Gamma IT D X -> conv D (TIProd A B) ->
  typing Gamma (if first then A else B) (TIDesc IT) ->
  typing Gamma d (arrow (TInterp IT (if first then A else B) X) Bot) ->
  let x := fresh [IT; D; X; A; B; d] in
  typing Gamma (TLam x (TApp d (if first then TFst (TVar x) else TSnd (TVar x))))
    (arrow (TInterp IT D X) Bot).
Proof.
  intros Gamma IT D X A B d first [HIT [HD HX]] HC Hpart Hd x.
  destruct (typed_iprod_view _ _ _ _ _ HIT HD HC) as [A' [B' [HA' [HB' [HAA' [HBB' Hprod]]]]]].
  assert (Hdom : typing Gamma (TInterp IT D X) (TSort 0)) by now apply ty_interp.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  assert (Hxd : ~ In x (free_vars d)) by (apply fresh_not_free; cbn; tauto).
  eapply arrow_intro_fresh; [exact weaken|exact Hdom|apply ty_enumt, ty_nile;exact Hctx|].
  intros y Hy Hfree.
  replace (subst (TVar y) x (TApp d (if first then TFst (TVar x) else TSnd (TVar x))))
    with (TApp d (if first then TFst (TVar y) else TSnd (TVar y)))
    by (destruct first; cbn [subst substitute]; fold (subst (TVar y) x d); rewrite Nat.eqb_refl, subst_fresh by exact Hxd; reflexivity).
  pose (Delta := extend Gamma y (TInterp IT D X)).
  assert (HDelta : wf Delta) by (eapply wf_cons; eassumption).
  assert (HIT' : typing Delta IT (TSort 0)) by (eapply weaken; eassumption).
  assert (HX' : typing Delta X (Family IT)) by (eapply weaken; eassumption).
  assert (HA'' : typing Delta A' (TIDesc IT)) by (eapply weaken; eassumption).
  assert (HB'' : typing Delta B' (TIDesc IT)) by (eapply weaken; eassumption).
  assert (HPA : typing Delta (TInterp IT A' X) (TSort 0)) by now apply ty_interp.
  assert (HPB : typing Delta (TInterp IT B' X) (TSort 0)) by now apply ty_interp.
  assert (HPC : typing Delta (TInterp IT (if first then A else B) X) (TSort 0)).
  { apply ty_interp; [exact HIT'|eapply weaken; eassumption|exact HX']. }
  assert (Hvar : typing Delta (TVar y) (product (TInterp IT A' X) (TInterp IT B' X))).
  { eapply ty_conv with (A:=TInterp IT D X).
    - apply ty_var; [exact HDelta|apply lookup_extend_same].
    - exact (product_formation weaken _ _ _ 0 0 HPA HPB).
    - eapply cv_trans; [apply interp_conversion;exact Hprod|apply cv_step, st_root;reflexivity]. }
  eapply arrow_app; [exact weaken|exact HPC|apply ty_enumt, ty_nile;exact HDelta| |].
  - eapply weaken; eassumption.
  - eapply ty_conv with (A:=if first then TInterp IT A' X else TInterp IT B' X).
    + eapply product_projection_typing; eassumption.
    + exact HPC.
    + destruct first; apply interp_conversion, cv_sym; assumption.
Qed.

Scheme dead_mut := Induction for dead Sort Prop
  with dead_rows_mut := Induction for dead_rows Sort Prop.
Combined Scheme dead_mutual from dead_mut, dead_rows_mut.

Theorem dead_from_rules : forall Gamma IT D X d,
  dead Gamma IT D X d -> typing Gamma d (arrow (TInterp IT D X) Bot).
Proof.
  refine (proj1 (dead_mutual
    (fun Gamma IT D X d _ => typing Gamma d (arrow (TInterp IT D X) Bot))
    (fun Gamma IT rs X hs _ => Forall2
      (fun entry h => typing Gamma h (arrow (TInterp IT (snd entry) X) Bot)) rs hs)
    _ _ _ _ _ _ _ _)).
  - intros Gamma IT D X [HIT [HD HX]] HC.
    eapply identity_for_typing; [exact weaken|now apply ty_interp| |].
    + apply ty_enumt, ty_nile. eapply typing_context; eassumption.
    + eapply cv_trans; [apply interp_conversion;exact HC|apply cv_step, st_root;reflexivity].
  - intros; now apply dead_nil_typing.
  - intros Gamma IT D X A B d Hinput HC Hdead Hd.
    exact (dead_product_typing Gamma IT D X A B d true Hinput HC
      (proj1 (proj2 (dead_input _ _ _ _ _ Hdead))) Hd).
  - intros Gamma IT D X A B d Hinput HC Hdead Hd.
    exact (dead_product_typing Gamma IT D X A B d false Hinput HC
      (proj1 (proj2 (dead_input _ _ _ _ _ Hdead))) Hd).
  - intros Gamma IT D X rs hs [HIT [HD HX]] Hview Hdead Hhs.
    inversion Hview as [rs0 Hrow HD' HC]; subst rs0.
    assert (HBot : typing Gamma Bot (TSort 0)) by (apply ty_enumt, ty_nile; eapply typing_context; eassumption).
    eapply ty_conv with (A:=arrow (TInterp IT (row_code IT rs) X) Bot).
    + apply row_map_typing; [exact weaken|exact Hrow|exact HX|exact HBot|].
      apply row_handlers_tuple; assumption.
    + apply arrow_formation; [exact weaken|now apply ty_interp|exact HBot].
    + apply arrow_conversion; [apply interp_conversion, cv_sym;exact HC|apply cv_refl].
  - intros; assumption.
  - intros; constructor.
  - intros; constructor; assumption.
Qed.
End DeadTyping.
