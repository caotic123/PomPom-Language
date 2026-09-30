(* Description interpretation computes without assuming subject reduction. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBConstructorGeneration.
Import ListNotations.

Lemma arrow_application : forall Gamma A B f a,
  typing Gamma f (arrow A B) -> typing Gamma a A -> typing Gamma (TApp f a) B.
Proof.
  intros Gamma A B f a Hf Ha.
  pose proof (regular_application _ _ _ _ _ Hf Ha) as H.
  now rewrite subst_lift_zero in H.
Qed.
Lemma product_formation : forall Gamma A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (product A B) (TSort (Nat.max j k)).
Proof. intros Gamma A B j k HA HB; apply ty_sigma; [exact HA|exact (weakening _ _ _ _ _ HB HA)]. Qed.

Lemma pair_first : forall Gamma A B a b,
  typing Gamma (TPair a b) (TSigma A B) -> typing Gamma a A.
Proof.
  intros Gamma A B a b H. destruct (type_correctness _ _ _ H) as [k HS].
  eapply fst_preservation; eassumption.
Qed.
Lemma pair_second : forall Gamma A B a b,
  typing Gamma (TPair a b) (TSigma A B) -> typing Gamma b (subst a 0 B).
Proof.
  intros Gamma A B a b H.
  destruct (type_correctness _ _ _ H) as [k HS].
  destruct (sigma_components _ _ _ HS _ _ eq_refl) as [j [l [HA HB]]].
  eapply ty_conv.
  - eapply snd_preservation; eassumption.
  - exact (substitution _ _ _ _ _ HB (pair_first _ _ _ _ _ H)).
  - apply substitution_argument_conversion, cv_step, st_root; reflexivity.
Qed.

Lemma interpretation_binder_typing : forall Gamma IT A D X,
  typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing (A::Gamma)
    (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)) (TSort 0).
Proof.
  intros Gamma IT A D X HI HA HD HX.
  pose proof (weakening _ _ _ _ _ HI HA) as HI'.
  pose proof (weakening _ _ _ _ _ HD HA) as HD'. rewrite lift_arrow in HD'.
  pose proof (weakening _ _ _ _ _ HX HA) as HX'. rewrite lift_Family in HX'.
  apply ty_interp; [exact HI'| |exact HX'].
  eapply arrow_application; [exact HD'|].
  apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity].
Qed.

Theorem interp_beta : forall Gamma IT D X u,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
  typing Gamma X (Family IT) -> root_step (TInterp IT D X) = Some u ->
  typing Gamma u (TSort 0).
Proof.
  intros Gamma IT D X u HI HD HX Hr.
  pose proof (description_inversion _ _ _ HI HD) as HV.
  destruct D; cbn [root_step] in Hr; try discriminate; inversion Hr; subst;
    cbn [description_components] in HV; try match type of HV with _ /\ _ => destruct HV as [HA HB] end.
  - exact (regular_application _ _ _ _ _ HX HV).
  - apply ty_unitT; eauto using typing_context.
  - apply ty_enumt, smart_nile; eauto using typing_context.
  - change (TSort 0) with (TSort (Nat.max 0 0)).
    apply product_formation; apply ty_interp; assumption.
  - change (TSort 0) with (TSort (Nat.max 0 0)).
    apply ty_pi; [exact HA|eapply interpretation_binder_typing; eassumption].
  - change (TSort 0) with (TSort (Nat.max 0 0)).
    apply ty_sigma; [exact HA|eapply interpretation_binder_typing; eassumption].
  - change (TSort 0) with (TSort (Nat.max 0 0)).
    apply ty_sigma; [now apply ty_enumt|].
    eapply interpretation_binder_typing; eauto using ty_enumt.
Qed.

Theorem interp_reduction_preservation : forall Gamma t T,
  typing Gamma t T -> forall IT D X u,
  t = TInterp IT D X -> root_step t = Some u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros JT DD XX u Heq Hr; try discriminate.
  - eapply ty_conv; [eapply IHtyping1; eassumption|eassumption|eassumption].
  - eapply ty_cumul; [eapply IHtyping; eassumption|eassumption].
  - inversion Heq; subst. eapply interp_beta; eassumption.
  - eapply ty_cumul_fun; [eapply IHtyping1; eassumption|eassumption|eassumption|eassumption|eassumption].
Qed.

Lemma interp_payload_compute : forall Gamma IT D X x R,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma x (TInterp IT D X) -> root_step (TInterp IT D X) = Some R -> typing Gamma x R.
Proof.
  intros. eapply ty_conv; [eassumption|eapply interp_beta; eassumption|apply cv_step, st_root; eassumption].
Qed.

Lemma interpreted_pair : forall Gamma IT D X a b A B,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma (TPair a b) (TInterp IT D X) ->
  root_step (TInterp IT D X) = Some (TSigma A B) ->
  typing Gamma a A /\ typing Gamma b (subst a 0 B).
Proof.
  intros Gamma IT D X a b A B HI HD HX Hx HR.
  pose proof (interp_payload_compute _ _ _ _ _ _ HI HD HX Hx HR) as Hpair.
  split; eauto using pair_first, pair_second.
Qed.

Lemma interpreted_product : forall Gamma IT A B X a b,
  typing Gamma IT (TSort 0) -> typing Gamma (TIProd A B) (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma (TPair a b) (TInterp IT (TIProd A B) X) ->
  typing Gamma a (TInterp IT A X) /\ typing Gamma b (TInterp IT B X).
Proof.
  intros Gamma IT A B X a b HI HD HX Hx.
  destruct (interpreted_pair _ _ _ _ _ _ _ _ HI HD HX Hx eq_refl) as [Ha Hb].
  rewrite subst_lift_zero in Hb. auto.
Qed.

Lemma instantiated_interpretation : forall IT D X a,
  subst a 0 (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)) =
  TInterp IT (TApp D a) X.
Proof. intros; cbn [subst]; now rewrite ?subst_lift_zero, ?lift_zero_id. Qed.

Lemma application_in_binder : forall Gamma A B f j,
  typing Gamma A (TSort j) -> typing Gamma f (TPi A B) ->
  typing (A::Gamma) (TApp (lift 1 0 f) (TVar 0)) B.
Proof.
  intros Gamma A B f j HA Hf.
  pose proof (weakening _ _ _ _ _ Hf HA) as Hf'. cbn [lift] in Hf'.
  assert (Hv : typing (A::Gamma) (TVar 0) (lift 1 0 A))
    by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
  pose proof (regular_application _ _ _ _ _ Hf' Hv) as H.
  now rewrite subst_eta_beta_cancel in H.
Qed.

Lemma iall_binder_typing : forall Gamma IT A D X f P,
  typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma f (TPi A (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X))) ->
  typing Gamma P (motive IT X) ->
  typing (A::Gamma)
    (TIAll (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)
      (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)) (TSort 0).
Proof.
  intros Gamma IT A D X f P HI HA HD HX Hf HP.
  pose proof (weakening _ _ _ _ _ HI HA) as HI'.
  pose proof (weakening _ _ _ _ _ HD HA) as HD'. rewrite lift_arrow in HD'.
  pose proof (weakening _ _ _ _ _ HX HA) as HX'. rewrite lift_Family in HX'.
  pose proof (weakening _ _ _ _ _ HP HA) as HP'. rewrite lift_motive in HP'.
  apply ty_iall; [exact HI'| |exact HX'|eapply application_in_binder; eassumption|exact HP'].
  eapply arrow_application; [exact HD'|].
  apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity].
Qed.

Theorem iall_beta : forall Gamma IT D X x P u,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma x (TInterp IT D X) -> typing Gamma P (motive IT X) ->
  root_step (TIAll IT D X x P) = Some u -> typing Gamma u (TSort 0).
Proof.
  intros Gamma IT D X x P u HI HD HX Hx HP Hr.
  pose proof (description_inversion _ _ _ HI HD) as HV.
  destruct D; cbn [root_step] in Hr; try discriminate;
    cbn [description_components] in HV.
  - inversion Hr; subst. eapply motive_application; try eassumption.
    eapply interp_payload_compute; [exact HI|exact HD|exact HX|exact Hx|reflexivity].
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    apply ty_unitT; eauto using typing_context.
  - inversion Hr; subst. apply ty_unitT; eauto using typing_context.
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_product _ _ _ _ _ _ _ HI HD HX Hx) as [Ha Hb].
    change (TSort 0) with (TSort (Nat.max 0 0)).
    apply product_formation; apply ty_iall; assumption.
  - inversion Hr; subst. destruct HV as [HA HB].
    change (TSort 0) with (TSort (Nat.max 0 0)). apply ty_pi; [exact HA|].
    eapply iall_binder_typing; try eassumption.
    eapply interp_payload_compute; [exact HI|exact HD|exact HX|exact Hx|reflexivity].
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_pair _ _ _ _ _ _ _ _ HI HD HX Hx eq_refl) as [Ha Hb].
    rewrite instantiated_interpretation in Hb.
    apply ty_iall; eauto using arrow_application.
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_pair _ _ _ _ _ _ _ _ HI HD HX Hx eq_refl) as [Ha Hb].
    rewrite instantiated_interpretation in Hb.
    apply ty_iall; eauto using arrow_application.
Qed.

Lemma product_intro : forall Gamma a b A B,
  typing Gamma a A -> typing Gamma b B -> typing Gamma (TPair a b) (product A B).
Proof.
  intros Gamma a b A B Ha Hb.
  destruct (type_correctness _ _ _ Ha) as [j HA].
  destruct (type_correctness _ _ _ Hb) as [k HB].
  eapply ty_pair; [eapply product_formation; eassumption|exact Ha|].
  now rewrite subst_lift_zero.
Qed.

Lemma recursive_method_application : forall Gamma IT X P h i x,
  typing Gamma h (recursive_method IT X P) -> typing Gamma i IT ->
  typing Gamma x (TApp X i) -> typing Gamma (TApp (TApp h i) x) (TApp P (TPair i x)).
Proof.
  intros Gamma IT X P h i x Hh Hi Hx.
  pose proof (regular_application _ _ _ _ _ Hh Hi) as H1.
  cbn [recursive_method subst] in H1.
  rewrite ?subst_lift_prefix, ?lift_zero_id in H1 by lia.
  cbn [Nat.ltb Nat.leb Nat.eqb] in H1.
  pose proof (regular_application _ _ _ _ _ H1 Hx) as H2.
  cbn [subst] in H2. now rewrite ?subst_lift_zero, ?lift_zero_id in H2.
Qed.

Lemma hyps_binder_typing : forall Gamma IT A D X f P h,
  typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma f (TPi A (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X))) ->
  typing Gamma P (motive IT X) -> typing Gamma h (recursive_method IT X P) ->
  typing (A::Gamma)
    (THyps (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)
      (lift 1 0 P) (lift 1 0 h) (TApp (lift 1 0 f) (TVar 0)))
    (TIAll (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0)) (lift 1 0 X)
      (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)).
Proof.
  intros Gamma IT A D X f P h HI HA HD HX Hf HP Hh.
  pose proof (weakening _ _ _ _ _ HI HA) as HI'.
  pose proof (weakening _ _ _ _ _ HD HA) as HD'. rewrite lift_arrow in HD'.
  pose proof (weakening _ _ _ _ _ HX HA) as HX'. rewrite lift_Family in HX'.
  pose proof (weakening _ _ _ _ _ HP HA) as HP'. rewrite lift_motive in HP'.
  pose proof (weakening _ _ _ _ _ Hh HA) as Hh'. rewrite lift_recursive_method in Hh'.
  apply smart_hyps; [exact HI'| |exact HX'|exact HP'|exact Hh'|eapply application_in_binder; eassumption].
  eapply arrow_application; [exact HD'|].
  apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity].
Qed.

Theorem hyps_beta : forall Gamma IT D X P h x u,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> typing Gamma X (Family IT) ->
  typing Gamma P (motive IT X) -> typing Gamma h (recursive_method IT X P) ->
  typing Gamma x (TInterp IT D X) -> root_step (THyps IT D X P h x) = Some u ->
  typing Gamma u (TIAll IT D X x P).
Proof.
  intros Gamma IT D X P h x u HI HD HX HP Hh Hx Hr.
  pose proof (description_inversion _ _ _ HI HD) as HV.
  assert (HT : typing Gamma (TIAll IT D X x P) (TSort 0)) by (apply ty_iall; assumption).
  destruct D; cbn [root_step] in Hr; try discriminate;
    cbn [description_components] in HV.
  - inversion Hr; subst. eapply ty_conv; [|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
    eapply recursive_method_application; try eassumption.
    eapply interp_payload_compute; [exact HI|exact HD|exact HX|exact Hx|reflexivity].
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    eapply ty_conv; [apply smart_unit; eauto using typing_context|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
  - inversion Hr; subst.
    eapply ty_conv; [apply smart_unit; eauto using typing_context|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_product _ _ _ _ _ _ _ HI HD HX Hx) as [Ha Hb].
    eapply ty_conv; [|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
    apply product_intro; apply smart_hyps; assumption.
  - inversion Hr; subst. destruct HV as [HA HB].
    eapply ty_conv; [|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
    apply regular_lambda; [exists 0; exact HA|].
    eapply hyps_binder_typing; try eassumption.
    eapply interp_payload_compute; [exact HI|exact HD|exact HX|exact Hx|reflexivity].
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_pair _ _ _ _ _ _ _ _ HI HD HX Hx eq_refl) as [Ha Hb].
    rewrite instantiated_interpretation in Hb.
    eapply ty_conv; [|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
    apply smart_hyps; eauto using arrow_application.
  - destruct x; cbn in Hr; try discriminate; inversion Hr; subst.
    destruct HV as [HA HB].
    destruct (interpreted_pair _ _ _ _ _ _ _ _ HI HD HX Hx eq_refl) as [Ha Hb].
    rewrite instantiated_interpretation in Hb.
    eapply ty_conv; [|exact HT|apply cv_sym, cv_step, st_root; reflexivity].
    apply smart_hyps; eauto using arrow_application.
Qed.
