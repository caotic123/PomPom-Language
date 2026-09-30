(* Checked derived rules with explicit metatheory premises. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Export OpenSignaturesElaborationSoundness.
Import ListNotations.

Lemma enum_position_closed : forall n, free_vars (enum_position n) = [].
Proof. induction n; cbn; auto. Qed.

Lemma dead_input : forall Gamma IT D X d,
  dead Gamma IT D X d -> description_input Gamma IT D X.
Proof. intros Gamma IT D X d H; inversion H; assumption. Qed.

Section CoercionTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable dead_typed : forall Gamma IT D X d,
  dead Gamma IT D X d -> typing Gamma d (arrow (TInterp IT D X) Bot).

Lemma identity_for_typing : forall Gamma A B ts j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) -> conv A B ->
  typing Gamma (identity_for ts) (arrow A B).
Proof.
  intros Gamma A B ts j k HA HB Hconv.
  eapply ty_conv with (A := arrow A A).
  - eapply ty_alpha with (t := identity); [eapply identity_typing; eassumption|apply alpha_lam_identity].
  - eapply arrow_formation; eassumption.
  - apply arrow_conversion; [apply cv_refl|exact Hconv].
Qed.

Lemma retag_handler_typing : forall Gamma IT target X Y n name D D',
  row_input Gamma IT target -> typing Gamma D (TIDesc IT) ->
  typing Gamma X (Family IT) -> typing Gamma Y (TSort 0) ->
  conv Y (TInterp IT (row_code IT target) X) ->
  nth_error target n = Some (name,D') -> conv (TInterp IT D X) (TInterp IT D' X) ->
  typing Gamma (retag_handler n) (arrow (TInterp IT D X) Y).
Proof.
  intros Gamma IT target X Y n name D D' Hrow HD HX HY HYrow Hnth Hconv.
  pose proof (proj1 Hrow) as HIT.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  assert (HD' : typing Gamma D' (TIDesc IT)).
  { destruct Hrow as [_ [_ Hcodes]]. apply Forall_forall with (x := (name,D')) in Hcodes;
      [exact Hcodes|eapply nth_error_In; exact Hnth]. }
  assert (Hdom : typing Gamma (TInterp IT D X) (TSort 0)) by now apply ty_interp.
  assert (Htarget : typing Gamma (TInterp IT D' X) (TSort 0)) by now apply ty_interp.
  unfold retag_handler. eapply arrow_intro_fresh; [exact weaken|exact Hdom|exact HY|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (TInterp IT D X))
    (TPair (subst (TVar y) (fresh [enum_position n]) (enum_position n))
      (if fresh [enum_position n] =? fresh [enum_position n] then TVar y else TVar (fresh [enum_position n]))) Y).
  rewrite Nat.eqb_refl, subst_fresh by (rewrite enum_position_closed; cbn; tauto).
  eapply ty_conv with (A := TInterp IT (row_code IT target) X).
  - eapply row_injection_typing; [exact weaken| | |exact Hnth|].
    + eapply row_input_weaken; eassumption.
    + eapply weaken; eassumption.
    + eapply ty_conv with (A := TInterp IT D X).
      * apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
      * eapply weaken; eassumption.
      * exact Hconv.
  - eapply weaken; eassumption.
  - now apply cv_sym.
Qed.

Theorem row_handlers_from_rules : forall Gamma IT X Y target source handlers,
  row_input Gamma IT source -> row_input Gamma IT target ->
  typing Gamma X (Family IT) -> typing Gamma Y (TSort 0) ->
  conv Y (TInterp IT (row_code IT target) X) ->
  row_handlers Gamma IT X Y target source handlers ->
  Forall2 (fun entry h => typing Gamma h (arrow (TInterp IT (snd entry) X) Y)) source handlers.
Proof.
  intros Gamma IT X Y target source handlers Hsource Htarget HX HY Hconv Hhandlers.
  revert Hsource. induction Hhandlers; intro Hsource; [constructor| |].
  - destruct (row_input_cons _ _ _ _ _ Hsource) as [Htail HD]. constructor.
    + eapply retag_handler_typing with (target := target); eassumption.
    + now apply IHHhandlers.
  - destruct (row_input_cons _ _ _ _ _ Hsource) as [Htail HD]. constructor.
    + eapply dead_handler_typing; [exact weaken| |exact HY|].
      * apply ty_interp; [exact (proj1 Hsource)|exact HD|exact HX].
      * now apply dead_typed.
    + now apply IHHhandlers.
Qed.

Theorem description_subtyping_from_rules : forall Gamma IT D D' X q,
  desc_sub Gamma IT D D' X q ->
  typing Gamma q (arrow (TInterp IT D X) (TInterp IT D' X)).
Proof.
  intros Gamma IT D D' X q Hsub. destruct Hsub.
  - destruct H as [HIT [HD HX]]. destruct H0 as [_ [HD' _]].
    eapply identity_for_typing; [now apply ty_interp|now apply ty_interp|].
    apply cv_compatible, cp_TInterp; auto using cv_refl.
  - destruct (dead_input _ _ _ _ _ H) as [HIT [HD HX]].
    destruct H0 as [_ [HD' _]]. eapply dead_handler_typing; [exact weaken| | |now apply dead_typed];
      now apply ty_interp.
  - destruct H as [HIT [HD HX]]. destruct H0 as [_ [HD' _]].
    destruct H1 as [rs Hsource Hcode Hconv]. destruct H2 as [rt Htarget Hcode' Hconv'].
    assert (HsourceT : typing Gamma (TInterp IT D X) (TSort 0)) by now apply ty_interp.
    assert (HtargetT : typing Gamma (TInterp IT D' X) (TSort 0)) by now apply ty_interp.
    eapply ty_conv with (A := arrow (TInterp IT (row_code IT rs) X) (TInterp IT D' X)).
    + apply row_map_typing; [exact weaken|exact Hsource|exact HX|exact HtargetT|].
      apply row_handlers_tuple; [exact weaken|exact Hsource|exact HX|exact HtargetT|].
      eapply row_handlers_from_rules; try eassumption.
      apply cv_compatible, cp_TInterp; auto using cv_refl.
    + eapply arrow_formation; eassumption.
    + apply arrow_conversion; [|apply cv_refl].
      apply cv_compatible, cp_TInterp; try apply cv_refl. now apply cv_sym.
Qed.

End CoercionTyping.
