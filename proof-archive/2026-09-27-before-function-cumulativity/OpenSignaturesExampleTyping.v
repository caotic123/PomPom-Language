(* Symbolic example typing: proofs work for every context and payload type.
   Context extension is supplied as an explicit weakening premise. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Export OpenSignaturesRowTyping OpenSignaturesExamples.
Import ListNotations.

Lemma unit_signature_application : forall rs i,
  conv (TApp (unit_signature rs) i) (row_code TUnitT rs).
Proof.
  intros rs i. eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  rewrite subst_fresh; [apply cv_refl|apply fresh_not_free; cbn; auto].
Qed.

Section ExampleTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma cons_description_function : forall Gamma A,
  typing Gamma A (TSort 0) ->
  typing Gamma (TLam (fresh [A]) (TIVar TUnit)) (arrow A (TIDesc TUnitT)).
Proof.
  intros Gamma A HA. pose proof (typing_context _ _ _ HA) as Hctx.
  eapply constant_lambda_typing; [exact weaken| |exact HA| |cbn; tauto];
    auto using ty_ivar, ty_unit, ty_unitT, ty_idesc.
Qed.

Lemma cons_code_typing : forall Gamma A,
  typing Gamma A (TSort 0) -> typing Gamma (cons_code A) (TIDesc TUnitT).
Proof.
  intros Gamma A HA. apply ty_isig; [|exact HA|now apply cons_description_function].
  apply ty_unitT. eapply typing_context; exact HA.
Qed.

Lemma fork_code_typing : forall Gamma,
  wf Gamma -> typing Gamma fork_code (TIDesc TUnitT).
Proof.
  intros Gamma Hctx. apply ty_iprod; auto using ty_unitT, ty_ivar, ty_unit.
Qed.

Local Ltac concrete_row :=
  unfold row_input; split;
    [apply ty_unitT; eapply typing_context; eassumption|];
  split;
    [unfold row_names; cbn; repeat constructor; cbn; intuition discriminate|
     repeat (apply Forall_cons || apply Forall_nil); cbn;
       eauto using cons_code_typing, fork_code_typing, ty_i1, ty_unitT, typing_context].

Lemma list_rows_typing : forall Gamma A,
  typing Gamma A (TSort 0) -> row_input Gamma TUnitT (list_rows A).
Proof. intros. concrete_row. Qed.

Lemma nonempty_rows_typing : forall Gamma A,
  typing Gamma A (TSort 0) -> row_input Gamma TUnitT (nonempty_rows A).
Proof. intros. concrete_row. Qed.

Lemma tree_rows_typing : forall Gamma A,
  typing Gamma A (TSort 0) -> row_input Gamma TUnitT (tree_rows A).
Proof. intros. concrete_row. Qed.

Lemma unit_signature_typing : forall Gamma rs,
  row_input Gamma TUnitT rs -> typing Gamma (unit_signature rs) (Def TUnitT).
Proof.
  intros Gamma rs Hrows. destruct Hrows as [HIT [Hnames Hrows]].
  change (typing Gamma (TLam (fresh [TUnitT; row_code TUnitT rs]) (row_code TUnitT rs))
    (arrow TUnitT (TIDesc TUnitT))).
  eapply constant_lambda_typing; [exact weaken| |exact HIT|now apply ty_idesc|].
  - apply row_code_from_weakening; [exact weaken|repeat split; assumption].
  - apply fresh_not_free; cbn; auto.
Qed.

Theorem list_definitions_from_weakening : forall Gamma A,
  typing Gamma A (TSort 0) ->
  typing Gamma (list_def A) (Def TUnitT) /\
  typing Gamma (nonempty_def A) (Def TUnitT) /\
  typing Gamma (tree_def A) (Def TUnitT).
Proof.
  intros Gamma A HA. repeat split; apply unit_signature_typing;
    auto using list_rows_typing, nonempty_rows_typing, tree_rows_typing.
Qed.

Lemma cons_payload_typing : forall Gamma A X a xs,
  typing Gamma A (TSort 0) -> typing Gamma X (Family TUnitT) ->
  typing Gamma a A -> typing Gamma xs (TApp X TUnit) ->
  typing Gamma (TPair a xs) (TInterp TUnitT (cons_code A) X).
Proof.
  intros Gamma A X a xs HA HX Ha Hxs.
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (HIT : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (HD : typing Gamma (TLam (fresh [A]) (TIVar TUnit))
    (arrow A (TIDesc TUnitT))) by now apply cons_description_function.
  apply interp_sig_pair; try assumption.
  eapply ty_conv with (A := TInterp TUnitT (TIVar TUnit) X).
  - apply interp_variable; auto using ty_unit.
  - apply ty_interp; [exact HIT| |exact HX].
    eapply arrow_app with (A := A); eauto using ty_idesc.
  - apply cv_compatible, cp_TInterp; try apply cv_refl.
    apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Theorem nil_from_weakening : forall Gamma A,
  typing Gamma A (TSort 0) -> typing Gamma nil_value (list_type A).
Proof.
  intros Gamma A HA. destruct (list_definitions_from_weakening Gamma A HA) as [HL _].
  pose proof (typing_context _ _ _ HA) as Hctx.
  eapply close_row_constructor with (rs := list_rows A) (n := 0) (name := "nil"%string) (D := TI1).
  - exact weaken.
  - repeat split; auto using ty_unitT, ty_unit.
  - now apply list_rows_typing.
  - apply unit_signature_application.
  - reflexivity.
  - apply interp_unit; [now apply ty_unitT|apply ty_close; auto using ty_unitT].
Qed.

Theorem cons_from_weakening : forall Gamma A a xs,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma xs (list_type A) ->
  typing Gamma (cons_value a xs) (list_type A).
Proof.
  intros Gamma A a xs HA Ha Hxs.
  destruct (list_definitions_from_weakening Gamma A HA) as [HL _].
  pose proof (typing_context _ _ _ HA) as Hctx.
  eapply close_row_constructor with (rs := list_rows A) (n := 1)
    (name := "cons"%string) (D := cons_code A).
  - exact weaken.
  - repeat split; auto using ty_unitT, ty_unit.
  - now apply list_rows_typing.
  - apply unit_signature_application.
  - reflexivity.
  - apply cons_payload_typing; try assumption. apply ty_close; auto using ty_unitT.
Qed.

Theorem nonempty_cons_from_weakening : forall Gamma A a xs,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma xs (list_type A) ->
  typing Gamma (nonempty_value a xs) (nonempty_type A).
Proof.
  intros Gamma A a xs HA Ha Hxs.
  destruct (list_definitions_from_weakening Gamma A HA) as [HL [HN _]].
  pose proof (typing_context _ _ _ HA) as Hctx.
  eapply close_row_constructor with (rs := nonempty_rows A) (n := 0)
    (name := "cons"%string) (D := cons_code A).
  - exact weaken.
  - repeat split; auto using ty_unitT, ty_unit.
  - now apply nonempty_rows_typing.
  - apply unit_signature_application.
  - reflexivity.
  - apply cons_payload_typing; try assumption. apply ty_close; auto using ty_unitT.
Qed.

Theorem tree_cons_from_weakening : forall Gamma A a xs,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma xs (tree_type A) ->
  typing Gamma (cons_value a xs) (tree_type A).
Proof.
  intros Gamma A a xs HA Ha Hxs.
  destruct (list_definitions_from_weakening Gamma A HA) as [_ [_ HT]].
  pose proof (typing_context _ _ _ HA) as Hctx.
  eapply close_row_constructor with (rs := tree_rows A) (n := 1)
    (name := "cons"%string) (D := cons_code A).
  - exact weaken.
  - repeat split; auto using ty_unitT, ty_unit.
  - now apply tree_rows_typing.
  - apply unit_signature_application.
  - reflexivity.
  - apply cons_payload_typing; try assumption. apply ty_close; auto using ty_unitT.
Qed.

Theorem nonempty_widening_from_weakening : forall Gamma A,
  typing Gamma A (TSort 0) ->
  sub Gamma (nonempty_type A) (list_type A) (to_list A).
Proof.
  intros Gamma A HA.
  destruct (list_definitions_from_weakening Gamma A HA) as [HL [HN _]].
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (HIT : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hi : typing Gamma TUnit TUnitT) by now apply ty_unit.
  assert (HX : typing Gamma (carrier TUnitT (list_def A)) (Family TUnitT))
    by (apply ty_close; assumption).
  assert (HF : typing Gamma (TApp (nonempty_def A) TUnit) (TIDesc TUnitT))
    by (eapply def_application; eassumption).
  assert (HG : typing Gamma (TApp (list_def A) TUnit) (TIDesc TUnitT))
    by (eapply def_application; eassumption).
  apply su_close; try solve [repeat split; assumption].
  eapply ds_rows with (rs := nonempty_rows A) (rt := list_rows A).
  - repeat split; assumption.
  - repeat split; assumption.
  - constructor; [now apply nonempty_rows_typing|exact HF|apply unit_signature_application].
  - constructor; [now apply list_rows_typing|exact HG|apply unit_signature_application].
  - eapply rh_live with (D' := cons_code A) (n := 1);
      [reflexivity|apply cv_refl|constructor].
Qed.

End ExampleTyping.
