(* Principal constructor views and conversion injectivity. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBInductionBeta.
Import ListNotations.

Section UnaryConversion.
Variable C : term -> term.
Hypothesis redC : forall A t, reduction (C A) t -> exists B, t = C B /\ rtc reduction A B.
Hypothesis injC : forall A B, C A = C B -> A = B.
Lemma reduces_unary : forall A t, rtc reduction (C A) t -> exists B, t = C B /\ rtc reduction A B.
Proof.
  intros A t H; remember (C A) as src eqn:E; revert A E.
  induction H; intros A E; subst.
  - exists A; split; auto using rtc_refl.
  - destruct (redC _ _ H) as [B [-> HB]].
    destruct (IHrtc _ eq_refl) as [D [-> HD]]. exists D; split; eauto using rtc_trans.
Qed.
Lemma conversion_unary : forall A B, conv (C A) (C B) -> conv A B.
Proof.
  intros A B H. destruct (conversion_joinable _ _ H) as [w [HA HB]].
  destruct (reduces_unary _ _ HA) as [A' [-> HA']].
  destruct (reduces_unary _ _ HB) as [B' [E HB']].
  apply injC in E; subst. eauto using joined_conversion.
Qed.
End UnaryConversion.

Lemma reduction_idesc : forall A t, reduction (TIDesc A) t ->
  exists B, t = TIDesc B /\ rtc reduction A B.
Proof. intros A t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto using rtc_one. Qed.
Lemma conversion_idesc : forall A B, conv (TIDesc A) (TIDesc B) -> conv A B.
Proof. apply (conversion_unary TIDesc reduction_idesc); intros; congruence. Qed.
Lemma reduction_enumt : forall A t, reduction (TEnumT A) t ->
  exists B, t = TEnumT B /\ rtc reduction A B.
Proof. intros A t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto using rtc_one. Qed.
Lemma conversion_enumt : forall A B, conv (TEnumT A) (TEnumT B) -> conv A B.
Proof. apply (conversion_unary TEnumT reduction_enumt); intros; congruence. Qed.

Definition description_shape D :=
  match D with TIVar _ | TI1 | TIBot | TIProd _ _ | TIPi _ _ | TISig _ _ | TIChoice _ _ => True | _ => False end.
Definition description_components Gamma IT D :=
  match D with
  | TIVar i => typing Gamma i IT
  | TIProd A B => typing Gamma A (TIDesc IT) /\ typing Gamma B (TIDesc IT)
  | TIPi A D | TISig A D => typing Gamma A (TSort 0) /\ typing Gamma D (arrow A (TIDesc IT))
  | TIChoice E D => typing Gamma E TEnumU /\ typing Gamma D (arrow (TEnumT E) (TIDesc IT))
  | _ => True
  end.

Lemma description_generation : forall Gamma t T, typing Gamma t T -> description_shape t ->
  exists IT, typing Gamma IT (TSort 0) /\ conv (TIDesc IT) T /\ description_components Gamma IT t.
Proof.
  intros Gamma t T H; induction H; cbn [description_shape]; intro HS; try contradiction.
  - destruct (IHtyping1 HS) as [IT [HI [HC HD]]]. exists IT; repeat split; try assumption.
    eapply cv_trans; eassumption.
  - destruct (IHtyping HS) as [IT [HI [HC HD]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - exists IT; cbn [description_components]; repeat split; eauto using cv_refl.
  - destruct (IHtyping1 HS) as [IT [HI [HC HD]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.

Lemma arrow_formation : forall Gamma A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (arrow A B) (TSort (Nat.max j k)).
Proof. intros Gamma A B j k HA HB; apply ty_pi; [exact HA|exact (weakening _ _ _ _ _ HB HA)]. Qed.
Lemma arrow_conversion : forall A B C D,
  conv A C -> conv B D -> conv (arrow A B) (arrow C D).
Proof. intros; apply cv_compatible, cp_TPi; auto using conversion_lift. Qed.

Lemma description_inversion : forall Gamma IT D,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
  description_components Gamma IT D.
Proof.
  intros Gamma IT D HI HD.
  assert (HS : description_shape D \/ description_components Gamma IT D).
  { destruct D; cbn [description_shape description_components]; tauto. }
  destruct HS as [HS|HS]; [|exact HS].
  destruct (description_generation _ _ _ HD HS) as [JT [HJ [HC HV]]].
  apply conversion_idesc in HC.
  destruct D; cbn [description_components] in *; try exact I.
  all: try destruct HV as [HA HB]; try split; try assumption.
  all: eapply ty_conv; [eassumption|eauto using arrow_formation, ty_idesc, ty_enumt|].
  all: auto using arrow_conversion, cv_compatible, compatible, cv_refl.
Qed.
