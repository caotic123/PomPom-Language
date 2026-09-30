From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesCanonical OpenSignaturesDataTyping.
Import ListNotations.

Section UnaryInversion.
Variable C : term -> term.
Hypothesis redC : forall a t, reduction (C a) t -> exists b, t = C b /\ reduces a b.
Hypothesis alphaC : forall a b, alpha_equiv (C a) (C b) -> alpha_equiv a b.
Lemma reduces_unary : forall a t, reduces (C a) t -> exists b, t = C b /\ reduces a b.
Proof.
  intros a t H; remember (C a) as src eqn:E; revert a E.
  induction H; intros a E; subst.
  - exists a; split; [reflexivity|constructor].
  - destruct (redC _ _ H) as [b [-> Hb]].
    destruct (IHreduces b eq_refl) as [c [-> Hc]].
    exists c; split; [reflexivity|eapply reduces_trans;eassumption].
Qed.
Lemma conv_unary : forall a b, conv (C a) (C b) -> conv a b.
Proof.
  intros a b H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_unary _ _ Hw) as [a' [-> Ha']].
  destruct (reduces_unary _ _ Hw') as [b' [-> Hb']].
  eapply joined_conv; [exact Ha'|exact Hb'|now apply alphaC].
Qed.
End UnaryInversion.

Lemma reduction_idesc : forall a t, reduction (TIDesc a) t ->
  exists b, t = TIDesc b /\ reduces a b.
Proof. intros a t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto using reduces. Qed.
Lemma conv_idesc : forall a b, conv (TIDesc a) (TIDesc b) -> conv a b.
Proof. apply (conv_unary TIDesc reduction_idesc). intros; exact H. Qed.
Lemma reduction_enum : forall a t, reduction (TEnumT a) t ->
  exists b, t = TEnumT b /\ reduces a b.
Proof. intros a t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto using reduces. Qed.
Lemma conv_enum : forall a b, conv (TEnumT a) (TEnumT b) -> conv a b.
Proof. apply (conv_unary TEnumT reduction_enum). intros; exact H. Qed.

Section BinaryInversion.
Variable C : term -> term -> term.
Hypothesis redC : forall a b t, reduction (C a b) t ->
  exists a' b', t = C a' b' /\ reduces a a' /\ reduces b b'.
Lemma reduces_binary : forall a b t, reduces (C a b) t ->
  exists a' b', t = C a' b' /\ reduces a a' /\ reduces b b'.
Proof.
  intros a b t H; remember (C a b) as src eqn:E; revert a b E.
  induction H; intros a b E; subst.
  - exists a,b; repeat split; constructor.
  - destruct (redC _ _ _ H) as [a' [b' [-> [Ha Hb]]]].
    destruct (IHreduces _ _ eq_refl) as [a'' [b'' [-> [Ha' Hb']]]].
    exists a'',b''; repeat split; eauto using reduces_trans.
Qed.
End BinaryInversion.
Lemma reduction_iprod : forall a b t, reduction (TIProd a b) t ->
  exists a' b', t = TIProd a' b' /\ reduces a a' /\ reduces b b'.
Proof. intros a b t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto 6 using reduces. Qed.
Lemma reduction_ichoice : forall a b t, reduction (TIChoice a b) t ->
  exists a' b', t = TIChoice a' b' /\ reduces a a' /\ reduces b b'.
Proof. intros a b t H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto 6 using reduces. Qed.

Lemma typing_iprod_principal : forall Gamma t T, typing Gamma t T -> forall A B,
  t = TIProd A B -> exists IT,
  typing Gamma IT (TSort 0) /\ typing Gamma A (TIDesc IT) /\
  typing Gamma B (TIDesc IT) /\ conv (TIDesc IT) T.
Proof.
  intros Gamma t T H; induction H; intros A0 B0 Heq; try discriminate.
  - subst u. unfold alpha_equiv, alpha_eqb in H0. destruct t; cbn [alpha_eqb_in] in H0; try discriminate.
    apply Bool.andb_true_iff in H0; destruct H0 as [HA HB].
    destruct (IHtyping _ _ eq_refl) as [IT [HIT [HAT [HBT Hc]]]].
    exists IT; repeat split; try assumption.
    + eapply ty_alpha; [exact HAT|exact HA].
    + eapply ty_alpha; [exact HBT|exact HB].
  - destruct (IHtyping1 _ _ Heq) as [IT [HIT [HA [HB Hc]]]].
    exists IT; repeat split; try assumption; eapply cv_trans; eassumption.
  - destruct (IHtyping _ _ Heq) as [IT [HIT [HA [HB Hc]]]].
    exfalso; pose proof (raw_head _ _ _ _ Hc eq_refl eq_refl); discriminate.
  - inversion Heq; subst. exists IT; repeat split; auto using cv_refl.
Qed.

Lemma reduces_nile : forall t, reduces TNilE t -> t = TNilE.
Proof.
  intros t H; remember TNilE as src eqn:E; induction H; subst; auto.
  inversion H; subst; cbn [root_step] in *; discriminate.
Qed.

Section TypedDescriptions.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma typing_ichoice_principal : forall Gamma t T, typing Gamma t T -> forall E D,
  t = TIChoice E D -> exists IT,
  typing Gamma IT (TSort 0) /\ typing Gamma E TEnumU /\
  typing Gamma D (arrow (TEnumT E) (TIDesc IT)) /\ conv (TIDesc IT) T.
Proof.
  intros Gamma t T H; induction H; intros E0 D0 Heq; try discriminate.
  - subst u. unfold alpha_equiv, alpha_eqb in H0. destruct t; cbn [alpha_eqb_in] in H0; try discriminate.
    apply Bool.andb_true_iff in H0; destruct H0 as [HE HD].
    destruct (IHtyping _ _ eq_refl) as [IT [HIT [HET [HDT Hc]]]].
    assert (HE0 : typing Gamma E0 TEnumU) by (eapply ty_alpha;[exact HET|exact HE]).
    exists IT; repeat split; try assumption.
    eapply ty_conv with (A:=arrow (TEnumT t1) (TIDesc IT)).
    + eapply ty_alpha; [exact HDT|exact HD].
    + apply arrow_formation; [exact weaken|now apply ty_enumt|now apply ty_idesc].
    + apply arrow_conversion; [apply cv_compatible, cp_TEnumT, cv_alpha;exact HE|apply cv_refl].
  - destruct (IHtyping1 _ _ Heq) as [IT [HIT [HE [HD Hc]]]].
    exists IT; repeat split; try assumption; eapply cv_trans; eassumption.
  - destruct (IHtyping _ _ Heq) as [IT [HIT [HE [HD Hc]]]].
    exfalso; pose proof (raw_head _ _ _ _ Hc eq_refl eq_refl); discriminate.
  - inversion Heq; subst. exists IT; repeat split; auto using cv_refl.
Qed.

Variable preserve : forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A.
Lemma typing_reduces : forall t u, reduces t u -> forall Gamma A,
  typing Gamma t A -> typing Gamma u A.
Proof. intros t u H; induction H; intros; eauto. Qed.

Lemma typed_iprod_view : forall Gamma IT D A B,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> conv D (TIProd A B) ->
  exists A' B', typing Gamma A' (TIDesc IT) /\ typing Gamma B' (TIDesc IT) /\
    conv A A' /\ conv B B' /\ conv D (TIProd A' B').
Proof.
  intros Gamma IT D A B HIT HD HC.
  destruct (raw_conversion_joinability _ _ HC) as [w [w' [HDw [Hpw' Ha]]]].
  destruct (reduces_binary TIProd reduction_iprod _ _ _ Hpw') as [A' [B' [-> [HA HB]]]].
  assert (Hprod : typing Gamma (TIProd A' B') (TIDesc IT)) by
    (eapply ty_alpha; [eapply typing_reduces; [exact HDw|exact HD]|exact Ha]).
  destruct (typing_iprod_principal _ _ _ Hprod _ _ eq_refl) as [JT [HJT [HA' [HB' Hconv]]]].
  apply conv_idesc in Hconv.
  exists A',B'; repeat split.
  - eapply ty_conv; [exact HA'|now apply ty_idesc|apply cv_compatible, cp_TIDesc;exact Hconv].
  - eapply ty_conv; [exact HB'|now apply ty_idesc|apply cv_compatible, cp_TIDesc;exact Hconv].
  - exact (reduces_conv _ _ HA).
  - exact (reduces_conv _ _ HB).
  - eapply cv_trans; [exact (reduces_conv _ _ HDw)|now apply cv_alpha].
Qed.

Lemma typed_empty_choice_view : forall Gamma IT D T,
  typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) -> conv D (TIChoice TNilE T) ->
  exists T', typing Gamma T' (arrow (TEnumT TNilE) (TIDesc IT)) /\ conv D (TIChoice TNilE T').
Proof.
  intros Gamma IT D T HIT HD HC.
  destruct (raw_conversion_joinability _ _ HC) as [w [w' [HDw [Hpw' Ha]]]].
  destruct (reduces_binary TIChoice reduction_ichoice _ _ _ Hpw') as [E' [T' [-> [HE HT]]]].
  apply reduces_nile in HE; subst E'.
  assert (Hchoice : typing Gamma (TIChoice TNilE T') (TIDesc IT)) by
    (eapply ty_alpha; [eapply typing_reduces; [exact HDw|exact HD]|exact Ha]).
  destruct (typing_ichoice_principal _ _ _ Hchoice _ _ eq_refl) as [JT [HJT [HE [HT' Hconv]]]].
  apply conv_idesc in Hconv. exists T'; split.
  - eapply ty_conv; [exact HT'| |].
    + apply arrow_formation; [exact weaken|now apply ty_enumt|now apply ty_idesc].
    + apply arrow_conversion; [apply cv_refl|apply cv_compatible, cp_TIDesc;exact Hconv].
  - eapply cv_trans; [exact (reduces_conv _ _ HDw)|now apply cv_alpha].
Qed.
End TypedDescriptions.
