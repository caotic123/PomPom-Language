From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBBeta.
Import ListNotations.

Lemma reduction_close_at : forall IT F G i t,
  reduction (CloseAt IT F G i) t -> exists JT H K j,
  t = CloseAt JT H K j /\ rtc reduction IT JT /\ rtc reduction F H /\
  rtc reduction G K /\ rtc reduction i j.
Proof.
  intros IT F G i t Hr. unfold CloseAt in *.
  inversion Hr; subst; cbn [root_step] in *; try discriminate.
  all: try match goal with H : reduction (TClose _ _ _) _ |- _ =>
    inversion H; subst; cbn [root_step] in *; try discriminate end.
  all: eauto 10 using rtc_refl, rtc_one.
Qed.

Lemma reduces_close_at : forall IT F G i t,
  rtc reduction (CloseAt IT F G i) t -> exists JT H K j,
  t = CloseAt JT H K j /\ rtc reduction IT JT /\ rtc reduction F H /\
  rtc reduction G K /\ rtc reduction i j.
Proof.
  intros IT F G i t Hr; remember (CloseAt IT F G i) as src eqn:E; revert IT F G i E.
  induction Hr; intros IT F G i E; subst.
  - exists IT,F,G,i; repeat split; constructor.
  - destruct (reduction_close_at _ _ _ _ _ H) as [JT [J [K [j [-> [HI [HF [HG Hi]]]]]]]].
    destruct (IHHr _ _ _ _ eq_refl) as [LT [L [M [l [-> [HI' [HF' [HG' Hi']]]]]]]].
    exists LT,L,M,l; repeat split; eauto using rtc_trans.
Qed.

Lemma joined_conversion : forall a b w,
  rtc reduction a w -> rtc reduction b w -> conv a b.
Proof. intros; eapply cv_trans; [eapply reductions_conversion;eassumption|apply cv_sym;eapply reductions_conversion;eassumption]. Qed.

Lemma conversion_close_at : forall IT F G i JT H K j,
  conv (CloseAt IT F G i) (CloseAt JT H K j) ->
  conv IT JT /\ conv F H /\ conv G K /\ conv i j.
Proof.
  intros IT F G i JT H K j HC. destruct (conversion_joinable _ _ HC) as [w [Ha Hb]].
  destruct (reduces_close_at _ _ _ _ _ Ha) as [IT' [F' [G' [i' [-> [HI [HF [HG Hi]]]]]]]].
  destruct (reduces_close_at _ _ _ _ _ Hb) as [JT' [H' [K' [j' [E [HJ [HH [HK Hj]]]]]]]].
  inversion E; subst. repeat split; eauto using joined_conversion.
Qed.

Lemma payload_conversion : forall IT F G i JT H K j,
  conv IT JT -> conv F H -> conv G K -> conv i j ->
  conv (payload IT F G i) (payload JT H K j).
Proof.
  intros. unfold payload, carrier.
  apply cv_compatible, cp_TInterp; auto using cv_compatible, compatible.
Qed.

Theorem close_payload_generation : forall Gamma t T, typing Gamma t T ->
  forall IT F G i xs, t = TIn xs -> conv T (CloseAt IT F G i) ->
  type_wf Gamma (payload IT F G i) -> typing Gamma xs (payload IT F G i).
Proof.
  intros Gamma t T H; induction H; intros JT FF GG ii ys Heq0 HC HF; try discriminate.
  - eapply IHtyping1; [exact Heq0|eapply cv_trans;eassumption|exact HF].
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - inversion Heq0; subst. destruct (conversion_close_at _ _ _ _ _ _ _ _ HC) as [HI [HFF [HGG Hii]]].
    eapply convert_type; [eassumption|exact HF|apply payload_conversion;assumption].
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.
