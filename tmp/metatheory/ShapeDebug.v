From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesLabels OpenSignaturesDerivedTyping.
Import ListNotations.

Lemma raw_join_typed : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof. intros; now apply raw_conversion_joinability. Qed.
Lemma close_value_shape : forall Gamma IT F G i v,
  typing Gamma v (CloseAt IT F G i) -> value v -> exists xs, v = TIn xs.
Proof.
  intros Gamma IT F G i v Hty Hv.
  destruct (canonical_representation raw_join_typed _ _ _ Hty Hv) as [T [HT [Hform [Hconv HC]]]].
  destruct (canonical_type_head _ _ HC) as [h Hh].
  assert (h = h_closeapp) by (eapply raw_head; [exact Hconv|exact Hh|reflexivity]).
  subst h; inversion HC; subst; cbn [term_head] in Hh; try discriminate; eauto.
Qed.

Lemma pi_domain_conversion : forall x y A B C D,
  conv (TPi x A B) (TPi y C D) -> conv A C.
Proof.
  intros x y A B C D H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_pi _ _ _ _ Hw) as [A' [B' [-> [HA HB]]]].
  destruct (reduces_pi _ _ _ _ Hw') as [C' [D' [-> [HC HD]]]].
  change (alpha_eqb_in [] [] A' C' && alpha_eqb_in [x] [y] B' D' = true) in Ha.
  apply Bool.andb_true_iff in Ha; destruct Ha as [HAC HBD].
  eapply joined_conv; eassumption.
Qed.

Lemma constant_pi_convert : forall x y A B C D,
  ~ In x (free_vars B) -> ~ In y (free_vars D) -> conv A C -> conv B D ->
  conv (TPi x A B) (TPi y C D).
Proof.
  intros x y A B C D Hx Hy HAC HBD.
  eapply cv_trans with (u:=arrow A B).
  - apply cv_alpha, constant_pi_alpha; [exact Hx|apply fresh_not_free;cbn;auto].
  - eapply cv_trans with (u:=arrow C D).
    + now apply arrow_conversion.
    + apply cv_alpha, constant_pi_alpha; [apply fresh_not_free;cbn;auto|exact Hy].
Qed.

Section TypedShapes.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma def_conversion : forall IT JT, conv IT JT -> conv (Def IT) (Def JT).
Proof.
  intros. apply constant_pi_convert; [cbn [free_vars];apply fresh_not_free;cbn;auto|cbn [free_vars];apply fresh_not_free;cbn;auto|assumption|].
  apply cv_compatible, cp_TIDesc; assumption.
Qed.
Lemma close_components_alpha : forall Gamma IT F G JT H K,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
  alpha_equiv IT JT -> alpha_equiv F H -> alpha_equiv G K ->
  typing Gamma JT (TSort 0) /\ typing Gamma H (Def JT) /\ typing Gamma K (Def JT).
Proof.
  intros Gamma IT F G JT H K HIT HF HG HI HH HK.
  assert (HJT : typing Gamma JT (TSort 0)) by (eapply ty_alpha; eassumption).
  assert (HFH : typing Gamma H (Def IT)) by (eapply ty_alpha; [exact HF|exact HH]).
  assert (HGK : typing Gamma K (Def IT)) by (eapply ty_alpha; [exact HG|exact HK]).
  split; [exact HJT|]. split;
    (eapply ty_conv with (A:=Def IT);
      [eassumption|apply def_formation; [exact weaken|exact HJT]|apply def_conversion, cv_alpha;exact HI]).
Qed.
Lemma typing_close_head : forall Gamma t T, typing Gamma t T -> forall IT F G,
  t = TClose IT F G ->
  typing Gamma IT (TSort 0) /\ typing Gamma F (Def IT) /\ typing Gamma G (Def IT) /\
  conv (Family IT) T.
Proof.
  intros Gamma t T H; induction H; intros J F0 G0 Heq; try discriminate.
  - destruct t; cbn [alpha_equiv alpha_eqb alpha_eqb_in] in H0;
      subst u; cbn [alpha_eqb_in] in H0; try discriminate.
    repeat rewrite Bool.andb_true_iff in H0.
Show.
Abort.
End TypedShapes.
