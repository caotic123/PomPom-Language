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
  - subst u; unfold alpha_equiv, alpha_eqb in H0. destruct t;
      cbn [alpha_eqb_in] in H0; try discriminate.
    repeat rewrite Bool.andb_true_iff in H0. destruct H0 as [[HI HF] HG].
    destruct (IHtyping _ _ _ eq_refl) as [HIT [HFT [HGT Hconv]]].
    destruct (close_components_alpha _ _ _ _ _ _ _ HIT HFT HGT HI HF HG)
      as [HJT [HF0 HG0]]. repeat split; try assumption.
    eapply cv_trans; [|exact Hconv].
    apply constant_pi_convert; try solve [cbn;tauto].
    + apply cv_sym, cv_alpha;exact HI.
    + apply cv_refl.
  - destruct (IHtyping1 _ _ _ Heq) as [HIT [HF [HG Hconv]]].
    repeat split; try assumption. eapply cv_trans; eassumption.
  - destruct (IHtyping _ _ _ Heq) as [HIT [HF [HG Hconv]]].
    exfalso. pose proof (raw_head _ _ _ _ Hconv eq_refl eq_refl); discriminate.
  - inversion Heq; subst. repeat split; auto using cv_refl.
Qed.
Lemma typing_close_application : forall Gamma t T, typing Gamma t T -> forall IT F G i,
  t = CloseAt IT F G i -> close_input Gamma IT F G i.
Proof.
  intros Gamma t T H; induction H; intros J F0 G0 i0 Heq; try discriminate.
  - inversion Heq; subst f a.
    destruct (typing_close_head _ _ _ H0 _ _ _ eq_refl) as [HJ [HF [HG Hconv]]].
    repeat split; try assumption.
    eapply ty_conv with (A:=A); [exact H1|exact HJ|].
    eapply pi_domain_conversion. apply cv_sym; exact Hconv.
  - subst u; unfold alpha_equiv, alpha_eqb in H0.
    destruct t; cbn [alpha_eqb_in] in H0; try discriminate.
    apply Bool.andb_true_iff in H0; destruct H0 as [Hfun Hi].
    destruct t1; cbn [alpha_eqb_in] in Hfun; try discriminate.
    repeat rewrite Bool.andb_true_iff in Hfun; destruct Hfun as [[HJ HF] HG].
    destruct (IHtyping _ _ _ _ eq_refl) as [HIT [HFT [HGT Hit]]].
    destruct (close_components_alpha _ _ _ _ _ _ _ HIT HFT HGT HJ HF HG)
      as [HJT [HF0 HG0]]. repeat split; try assumption.
    eapply ty_conv; [eapply ty_alpha; [exact Hit|exact Hi]|exact HJT|now apply cv_alpha].
  - eapply IHtyping1; exact Heq.
  - eapply IHtyping; exact Heq.
Qed.

Lemma typing_in_regularity : forall Gamma t A, typing Gamma t A -> forall xs,
  t = TIn xs -> type_wf Gamma A.
Proof.
  intros Gamma t A H; induction H; intros ys Heq; try discriminate.
  - subst u. destruct t; unfold alpha_equiv, alpha_eqb in H0;
      cbn [alpha_eqb_in] in H0; try discriminate. eapply IHtyping; reflexivity.
  - eexists; eassumption.
  - exists (S k); apply ty_sort. eapply typing_context; exact H.
  - exists 0; eapply mu_at_formation; eassumption.
  - exists 0; eapply close_at_formation; eassumption.
Qed.

Variable preserve : forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A.
Theorem canonical_close_from_rules : forall IT F G i v,
  typing empty_ctx v (CloseAt IT F G i) -> value v ->
  exists xs, v = TIn xs /\ typing empty_ctx xs (payload IT F G i).
Proof.
  intros IT F G i v Hty Hv.
  destruct (close_value_shape _ _ _ _ _ _ Hty Hv) as [xs ->].
  destruct (typing_in_regularity _ _ _ Hty _ eq_refl) as [k Hformed].
  pose proof (typing_close_application _ _ _ Hformed _ _ _ _ eq_refl) as Hinput.
  pose proof (unroll_from_weakening weaken _ _ _ _ _ _ Hinput Hty) as Hunroll.
  exists xs; split; [reflexivity|].
  eapply preserve with (t:=TApp identity xs).
  - eapply preserve; [exact Hunroll|apply red_root;reflexivity].
  - apply red_root; reflexivity.
Qed.
End TypedShapes.
