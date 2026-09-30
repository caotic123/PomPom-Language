(* The reference indexed fixed point has the same strictly positive
   recursive-call typing argument as open closure. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDescriptionBeta.
Import ListNotations.

Lemma reduction_mu_at : forall IT D i t,
  reduction (MuAt IT D i) t -> exists JT E j,
  t = MuAt JT E j /\ rtc reduction IT JT /\ rtc reduction D E /\ rtc reduction i j.
Proof.
  intros IT D i t Hr. unfold MuAt in *.
  inversion Hr; subst; cbn [root_step] in *; try discriminate.
  all: try match goal with H : reduction (TMuI _ _) _ |- _ =>
    inversion H; subst; cbn [root_step] in *; try discriminate end.
  all: eauto 8 using rtc_refl, rtc_one.
Qed.
Lemma reduces_mu_at : forall IT D i t,
  rtc reduction (MuAt IT D i) t -> exists JT E j,
  t = MuAt JT E j /\ rtc reduction IT JT /\ rtc reduction D E /\ rtc reduction i j.
Proof.
  intros IT D i t Hr; remember (MuAt IT D i) as src eqn:E; revert IT D i E.
  induction Hr; intros IT D i E; subst.
  - exists IT,D,i; repeat split; constructor.
  - destruct (reduction_mu_at _ _ _ _ H) as [JT [J [j [-> [HI [HD Hi]]]]]].
    destruct (IHHr _ _ _ eq_refl) as [KT [K [k [-> [HI' [HD' Hi']]]]]].
    exists KT,K,k; repeat split; eauto using rtc_trans.
Qed.
Lemma conversion_mu_at : forall IT D i JT E j,
  conv (MuAt IT D i) (MuAt JT E j) -> conv IT JT /\ conv D E /\ conv i j.
Proof.
  intros IT D i JT E j HC. destruct (conversion_joinable _ _ HC) as [w [Ha Hb]].
  destruct (reduces_mu_at _ _ _ _ Ha) as [IT' [D' [i' [-> [HI [HD Hi]]]]]].
  destruct (reduces_mu_at _ _ _ _ Hb) as [JT' [E' [j' [H [HJ [HE Hj]]]]]].
  inversion H; subst. repeat split; eauto using joined_conversion.
Qed.
Lemma mu_payload_generation : forall Gamma t T, typing Gamma t T ->
  forall IT D i xs, t = TIn xs -> conv T (MuAt IT D i) ->
  type_wf Gamma (TInterp IT (TApp D i) (TMuI IT D)) ->
  typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D)).
Proof.
  intros Gamma t T H; induction H; intros JT DD ii ys Heq HC HF; try discriminate.
  - eapply IHtyping1; [exact Heq|eapply cv_trans; eassumption|exact HF].
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - inversion Heq; subst. destruct (conversion_mu_at _ _ _ _ _ _ HC) as [HI [HD Hi]].
    eapply convert_type; [eassumption|exact HF|].
    apply cv_compatible, cp_TInterp; auto using cv_compatible, compatible.
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.

Lemma mu_recursive_typing : forall Gamma IT D P st,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  typing Gamma P (motive IT (TMuI IT D)) -> typing Gamma st (mu_ind_method IT D P) ->
  typing Gamma
    (TLam (TLam (TInd (lift 2 0 IT) (lift 2 0 D)
      (lift 2 0 P) (lift 2 0 st) (TVar 1) (TVar 0))))
    (recursive_method IT (TMuI IT D) P).
Proof.
  intros Gamma IT D P st HI HD HP HS.
  pose proof (smart_mui _ _ _ HI HD) as HX.
  pose proof (weakening _ _ _ _ _ HX HI) as HX1. rewrite lift_Family in HX1.
  assert (Hv : typing (IT::Gamma) (TVar 0) (lift 1 0 IT))
    by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
  pose proof (regular_application _ _ _ _ _ HX1 Hv) as HA.
  apply recursive_method_intro; [exact HI|exact HX|].
  pose proof (weakening_two _ _ _ _ _ _ _ HI HI HA) as HI2.
  pose proof (weakening_two _ _ _ _ _ _ _ HD HI HA) as HD2.
  pose proof (weakening_two _ _ _ _ _ _ _ HP HI HA) as HP2.
  pose proof (weakening_two _ _ _ _ _ _ _ HS HI HA) as HS2.
  rewrite lift_Def in HD2. rewrite lift_motive in HP2.
  rewrite lift_mu_ind_method in HS2.
  pose proof (weakening _ _ _ _ _ Hv HA) as Hindex.
  rewrite lift_fuse_zero in Hindex by lia.
  assert (Hvalue : typing (TApp (lift 1 0 (TMuI IT D)) (TVar 0)::IT::Gamma)
    (TVar 0) (MuAt (lift 2 0 IT) (lift 2 0 D) (TVar 1))).
  { pose proof (smart_var _ 0 _ (wf_cons _ _ _ (typing_context _ _ _ HA) HA) eq_refl) as H.
    cbn [lift] in H. rewrite !lift_fuse_zero in H by lia. exact H. }
  eapply smart_ind; eassumption.
Qed.

Lemma mu_method_application : forall Gamma IT D P st i xs hs,
  typing Gamma st (mu_ind_method IT D P) -> typing Gamma i IT ->
  typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D)) ->
  typing Gamma hs (TIAll IT (TApp D i) (TMuI IT D) xs P) ->
  typing Gamma (TApp (TApp (TApp st i) xs) hs) (TApp P (TPair i (TIn xs))).
Proof.
  intros Gamma IT D P st i xs hs Hst Hi Hxs Hhs.
  pose proof (regular_application _ _ _ _ _ Hst Hi) as H1.
  cbn [mu_ind_method subst] in H1.
  rewrite ?subst_lift_prefix, ?lift_zero_id in H1 by lia.
  cbn [Nat.ltb Nat.leb Nat.eqb] in H1.
  pose proof (regular_application _ _ _ _ _ H1 Hxs) as H2.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H2.
  rewrite ?subst_lift_prefix, ?subst_lift_zero, ?lift_zero_id in H2 by lia.
  pose proof (regular_application _ _ _ _ _ H2 Hhs) as H3.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H3.
  now rewrite ?subst_lift_prefix, ?subst_lift_zero, ?lift_zero_id in H3 by lia.
Qed.

Theorem ind_beta : forall Gamma IT D P st i xs,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  typing Gamma P (motive IT (TMuI IT D)) -> typing Gamma st (mu_ind_method IT D P) ->
  typing Gamma i IT -> typing Gamma (TIn xs) (MuAt IT D i) ->
  typing Gamma
    (TApp (TApp (TApp st i) xs)
      (THyps IT (TApp D i) (TMuI IT D) P
        (TLam (TLam (TInd (lift 2 0 IT) (lift 2 0 D)
          (lift 2 0 P) (lift 2 0 st) (TVar 1) (TVar 0)))) xs))
    (TApp P (TPair i (TIn xs))).
Proof.
  intros Gamma IT D P st i xs HI HD HP Hst Hi Hx.
  assert (Hxs : typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D))).
  { eapply mu_payload_generation; [exact Hx|reflexivity|apply cv_refl|].
    exists 0; apply ty_interp; eauto using def_application, smart_mui. }
  eapply mu_method_application; try eassumption.
  eapply smart_hyps; eauto using def_application, smart_mui, mu_recursive_typing.
Qed.
