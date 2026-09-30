(* Typed reduction factors into computation followed by eta.
   This does not assume or assert general eta subject reduction. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEtaSafety.

Ltac split_safety :=
  repeat match goal with
  | H : eta_safe (lift _ _ _) = true |- _ => rewrite eta_safe_lift in H
  | H : eta_safe _ = true |- _ => progress cbn [eta_safe local_eta_safe not_lambda tests_payload] in H
  | H : not_lambda _ = true |- _ => progress cbn [not_lambda] in H
  | H : _ && _ = true |- _ => apply Bool.andb_true_iff in H; destruct H
  end; try discriminate.

Ltac take_postpone :=
  match goal with
  | IH : forall a, tsize a < tsize ?s -> forall t u,
      eta_safe a = true -> epstep a t -> pstep t u -> _,
    HE : epstep ?a ?b, HP : pstep ?b ?c, HS : eta_safe ?a = true |- _ =>
    tryif match goal with HC : pstep a ?v, HE : rtc epstep ?v c |- _ => idtac end then fail else idtac;
    let HL := fresh "HL" in assert (HL : tsize a < tsize s)
      by (cbn [tsize]; rewrite ?tsize_lift; lia);
    let v := fresh "v" in let HC := fresh "HC" in let HE' := fresh "HE" in
    destruct (IH a HL b c HS HE HP) as [v [HC HE']]; clear HL
  end.

Lemma eta_wrapper_postpose : forall f v u,
  pstep f v -> rtc epstep v u ->
  exists w, pstep (TLam (TApp (lift 1 0 f) (TVar 0))) w /\ rtc epstep w u.
Proof.
  intros f v u HC HE. exists (TLam (TApp (lift 1 0 v) (TVar 0))). split.
  - ps_congr.
  - eapply rtc_step; [apply eps_eta, epstep_refl|exact HE].
Qed.

Ltac invert_data_eta H :=
  match type of H with epstep ?s _ =>
    let Hnl := fresh "Hnl" in assert (Hnl : not_lambda s = true)
      by (first [assumption | reflexivity]);
    inversion H; subst; clear H
  end.

Ltac core_developed t :=
  match goal with H : pstep t ?v |- _ => constr:(v) | _ =>
    lazymatch t with ?f ?a =>
      let df := core_developed f in let da := core_developed a in constr:(df da)
    | _ => constr:(t) end end.

Ltac postpone_congruence :=
  match goal with |- exists v, pstep ?s v /\ rtc epstep v ?u =>
    let v := core_developed s in exists v; split; [ps_congr|eta_star_congr]
  end.

Ltac postpone_root :=
  match goal with |- exists v, pstep ?s v /\ rtc epstep v ?u =>
    let w := core_developed s in
    let r := eval cbn [root_step] in (root_step w) in
    lazymatch r with Some ?v => exists v; split;
      [unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; apply_root ltac:(ps_congr)
      |unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; eta_star_congr]
    end
  end.

Ltac eta_invert_target :=
  match goal with
  | H : epstep _ (TPair _ _) |- _ => invert_data_eta H
  | H : epstep _ TNilE |- _ => invert_data_eta H
  | H : epstep _ (TConsE _ _) |- _ => invert_data_eta H
  | H : epstep _ TEZero |- _ => invert_data_eta H
  | H : epstep _ (TESucc _) |- _ => invert_data_eta H
  | H : epstep _ TUnit |- _ => invert_data_eta H
  | H : epstep _ (TIVar _) |- _ => invert_data_eta H
  | H : epstep _ TI1 |- _ => invert_data_eta H
  | H : epstep _ TIBot |- _ => invert_data_eta H
  | H : epstep _ (TIProd _ _) |- _ => invert_data_eta H
  | H : epstep _ (TIPi _ _) |- _ => invert_data_eta H
  | H : epstep _ (TISig _ _) |- _ => invert_data_eta H
  | H : epstep _ (TIChoice _ _) |- _ => invert_data_eta H
  | H : epstep _ (TIn _) |- _ => invert_data_eta H
  end.

Theorem safe_eta_pstep_postpone : forall s t u,
  eta_safe s = true -> epstep s t -> pstep t u ->
  exists v, pstep s v /\ rtc epstep v u.
Proof.
  apply (tsize_strong_ind (fun s => forall t u,
    eta_safe s = true -> epstep s t -> pstep t u ->
    exists v, pstep s v /\ rtc epstep v u)).
  intros s IH t u HS HE HP. inversion HE; subst; clear HE.
  all: split_safety.
  all: repeat take_postpone.
  all: try solve [eapply eta_wrapper_postpose; eassumption].
  all: inversion HP; subst; clear HP.
  all: try match goal with H : epstep ?f (TLam _) |- exists v, pstep (TApp ?f _) v /\ _ =>
    inversion H; subst; clear H end.
  all: split_safety.
  all: repeat (eta_invert_target; split_safety).
  all: repeat take_postpone.
  all: try solve [postpone_congruence].
  all: try solve [postpone_root].
  - assert (HL : tsize (TApp (lift 1 0 f0) (TVar 0)) <
        tsize (TApp (TLam (TApp (lift 1 0 f0) (TVar 0))) a))
        by (cbn [tsize]; rewrite tsize_lift; lia).
    assert (HSsmall : eta_safe (TApp (lift 1 0 f0) (TVar 0)) = true)
      by (cbn [eta_safe local_eta_safe]; rewrite eta_safe_lift, H8; reflexivity).
    assert (HEsmall : epstep (TApp (lift 1 0 f0) (TVar 0))
      (TApp (lift 1 0 (TLam b)) (TVar 0))) by eta_congr.
    assert (HPsmall : pstep (TApp (lift 1 0 (TLam b)) (TVar 0)) b').
    { rewrite <- (subst_eta_beta_cancel b').
      cbn [lift]. apply ps_beta; [now apply pstep_lift|apply pstep_refl]. }
    destruct (IH _ HL _ _ HSsmall HEsmall HPsmall) as [w [HCw HEw]].
    exists (subst v 0 w). split.
    + now apply ps_beta.
    + now apply eta_star_subst.
Qed.
Print Assumptions safe_eta_pstep_postpone.

Lemma safe_etas_pstep_postpone : forall s t, rtc epstep s t ->
  eta_safe s = true -> forall u, pstep t u ->
  exists v, pstep s v /\ rtc epstep v u.
Proof.
  intros s t H; induction H; intros HS u HP.
  - exists u; split; [exact HP|constructor].
  - destruct (IHrtc (epstep_eta_safe _ _ H HS) _ HP) as [v [Hv HE]].
    destruct (safe_eta_pstep_postpone _ _ _ HS H Hv) as [w [Hw HE']].
    exists w; split; [exact Hw|eapply rtc_trans; eassumption].
Qed.

Lemma typed_reduction_postpone : forall t u, rtc reduction t u ->
  forall Gamma s T, typing Gamma s T -> rtc epstep s t ->
  exists v, rtc pstep s v /\ rtc epstep v u.
Proof.
  intros t u H; induction H; intros Gamma s T HS HE.
  - exists s; split; [constructor|exact HE].
  - destruct (reduction_parallel _ _ H) as [HP|Heta].
    + destruct (safe_etas_pstep_postpone _ _ HE (typing_eta_safe _ _ _ HS) _ HP)
        as [w [Hw Heta]].
      destruct (IHrtc Gamma w T (pstep_preservation _ _ Hw _ _ HS) Heta)
        as [v [Hv Hveta]].
      exists v; split; [eapply rtc_step; eassumption|exact Hveta].
    + apply (IHrtc Gamma s T HS).
      eapply rtc_trans; [exact HE|apply rtc_one; exact Heta].
Qed.

Theorem typed_reduction_factorization : forall Gamma t T,
  typing Gamma t T -> forall u, rtc reduction t u ->
  exists v, typing Gamma v T /\ rtc pstep t v /\ rtc epstep v u.
Proof.
  intros Gamma t T HT u HR.
  destruct (typed_reduction_postpone _ _ HR Gamma t T HT rtc_refl) as [v [HC HE]].
  exists v; split; [eapply psteps_preservation; eassumption|auto].
Qed.

Print Assumptions typed_reduction_factorization.
