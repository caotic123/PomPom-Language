From Stdlib Require Import List Arith Bool Lia.
Require Import nameless.DBEtaSafety.

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
    tryif match goal with HC : rtc computation a ?v, HE : rtc epstep ?v c |- _ => idtac end then fail else idtac;
    let HL := fresh "HL" in assert (HL : tsize a < tsize s)
      by (cbn [tsize]; rewrite ?tsize_lift; lia);
    let v := fresh "v" in let HC := fresh "HC" in let HE' := fresh "HE" in
    destruct (IH a HL b c HS HE HP) as [v [HC HE']]; clear HL
  end.

Lemma eta_wrapper_postpose : forall f v u,
  rtc computation f v -> rtc epstep v u ->
  exists w, rtc computation (TLam (TApp (lift 1 0 f) (TVar 0))) w /\ rtc epstep w u.
Proof.
  intros f v u HC HE. exists (TLam (TApp (lift 1 0 v) (TVar 0))). split.
  - pose proof (computations_lift _ _ HC 1 0) as HL. comp_star_congr.
  - eapply rtc_step; [apply eps_eta, epstep_refl|exact HE].
Qed.

Ltac invert_data_eta H :=
  match type of H with epstep ?s _ =>
    let Hnl := fresh "Hnl" in assert (Hnl : not_lambda s = true)
      by (first [assumption | reflexivity]);
    inversion H; subst; clear H
  end.

Ltac core_developed t :=
  match goal with H : rtc computation t ?v |- _ => constr:(v) | _ =>
    lazymatch t with ?f ?a =>
      let df := core_developed f in let da := core_developed a in constr:(df da)
    | _ => constr:(t) end end.

Ltac postpone_congruence :=
  match goal with |- exists v, rtc computation ?s v /\ rtc epstep v ?u =>
    let v := core_developed s in exists v; split; [comp_star_congr|eta_star_congr]
  end.

Ltac postpone_root :=
  match goal with |- exists v, rtc computation ?s v /\ rtc epstep v ?u =>
    let w := core_developed s in
    let r := eval cbn [root_step] in (root_step w) in
    lazymatch r with Some ?v => exists v; split;
      [eapply rtc_trans with (y:=w); [comp_star_congr|apply rtc_one, cmp_root; reflexivity]
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
  exists v, rtc computation s v /\ rtc epstep v u.
Proof.
  apply (tsize_strong_ind (fun s => forall t u,
    eta_safe s = true -> epstep s t -> pstep t u ->
    exists v, rtc computation s v /\ rtc epstep v u)).
  intros s IH t u HS HE HP. inversion HE; subst; clear HE.
  all: split_safety.
  all: repeat take_postpone.
  all: try solve [eapply eta_wrapper_postpose; eassumption].
  all: inversion HP; subst; clear HP.
  all: try match goal with H : epstep ?f (TLam _) |- exists v, rtc computation (TApp ?f _) v /\ _ =>
    inversion H; subst; clear H end.
  all: split_safety.
  all: repeat (eta_invert_target; split_safety).
  all: repeat take_postpone.
  all: try (timeout 2 solve [postpone_congruence]).
  all: try (timeout 2 solve [postpone_root]).
  - assert (HL : tsize (TApp f0 a) <
        tsize (TApp (TLam (TApp (lift 1 0 f0) (TVar 0))) a))
        by (cbn [tsize]; rewrite tsize_lift; lia).
    assert (HSsmall : eta_safe (TApp f0 a) = true)
      by (cbn [eta_safe local_eta_safe]; now rewrite H8, H3).
    destruct (IH (TApp f0 a) HL (TApp (TLam b) a') (subst a'0 0 b') HSsmall
      (eps_TApp _ _ _ _ H5 H0) (ps_beta _ _ _ _ H7 H9)) as [w [HCw HEw]].
    exists w; split; [|exact HEw].
    eapply rtc_step; [apply cmp_root; cbn [root_step]; rewrite subst_eta_app; reflexivity|exact HCw].
Qed.
Print Assumptions safe_eta_pstep_postpone.
