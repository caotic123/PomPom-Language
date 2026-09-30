From Stdlib Require Import Bool Lia.
Require Import ActiveParallelWork.

Ltac aps_congr :=
  solve [eassumption | apply apstep_refl | apply apstep_lift; aps_congr | constructor; aps_congr].

Ltac take_active_postpone :=
  match goal with
  | IH : forall a, tsize a < tsize ?s -> forall flag t u,
      eta_safe a = true -> epstep a t -> apstep flag t u -> _,
    HE : epstep ?a ?b, HP : apstep ?flag ?b ?c, HS : eta_safe ?a = true |- _ =>
    tryif match goal with HC : apstep flag a ?v, HE : rtc epstep ?v c |- _ => idtac end then fail else idtac;
    let HL := fresh "HL" in assert (HL : tsize a < tsize s)
      by (cbn [tsize]; rewrite ?tsize_lift; lia);
    let v := fresh "v" in let HC := fresh "HC" in let HE' := fresh "HE" in
    destruct (IH a HL flag b c HS HE HP) as [v [HC HE']]; clear HL
  end.

Lemma active_eta_wrapper_postpose : forall flag f v u,
  apstep flag f v -> rtc epstep v u ->
  exists w, apstep flag (TLam (TApp (lift 1 0 f) (TVar 0))) w /\ rtc epstep w u.
Proof.
  intros flag f v u HC HE. exists (TLam (TApp (lift 1 0 v) (TVar 0))). split.
  - apply aps_TLam. rewrite <- (Bool.orb_false_r flag) at 1.
    apply aps_TApp; [now apply apstep_lift|apply apstep_refl].
  - eapply rtc_step; [apply eps_eta, epstep_refl|exact HE].
Qed.

Ltac active_developed t :=
  match goal with H : apstep _ t ?v |- _ => constr:(v) | _ =>
    lazymatch t with ?f ?a =>
      let df := active_developed f in let da := active_developed a in constr:(df da)
    | _ => constr:(t) end end.

Ltac active_postpone_congruence :=
  match goal with |- exists v, apstep ?flag ?s v /\ rtc epstep v ?u =>
    let v := active_developed s in exists v; split; [aps_congr|eta_star_congr]
  end.

Ltac active_postpone_root :=
  match goal with |- exists v, apstep ?flag ?s v /\ rtc epstep v ?u =>
    let w := active_developed s in
    let r := eval cbn [root_step] in (root_step w) in
    lazymatch r with Some ?v => exists v; split;
      [unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; apply_active_root ltac:(aps_congr)
      |unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; eta_star_congr]
    end
  end.

Theorem safe_eta_apstep_postpone : forall s flag t u,
  eta_safe s = true -> epstep s t -> apstep flag t u ->
  exists v, apstep flag s v /\ rtc epstep v u.
Proof.
  apply (tsize_strong_ind (fun s => forall flag t u,
    eta_safe s = true -> epstep s t -> apstep flag t u ->
    exists v, apstep flag s v /\ rtc epstep v u)).
  intros s IH flag t u HS HE HP. inversion HE; subst; clear HE.
  all: split_safety.
  all: repeat take_active_postpone.
  all: try solve [eapply active_eta_wrapper_postpose; eassumption].
  all: inversion HP; subst; clear HP.
  all: try match goal with H : epstep ?f (TLam _) |- exists v, apstep _ (TApp ?f _) v /\ _ =>
    inversion H; subst; clear H end.
  all: split_safety.
  all: repeat (eta_invert_target; split_safety).
  all: repeat take_active_postpone.
  all: try solve [active_postpone_congruence].
  all: try solve [active_postpone_root].
  - assert (HL : tsize (TApp (lift 1 0 f0) (TVar 0)) <
        tsize (TApp (TLam (TApp (lift 1 0 f0) (TVar 0))) a))
        by (cbn [tsize]; rewrite tsize_lift; lia).
    assert (HSsmall : eta_safe (TApp (lift 1 0 f0) (TVar 0)) = true)
      by (cbn [eta_safe local_eta_safe]; rewrite eta_safe_lift; repeat rewrite Bool.andb_true_iff; tauto).
    assert (HEsmall : epstep (TApp (lift 1 0 f0) (TVar 0))
      (TApp (lift 1 0 (TLam b)) (TVar 0))) by eta_congr.
    Show.
Abort.
