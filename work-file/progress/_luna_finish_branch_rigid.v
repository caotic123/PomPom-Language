Require Import _glm_mueq_lift_descent_shape Progress _tmp_epstep _luna_finish_branch_erase _luna_finish_eta_sort _work_mixed_closure.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Definition branch_bad : term := branch_erase bad_t.

Lemma branch_bad_def : branch_bad =
  TSnd (TLam (TApp
    (TPair (TMuS (TLam (TFst (TApp (TVar 1) (TVar 0))))) (TSort 0))
    (TVar 0))).
Proof. reflexivity. Qed.

Lemma branch_bad_pstep_id : forall u, pstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. rewrite branch_bad_def in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : pstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TPair (TMuS _) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TMuS _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TLam (TFst _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TFst _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TVar _) (TVar _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TVar _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  reflexivity.
Qed.

Lemma lift_var_neq : forall k g, lift 1 k g <> TVar k.
Proof.
  intros k g H. destruct g; try discriminate H.
  change ((if Nat.ltb n k then TVar n else TVar (S n)) = TVar k) in H.
  destruct (Nat.ltb n k) eqn:E.
  - apply Nat.ltb_lt in E. injection H as Hn. lia.
  - apply Nat.ltb_ge in E. injection H as Hn. lia.
Qed.

Lemma lift_pair_neq : forall f,
    lift 1 0 f <> TPair (TMuS (TLam (TFst (TApp (TVar 1) (TVar 0))))) (TSort 0).
Proof.
  intros f H.
  destruct (lift_shape_pair_glm _ _ _ _ H) as [a [b [_ [Ha _]]]].
  destruct (lift_shape_mus_glm _ _ _ (eq_sym Ha)) as [s [_ Hs]].
  destruct (lift_shape_lam_glm _ _ _ (eq_sym Hs)) as [body [_ Hb]].
  destruct (lift_shape_fst_glm _ _ _ (eq_sym Hb)) as [app [_ Happ]].
  destruct (lift_shape_app_glm _ _ _ _ (eq_sym Happ)) as [v [w [_ [Hv _]]]].
  exact (lift_var_neq 1 v (eq_sym Hv)).
Qed.

Lemma branch_bad_epstep_id : forall u, epstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. rewrite branch_bad_def in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : epstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TPair (TMuS _) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TMuS _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TLam (TFst _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TFst _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TApp (TVar _) (TVar _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TVar _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  all: try reflexivity.
  all: exfalso; match goal with
  | H : TPair _ _ = lift 1 0 ?f |- _ => exact (lift_pair_neq f (eq_sym H))
  | H : lift 1 0 ?f = TPair _ _ |- _ => exact (lift_pair_neq f H)
  end.
Qed.

Lemma branch_bad_rtc_pstep_id : forall u, rtc pstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_pstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.

Lemma branch_bad_rtc_epstep_id : forall u, rtc epstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_epstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.

Lemma branch_bad_cstep_id : forall u, cstep branch_bad u -> u = branch_bad.
Proof. intros u H; inversion H; subst; [eapply branch_bad_rtc_pstep_id|eapply branch_bad_rtc_epstep_id]; eassumption. Qed.

Lemma branch_bad_rtc_cstep_id : forall u, rtc cstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_cstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.

Print Assumptions branch_bad_rtc_cstep_id.
