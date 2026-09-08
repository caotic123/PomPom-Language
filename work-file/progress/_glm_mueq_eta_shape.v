Require Import Progress _luna_mueq _tmp_epstep.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

(* GLM worker 2 — root eta contraction versus mueq, conditional on lift
   descent.  The TApp-source inversion is stated honestly: the mueq class
   has the additional overlapping case [me_muapp], whose source pattern is
   TApp (TMuS S1) i1, so a TApp source inverts into a structural [me_app]
   case plus an explicitly isolated exceptional case.  The exceptional case
   triggers exactly when the source function is TMuS-headed; the final
   simulation theorem therefore carries the exact additional premise that
   the outer function (lift 1 0 f) is not TMuS-headed.  The obstruction
   lemma at the end shows this premise cannot be dropped. *)

(* Conditional lift-descent premise. *)
Definition mueq_lift1_descent_glm : Prop :=
  forall f g, mueq (lift 1 0 f) g ->
    exists g0, g = lift 1 0 g0 /\ mueq f g0.

(* ========================================================================== *)
(*  Small inversion lemmas                                                    *)
(* ========================================================================== *)

(* 1. A TLam source can only come from me_lam (me_muapp has a TApp source,
      so inversion discards it). *)
Lemma mueq_lam_inv_glm : forall b t,
    mueq (TLam b) t -> exists b', t = TLam b' /\ mueq b b'.
Proof.
  intros b t H. inversion H; subst.
  exists b'. split; [reflexivity | assumption].
Qed.

(* 3. A TVar 0 source can only come from me_var. *)
Lemma mueq_var0_inv_glm : forall t, mueq (TVar 0) t -> t = TVar 0.
Proof.
  intros t H. inversion H; subst. reflexivity.
Qed.

(* 2. A TApp source forces a TApp target and component mueqs — with the
      me_muapp exception isolated explicitly: it applies only when the
      source function is TMuS-headed, and then the whole pair of
      applications must be conv-related. *)
Lemma mueq_tapp_inv_glm : forall f1 a1 t,
    mueq (TApp f1 a1) t ->
    (exists S1 S2 i1 i2,
        f1 = TMuS S1 /\ a1 = i1 /\ t = TApp (TMuS S2) i2 /\
        conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2))
    \/ (exists f2 a2, t = TApp f2 a2 /\ mueq f1 f2 /\ mueq a1 a2).
Proof.
  intros f1 a1 t H. inversion H; subst.
  - right. exists f', a'. split; [reflexivity | split; assumption].
  - left. exists S1, S2, a1, i2.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity | assumption].
Qed.

(* The exact additional premise that excludes the me_muapp exception:
   the source function is not TMuS-headed. *)
Lemma mueq_tapp_inv_nomu_glm : forall f1 a1 t,
    (forall S1, f1 <> TMuS S1) ->
    mueq (TApp f1 a1) t ->
    exists f2 a2, t = TApp f2 a2 /\ mueq f1 f2 /\ mueq a1 a2.
Proof.
  intros f1 a1 t Hnomu H.
  destruct (mueq_tapp_inv_glm f1 a1 t H)
    as [[S1 [S2 [i1 [i2 [Hf1 [Ha1 [Ht Hconv]]]]]]] | Happ].
  - exfalso. apply (Hnomu S1). exact Hf1.
  - exact Happ.
Qed.

(* ========================================================================== *)
(*  Outer function shape                                                      *)
(* ========================================================================== *)

(* Discharge attempt, outer-shape half: me_muapp fires only when the outer
   function is TMuS-headed, and lift preserves heads, so this is exactly
   when f itself is TMuS-headed. *)
Lemma lift1_tmus_head_inv_glm : forall f S1,
    lift 1 0 f = TMuS S1 -> exists S0, f = TMuS S0.
Proof.
  intros f S1 H. destruct f; cbn [lift] in H.
  all: try discriminate.
  all: try (destruct (Nat.ltb n 0); discriminate).
  exists f. reflexivity.
Qed.

(* Discharge attempt, descent half: descent cannot fire on the eta-expanded
   application, because TApp (lift 1 0 f) (TVar 0) is not in the image of
   lift 1 0 — lift 1 0 never produces TVar 0.  Hence the exceptional
   me_muapp subcase cannot be discharged from the descent hypothesis. *)
Lemma lift1_zero_no_var0_glm : forall t, lift 1 0 t <> TVar 0.
Proof.
  intros t H. destruct t; cbn [lift] in H; discriminate.
Qed.

(* ========================================================================== *)
(*  rtc epstep wrappers                                                       *)
(* ========================================================================== *)

Lemma epstep_rtc_one_glm : forall a b, epstep a b -> rtc epstep a b.
Proof.
  intros a b H. eapply rtc_step; [exact H | apply rtc_refl].
Qed.

Lemma epstep_rtc_refl_glm : forall a, rtc epstep a a.
Proof. intros a. apply rtc_refl. Qed.

Lemma epstep_rtc_trans_glm : forall a b c,
    rtc epstep a b -> rtc epstep b c -> rtc epstep a c.
Proof. intros a b c Hab Hbc. eapply rtc_trans; eassumption. Qed.

(* ========================================================================== *)
(*  Root eta contraction versus mueq, conditional on lift descent             *)
(* ========================================================================== *)

(* The eta-root simulation.  Besides the lift-descent hypothesis, the exact
   additional premise is stated explicitly: the outer function lift 1 0 f
   is not TMuS-headed, which is precisely what rules out the exceptional
   me_muapp case of the TApp inversion.  Dropping it falsifies the theorem
   (see mueq_eta_muapp_obstruction_glm below). *)
Theorem mueq_eta_root_sim_from_lift_descent_glm :
    mueq_lift1_descent_glm ->
    forall f u,
      mueq (TLam (TApp (lift 1 0 f) (TVar 0))) u ->
      (forall S1, lift 1 0 f <> TMuS S1) ->
      exists u', epstep u u' /\ mueq f u'.
Proof.
  intros Hd f u H Hnomu.
  apply mueq_lam_inv_glm in H. destruct H as [b' [Hu Hb']]. subst u.
  destruct (mueq_tapp_inv_glm (lift 1 0 f) (TVar 0) b' Hb')
    as [[S1 [S2 [i1 [i2 [Hf [Hi1 [Ht Hconv]]]]]]]
        | [f2 [a2 [Ht [Hff Haa]]]]].
  - (* exceptional me_muapp case: excluded by the exact additional premise *)
    exfalso. apply (Hnomu S1). exact Hf.
  - (* structural me_app case *)
    apply mueq_var0_inv_glm in Haa. subst a2.
    destruct (Hd f f2 Hff) as [g0 [Hg0 Hmg0]]. subst f2. subst b'.
    exists g0. split.
    + apply (eps_eta g0 g0). apply epstep_refl.
    + exact Hmg0.
Qed.

Corollary mueq_eta_root_sim_rtc_from_lift_descent_glm :
    mueq_lift1_descent_glm ->
    forall f u,
      mueq (TLam (TApp (lift 1 0 f) (TVar 0))) u ->
      (forall S1, lift 1 0 f <> TMuS S1) ->
      exists u', rtc epstep u u' /\ mueq f u'.
Proof.
  intros Hd f u H Hnomu.
  destruct (mueq_eta_root_sim_from_lift_descent_glm Hd f u H Hnomu)
    as [u' [Hep Hm]].
  exists u'. split.
  - apply epstep_rtc_one_glm. exact Hep.
  - exact Hm.
Qed.

(* ========================================================================== *)
(*  The obstruction: the additional premise is exact, not decorative          *)
(* ========================================================================== *)

(* A variable is conv-related to its beta-expansion. *)
Lemma conv_var_beta_exp_glm : forall k,
    conv (TVar k) (TApp (TLam (TVar 0)) (TVar k)).
Proof.
  intros k. apply cv_sym. eapply cv_step.
  apply (st_beta (TVar 0) (TVar k)).
Qed.

(* Dropping the additional premise falsifies the simulation: for f := TMuS X
   the mueq hypothesis holds through me_lam + me_muapp (the conv premise of
   me_muapp is satisfied by the beta-expansion above on the index), yet no
   u' exists — any epstep out of the TLam keeps the TLam (eps_lam), which
   can never be mueq to a TMuS-headed f, or is eps_eta, whose source shape
   forces the index to be TVar 0.  So the me_muapp exception is a genuine
   obstruction, not a proof artifact. *)
Lemma mueq_eta_muapp_obstruction_glm : forall X,
    mueq (TLam (TApp (lift 1 0 (TMuS X)) (TVar 0)))
         (TLam (TApp (TMuS (lift 1 0 X)) (TApp (TLam (TVar 0)) (TVar 0)))) /\
    ~ (exists u',
         epstep (TLam (TApp (TMuS (lift 1 0 X))
                            (TApp (TLam (TVar 0)) (TVar 0)))) u' /\
         mueq (TMuS X) u').
Proof.
  intros X. split.
  - apply (me_lam (TApp (TMuS (lift 1 0 X)) (TVar 0))
                  (TApp (TMuS (lift 1 0 X)) (TApp (TLam (TVar 0)) (TVar 0)))).
    apply (me_muapp (lift 1 0 X) (lift 1 0 X) (TVar 0)
                    (TApp (TLam (TVar 0)) (TVar 0))).
    apply cv_app; [apply cv_refl | apply conv_var_beta_exp_glm].
  - intros [u' [Hstep Hm]]. inversion Hstep; subst. inversion Hm.
Qed.

Print Assumptions mueq_lam_inv_glm.
Print Assumptions mueq_var0_inv_glm.
Print Assumptions mueq_tapp_inv_glm.
Print Assumptions mueq_tapp_inv_nomu_glm.
Print Assumptions lift1_tmus_head_inv_glm.
Print Assumptions lift1_zero_no_var0_glm.
Print Assumptions epstep_rtc_one_glm.
Print Assumptions epstep_rtc_refl_glm.
Print Assumptions epstep_rtc_trans_glm.
Print Assumptions mueq_eta_root_sim_from_lift_descent_glm.
Print Assumptions mueq_eta_root_sim_rtc_from_lift_descent_glm.
Print Assumptions conv_var_beta_exp_glm.
Print Assumptions mueq_eta_muapp_obstruction_glm.
