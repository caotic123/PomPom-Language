(* GLM worker 2 — quotient-conversion bundle, part 1: the quotient link and  *)
(* its equational closure.                                                   *)
(*                                                                           *)
(*   qlink t u := cjoin t u \/ mueq t u                                      *)
(*   qconv      := rtc qlink                                                 *)
(*                                                                           *)
(* cjoin (confluent joinability of the combined phase) comes from            *)
(* _work_cjoin; mueq (structural conversion with opaque mu^S application)    *)
(* comes from _luna_mueq.  This part proves qlink symmetry and qconv         *)
(* reflexivity / symmetry / transitivity, and routes the non-congruence      *)
(* sources of conv into qconv: cv_step and cv_eta via cjoin (the combined    *)
(* phase carries both fstep and eta: fstep_cstep), cv_phi via me_muapp.      *)

Require Import Progress.
Require Import _work_cjoin _luna_mueq _luna_mueq_equiv.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition qlink (t u : term) : Prop := cjoin t u \/ mueq t u.

Definition qconv (t u : term) : Prop := rtc qlink t u.

(* --- link algebra --------------------------------------------------------- *)

Lemma qlink_sym : forall t u, qlink t u -> qlink u t.
Proof.
  intros t u [H | H].
  - left. apply cjoin_sym, H.
  - right. apply mueq_sym, H.
Qed.

Lemma qlink_refl : forall t, qlink t t.
Proof. intros t. left. apply cjoin_refl. Qed.

Lemma qconv_refl : forall t, qconv t t.
Proof. intros t. apply rtc_refl. Qed.

Lemma qconv_sym : forall t u, qconv t u -> qconv u t.
Proof.
  intros t u H. induction H.
  - apply rtc_refl.
  - eapply rtc_trans; [exact IHrtc | apply rtc_one, qlink_sym, H].
Qed.

Lemma qconv_trans : forall t u v, qconv t u -> qconv u v -> qconv t v.
Proof. intros t u v H1 H2. eapply rtc_trans; eassumption. Qed.

(* --- embedding the components --------------------------------------------- *)

Lemma cjoin_qconv : forall t u, cjoin t u -> qconv t u.
Proof. intros t u H. apply rtc_one. left. exact H. Qed.

Lemma mueq_qconv : forall t u, mueq t u -> qconv t u.
Proof. intros t u H. apply rtc_one. right. exact H. Qed.

(* --- the step sources of conv --------------------------------------------- *)

Lemma step_cjoin : forall t u, step t u -> cjoin t u.
Proof.
  intros t u H. exists u. split;
    [apply rtc_one, fstep_cstep, fs_step, H | apply rtc_refl].
Qed.

Lemma eta_cjoin : forall f, cjoin (TLam (TApp (lift 1 0 f) (TVar 0))) f.
Proof.
  intros f. exists f. split;
    [apply rtc_one, fstep_cstep, fs_eta | apply rtc_refl].
Qed.

Lemma step_qconv : forall t u, step t u -> qconv t u.
Proof. intros t u H. apply cjoin_qconv, step_cjoin, H. Qed.

Lemma eta_qconv : forall f, qconv (TLam (TApp (lift 1 0 f) (TVar 0))) f.
Proof. intros f. apply cjoin_qconv, eta_cjoin. Qed.

(* --- the Eqφ source of conv ------------------------------------------------ *)

(* cv_phi's conclusion is exactly an opaque mu^S application conversion, so   *)
(* it is a single mueq link.  The premise conv needed by me_muapp is          *)
(* re-derived by cv_phi from cv_phi's own premises.                           *)
Lemma phi_qconv : forall S1 S2 i Phi1 Phi2 Psi1 Psi2,
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 ->
    eval (labels (TApp S2 i)) Phi2 ->
    spine_phi S1 i Phi1 Psi1 ->
    spine_phi S2 i Phi2 Psi2 ->
    conv Psi1 Psi2 ->
    qconv (TApp (TMuS S1) i) (TApp (TMuS S2) i).
Proof.
  intros S1 S2 i Phi1 Phi2 Psi1 Psi2 Hbr He1 He2 Hs1 Hs2 Hpsi.
  apply mueq_qconv. apply me_muapp.
  eapply cv_phi; [exact Hbr | exact He1 | exact He2 | exact Hs1 | exact Hs2 | exact Hpsi].
Qed.
