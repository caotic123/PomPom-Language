(* GLM worker 2 — the atomic mu^S-application case of epstep-vs-mueq.        *)
(*                                                                           *)
(*   1. epstep_muapp_shape : a single epstep out of a stuck mu^S             *)
(*      application preserves the exact outer application shape, and the     *)
(*      signature/index components step by epstep as well (epstep is a       *)
(*      pure parallel eta congruence with no beta/computation roots, so      *)
(*      this is direct inversion).                                           *)
(*   2. epstep_conv (_mut, with epbranches) : epstep embeds into conv.       *)
(*   3. me_muapp_epstep_l / _r : the opaque mueq class case [me_muapp]       *)
(*      commutes with a one-step epstep on the left / right — the reduced    *)
(*      term keeps the mu-application shape, so [me_muapp] can be            *)
(*      reconstructed, joining the component epsteps through conv via       *)
(*      cv_sym / cv_trans and epstep_conv.                                   *)
(*   4. me_muapp_rtc_epstep_r : the oriented commuting-diagram corollary     *)
(*      with a reflexive-transitive epstep sequence on the right.            *)

Require Import Progress.
Require Import _tmp_epstep _luna_mueq.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Ltac cv_congr :=
  eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma, cv_pair,
    cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi, cv_switch,
    cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
    cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
    cv_list, cv_lnil, cv_lcons.

(* ========================================================================== *)
(*  1. epstep preserves the exact outer stuck mu^S application shape          *)
(* ========================================================================== *)

(* One epstep out of TApp (TMuS S) i can only be the application congruence
   applied to the mu^S congruence on the head: eps_eta has a TLam source and
   no other rule produces a TApp or TMuS head. *)
Lemma epstep_muapp_shape :
    forall S i t', epstep (TApp (TMuS S) i) t' ->
      exists S' i', t' = TApp (TMuS S') i' /\ epstep S S' /\ epstep i i'.
Proof.
  intros S i t' H.
  inversion H; subst; clear H.
  (* eps_app : epstep (TMuS S) f' with epstep i a' *)
  match goal with
  | Hf : epstep (TMuS S) ?f' |- _ => inversion Hf; subst; clear Hf
  end.
  (* eps_mus : f' = TMuS S' *)
  eexists; eexists. split; [reflexivity |].
  split; assumption.
Qed.

(* ========================================================================== *)
(*  2. epstep embeds into conv                                                *)
(* ========================================================================== *)

(* Mutuality with epbranches: generalized over a branch prefix so
   cv_case_br can act on the first differing cell (same shape as the
   mueq_conv_mut argument of _luna_mueq). *)
Lemma epstep_conv_mut :
    (forall t u, epstep t u -> conv t u) /\
    (forall bs bs', epbranches bs bs' -> forall pre M Q,
        conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply epstep_epbranches_ind; intros;
    try solve [cv_congr].
  - (* eps_case : branches first (empty prefix), then head/motive *)
    eapply cv_trans.
    + apply (H1 [] M Q).
    + apply cv_case; [exact H | exact H0].
  - (* eps_eta : cv_eta composed with the induction hypothesis *)
    eapply cv_trans; [apply cv_eta | assumption].
  - (* epbs_cons : replace the first cell with cv_case_br, then the tail *)
    eapply cv_trans.
    + apply cv_case_br; [exact H | exact H0].
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma epstep_conv : forall t u, epstep t u -> conv t u.
Proof. exact (proj1 epstep_conv_mut). Qed.

Lemma epbranches_case_conv : forall bs bs',
    epbranches bs bs' -> forall M Q,
      conv (TCase M Q bs) (TCase M Q bs').
Proof.
  intros bs bs' H M Q.
  exact (proj2 epstep_conv_mut bs bs' H [] M Q).
Qed.

(* ========================================================================== *)
(*  3. the opaque me_muapp case commutes with epstep                          *)
(* ========================================================================== *)

(* Left orientation: the left side of the conv reduces by one epstep. *)
Lemma me_muapp_epstep_l :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      epstep (TApp (TMuS S1) i1) t' ->
      mueq t' (TApp (TMuS S2) i2).
Proof.
  intros S1 i1 S2 i2 t' Hconv Hstep.
  destruct (epstep_muapp_shape _ _ _ Hstep) as [S1' [i1' [Heq [HS Hi]]]].
  rewrite Heq.
  apply me_muapp.
  apply (cv_trans (u := TApp (TMuS S1) i1)).
  + apply cv_app.
    * apply cv_sym. apply cv_mus. apply epstep_conv. assumption.
    * apply cv_sym. apply epstep_conv. assumption.
  + exact Hconv.
Qed.

(* Right orientation: the right side of the conv reduces by one epstep. *)
Lemma me_muapp_epstep_r :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      epstep (TApp (TMuS S2) i2) t' ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros S1 i1 S2 i2 t' Hconv Hstep.
  destruct (epstep_muapp_shape _ _ _ Hstep) as [S2' [i2' [Heq [HS Hi]]]].
  rewrite Heq.
  apply me_muapp.
  apply (cv_trans (u := TApp (TMuS S2) i2)).
  + exact Hconv.
  + apply cv_app.
    * apply cv_mus. apply epstep_conv. assumption.
    * apply epstep_conv. assumption.
Qed.

(* ========================================================================== *)
(*  4. commuting-diagram corollary: rtc epstep on the right                   *)
(* ========================================================================== *)

(* General form, inducting on the epstep sequence out of a mu^S application;
   each intermediate regains the mu-application shape by
   epstep_muapp_shape, so the one-step right orientation re-applies. *)
Lemma me_muapp_rtc_epstep_r_gen :
    forall t0 t', rtc epstep t0 t' -> forall S1 i1 S2 i2,
      t0 = TApp (TMuS S2) i2 ->
      conv (TApp (TMuS S1) i1) t0 ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros t0 t' Hrtc.
  induction Hrtc as [t0 | x y z Hstep Hrtc IH]; intros S1 i1 S2 i2 Heq0 Hconv.
  - subst t0. apply me_muapp. exact Hconv.
  - subst x.
    destruct (epstep_muapp_shape _ _ _ Hstep) as [S2' [i2' [Hy [HS Hi]]]].
    apply IH with (S2 := S2') (i2 := i2').
    + exact Hy.
    + apply mueq_conv.
      apply (me_muapp_epstep_r S1 i1 S2 i2).
      * assumption.
      * assumption.
Qed.

Corollary me_muapp_rtc_epstep_r :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      rtc epstep (TApp (TMuS S2) i2) t' ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros S1 i1 S2 i2 t' Hconv Hrtc.
  exact (me_muapp_rtc_epstep_r_gen _ _ Hrtc S1 i1 S2 i2 eq_refl Hconv).
Qed.
