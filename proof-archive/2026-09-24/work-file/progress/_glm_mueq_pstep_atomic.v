(* GLM worker 3 — the atomic mu^S-application case of pstep-vs-mueq.         *)
(*                                                                           *)
(*   1. pstep_muapp_shape : a single pstep out of a stuck mu^S application    *)
(*      preserves the exact outer application shape, and the signature/index  *)
(*      components step by pstep as well.  The only pstep rule whose source   *)
(*      is an application is the application congruence (ps_beta needs a TLam *)
(*      head, and no root contraction has a TMuS head), so this is direct     *)
(*      inversion.                                                           *)
(*   2. pstep_conv is already proved closed in Progress.v; we reuse it.       *)
(*   3. me_muapp_pstep_l / _r : the opaque mueq class case [me_muapp]         *)
(*      commutes with a one-step pstep on the left / right — the reduced      *)
(*      term keeps the mu-application shape by pstep_muapp_shape, so          *)
(*      [me_muapp] can be reconstructed, joining the component psteps         *)
(*      through conv via cv_sym / cv_trans and pstep_conv.                   *)
(*   4. me_muapp_rtc_pstep_r : the oriented commuting-diagram corollary with  *)
(*      a reflexive-transitive pstep sequence on the right (u' = u).          *)

Require Import Progress.
Require Import _luna_mueq.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. pstep preserves the exact outer stuck mu^S application shape           *)
(* ========================================================================== *)

(* One pstep out of TApp (TMuS S) i can only be the application congruence
   with the mu^S congruence on the head: ps_beta needs a TLam in function
   position, and no root contraction produces/consumes a TMuS head. *)
Lemma pstep_muapp_shape :
    forall S i t', pstep (TApp (TMuS S) i) t' ->
      exists S' i', t' = TApp (TMuS S') i' /\ pstep S S' /\ pstep i i'.
Proof.
  intros S i t' H.
  inversion H; subst; clear H.
  (* ps_app : pstep (TMuS S) f' with pstep i a' *)
  match goal with
  | Hf : pstep (TMuS S) ?f' |- _ => inversion Hf; subst; clear Hf
  end.
  (* ps_mus : f' = TMuS S' *)
  eexists; eexists. split; [reflexivity |].
  split; assumption.
Qed.

(* ========================================================================== *)
(*  2. pstep embeds into conv (reused closed from Progress.v)                 *)
(* ========================================================================== *)

Lemma pstep_conv_closed : forall t u, pstep t u -> conv t u.
Proof. exact pstep_conv. Qed.

(* ========================================================================== *)
(*  3. the opaque me_muapp case commutes with pstep                           *)
(* ========================================================================== *)

(* Left orientation: the left side of the conv reduces by one pstep. *)
Lemma me_muapp_pstep_l :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      pstep (TApp (TMuS S1) i1) t' ->
      mueq t' (TApp (TMuS S2) i2).
Proof.
  intros S1 i1 S2 i2 t' Hconv Hstep.
  destruct (pstep_muapp_shape _ _ _ Hstep) as [S1' [i1' [Heq [HS Hi]]]].
  rewrite Heq.
  apply me_muapp.
  apply (cv_trans (u := TApp (TMuS S1) i1)).
  - apply cv_app.
    + apply cv_sym. apply cv_mus. apply pstep_conv_closed. assumption.
    + apply cv_sym. apply pstep_conv_closed. assumption.
  - exact Hconv.
Qed.

(* Right orientation: the right side of the conv reduces by one pstep. *)
Lemma me_muapp_pstep_r :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      pstep (TApp (TMuS S2) i2) t' ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros S1 i1 S2 i2 t' Hconv Hstep.
  destruct (pstep_muapp_shape _ _ _ Hstep) as [S2' [i2' [Heq [HS Hi]]]].
  rewrite Heq.
  apply me_muapp.
  apply (cv_trans (u := TApp (TMuS S2) i2)).
  - exact Hconv.
  - apply cv_app.
    + apply cv_mus. apply pstep_conv_closed. assumption.
    + apply pstep_conv_closed. assumption.
Qed.

(* ========================================================================== *)
(*  4. oriented commuting-diagram corollaries                                 *)
(* ========================================================================== *)

(* The instance of the simulation obligation for the [me_muapp] constructor:
   given mueq t u of the opaque mu-application class and one pstep out of t,
   the witness is u' = u itself (rtc pstep u u by reflexivity), since the
   reduced term is again mueq-related to u by me_muapp_pstep_l. *)
Corollary me_muapp_pstep_sim :
    forall S1 i1 S2 i2 t',
      mueq (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      pstep (TApp (TMuS S1) i1) t' ->
      exists u', rtc pstep (TApp (TMuS S2) i2) u' /\ mueq t' u'.
Proof.
  intros S1 i1 S2 i2 t' Hmueq Hstep.
  exists (TApp (TMuS S2) i2).
  split.
  - apply rtc_refl.
  - apply me_muapp_pstep_l with (S1 := S1) (i1 := i1).
    + apply mueq_conv. exact Hmueq.
    + exact Hstep.
Qed.

(* General form, inducting on the pstep sequence out of a mu^S application;
   each intermediate regains the mu-application shape by pstep_muapp_shape,
   so the one-step right orientation re-applies. *)
Lemma me_muapp_rtc_pstep_r_gen :
    forall t0 t', rtc pstep t0 t' -> forall S1 i1 S2 i2,
      t0 = TApp (TMuS S2) i2 ->
      conv (TApp (TMuS S1) i1) t0 ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros t0 t' Hrtc.
  induction Hrtc as [t0 | x y z Hstep Hrtc IH]; intros S1 i1 S2 i2 Heq0 Hconv.
  - subst t0. apply me_muapp. exact Hconv.
  - subst x.
    destruct (pstep_muapp_shape _ _ _ Hstep) as [S2' [i2' [Hy [HS Hi]]]].
    apply IH with (S2 := S2') (i2 := i2').
    + exact Hy.
    + apply mueq_conv.
      apply (me_muapp_pstep_r S1 i1 S2 i2).
      * assumption.
      * assumption.
Qed.

Corollary me_muapp_rtc_pstep_r :
    forall S1 i1 S2 i2 t',
      conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
      rtc pstep (TApp (TMuS S2) i2) t' ->
      mueq (TApp (TMuS S1) i1) t'.
Proof.
  intros S1 i1 S2 i2 t' Hconv Hrtc.
  exact (me_muapp_rtc_pstep_r_gen _ _ Hrtc S1 i1 S2 i2 eq_refl Hconv).
Qed.

(* Print assumptions on every target. *)
Print Assumptions pstep_muapp_shape.
Print Assumptions pstep_conv_closed.
Print Assumptions me_muapp_pstep_l.
Print Assumptions me_muapp_pstep_r.
Print Assumptions me_muapp_pstep_sim.
Print Assumptions me_muapp_rtc_pstep_r_gen.
Print Assumptions me_muapp_rtc_pstep_r.
