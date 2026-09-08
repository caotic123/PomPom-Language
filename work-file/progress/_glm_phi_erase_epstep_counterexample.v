(* _glm_phi_erase_epstep_counterexample.v — GLM worker A.

   Kernel-checked counterexample to *general* epstep reflection through
   [phi_erase].  Take

       t := TLam (TApp (TMuS (TVar 0)) (TVar 0)).

   Its erasure is [TLam (TApp (TMuS TUnit) (TVar 0))], which eta-reduces via
   [eps_eta] because [TMuS TUnit = lift 1 0 (TMuS TUnit)].  Yet the original
   head [TMuS (TVar 0)] is not in the image of [lift 1 0], so [t] itself can
   never eta-step; by the inversion lemmas below the ONLY epstep reduct of
   [t] is [t] itself, and [phi_erase t] is a lambda, not [TMuS TUnit].

   Contents:
     - small inversion lemmas for epstep at rigid heads (var, TMuS, TApp,
       TLam incl. the eta case);
     - Part 1 (erased eta step): epstep (phi_erase t) (TMuS TUnit);
     - Part 2 (exact image): every epstep reduct of t is t itself;
     - Part 3 (strongest exact negation): no epstep preimage of [TMuS TUnit]
       under phi_erase, bundled with Part 1;
     - corollary: the unrestricted reflection interface
         forall t u, epstep (phi_erase t) u -> exists t', epstep t t' /\
                                               phi_erase t' = u
       is refuted.

   No axioms, no conjectures, no admits; [Print Assumptions] closes. *)

Require Import Progress.
Require Import _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(** The witness term. *)
Definition counterexample_t : term :=
  TLam (TApp (TMuS (TVar 0)) (TVar 0)).

(* -------------------------------------------------------------------------- *)
(*  Non-image of [lift 1 0] at the obstructing heads                          *)
(* -------------------------------------------------------------------------- *)

(** [lift 1 0] never produces a bare [TVar 0]: it maps [TVar n] to
    [TVar (S n)] (the [n < 0] branch is dead) and keeps every other head. *)
Lemma lift_1_0_neq_tvar0_glm : forall x, lift 1 0 x <> TVar 0.
Proof.
  destruct x; cbn; discriminate.
Qed.

(** Hence the head of the witness body, [TMuS (TVar 0)], is not an
    eta-expanded term [lift 1 0 f]. *)
Lemma lift_1_0_neq_mus_tvar0_glm : forall f, lift 1 0 f <> TMuS (TVar 0).
Proof.
  intros f H. destruct f; cbn in H; try discriminate.
  injection H; intros He. exact (lift_1_0_neq_tvar0_glm _ He).
Qed.

(* -------------------------------------------------------------------------- *)
(*  Small inversion lemmas for [epstep] at rigid heads                        *)
(*                                                                            *)
(*  [eps_eta] is the only rule whose conclusion does not share the head       *)
(*  constructor of its premise side, and its left index is always a [TLam]    *)
(*  whose body is an application of a lifted term.  So at a [TVar], [TMuS],   *)
(*  or [TApp] head the step is forced through the congruence rule, and at a   *)
(*  [TLam] head it is either [eps_lam] or exactly an eta redex.               *)
(* -------------------------------------------------------------------------- *)

Lemma epstep_tvar_inv_glm : forall n u,
    epstep (TVar n) u -> u = TVar n.
Proof.
  intros n u H. inversion H; subst; reflexivity.
Qed.

Lemma epstep_mus_inv_glm : forall s u,
    epstep (TMuS s) u -> exists s', u = TMuS s' /\ epstep s s'.
Proof.
  intros s u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma epstep_tapp_inv_glm : forall f a u,
    epstep (TApp f a) u ->
    exists f' a', u = TApp f' a' /\ epstep f f' /\ epstep a a'.
Proof.
  intros f a u H. inversion H; subst.
  do 2 eexists. repeat split; try reflexivity; eassumption.
Qed.

Lemma epstep_lam_inv_glm : forall b u,
    epstep (TLam b) u ->
    (exists b', u = TLam b' /\ epstep b b') \/
    (exists f, b = TApp (lift 1 0 f) (TVar 0) /\ epstep f u).
Proof.
  intros b u H. inversion H; subst.
  - left. eexists. split; [reflexivity | eassumption].
  - right. eexists. split; [reflexivity | eassumption].
Qed.

(* -------------------------------------------------------------------------- *)
(*  Part 1: the erased eta step                                               *)
(* -------------------------------------------------------------------------- *)

(** [phi_erase t = TLam (TApp (TMuS TUnit) (TVar 0))] is a genuine eta
    redex, since [TMuS TUnit = lift 1 0 (TMuS TUnit)]. *)
Lemma phi_erase_t_epsteps_mus_unit_glm :
    epstep (phi_erase counterexample_t) (TMuS TUnit).
Proof.
  cbn [counterexample_t phi_erase].
  apply (eps_eta (TMuS TUnit) (TMuS TUnit)).
  apply epstep_refl.
Qed.

(** The erasure itself is not the eta target. *)
Lemma phi_erase_counterexample_t_neq_mus_unit_glm :
    phi_erase counterexample_t <> TMuS TUnit.
Proof.
  intros Heq. cbn [counterexample_t phi_erase] in Heq. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Part 2: exact image — every epstep reduct of [t] is [t] itself            *)
(* -------------------------------------------------------------------------- *)

Lemma epstep_counterexample_t_inv_glm : forall t',
    epstep counterexample_t t' ->
    t' = counterexample_t.
Proof.
  intros t' H. unfold counterexample_t in *.
  destruct (epstep_lam_inv_glm _ _ H) as [[b' [Ht' Hb]] | [f [Hb Hf]]].
  - (* eps_lam: the body TApp (TMuS (TVar 0)) (TVar 0) steps by eps_app,
       whose components are rigid: TVar 0 refl and TMuS (TVar 0) refl. *)
    subst t'. f_equal. f_equal.
    destruct (epstep_tapp_inv_glm _ _ _ Hb) as [g [a' [Hb' [Hg Ha]]]].
    subst b'. f_equal. f_equal.
    + destruct (epstep_mus_inv_glm _ _ Hg) as [s' [Hg' Hs]].
      subst g. f_equal. exact (epstep_tvar_inv_glm _ _ Hs).
    + exact (epstep_tvar_inv_glm _ _ Ha).
  - (* eps_eta: would force TMuS (TVar 0) = lift 1 0 f — impossible. *)
    exfalso.
    assert (Hhead : TMuS (TVar 0) = lift 1 0 f) by congruence.
    apply (lift_1_0_neq_mus_tvar0_glm f). symmetry. exact Hhead.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Part 3: absence of a matching epstep preimage, strongest exact negation    *)
(* -------------------------------------------------------------------------- *)

Lemma no_epstep_to_mus_unit_glm : forall t',
    epstep counterexample_t t' ->
    phi_erase t' <> TMuS TUnit.
Proof.
  intros t' Hstep Heq.
  rewrite (epstep_counterexample_t_inv_glm t' Hstep) in Heq.
  exact (phi_erase_counterexample_t_neq_mus_unit_glm Heq).
Qed.

(** Exact negation at the witness: no original term epstep lands on any
    preimage of [TMuS TUnit]. *)
Theorem no_epstep_preimage_mus_unit_glm :
    ~ exists u, epstep counterexample_t u /\ phi_erase u = TMuS TUnit.
Proof.
  intros [u [Hs Heq]]. exact (no_epstep_to_mus_unit_glm u Hs Heq).
Qed.

(** Strongest exact negation theorem: the erased side DOES take the eta
    step to [TMuS TUnit], while the original side takes no step at all
    (exact image is the singleton [t]) and so can never supply the
    preimage.  This is the precise failure of reflection at [t]. *)
Theorem phi_erase_epstep_counterexample_strong_glm :
    epstep (phi_erase counterexample_t) (TMuS TUnit) /\
    (forall u, epstep counterexample_t u -> u = counterexample_t) /\
    ~ (exists u, epstep counterexample_t u /\ phi_erase u = TMuS TUnit).
Proof.
  split; [| split].
  - exact phi_erase_t_epsteps_mus_unit_glm.
  - exact epstep_counterexample_t_inv_glm.
  - exact no_epstep_preimage_mus_unit_glm.
Qed.

(* -------------------------------------------------------------------------- *)
(*  Corollary: the unrestricted reflection interface fails                    *)
(* -------------------------------------------------------------------------- *)

(** The general reflection interface for [phi_erase] along [epstep]:
    every epstep from an erasure should lift back to an epstep from the
    original term with matching erasure. *)
Definition phi_erase_epstep_reflection_glm : Prop :=
  forall t u,
    epstep (phi_erase t) u ->
    exists t', epstep t t' /\ phi_erase t' = u.

Corollary phi_erase_epstep_no_general_reflection_glm :
    ~ phi_erase_epstep_reflection_glm.
Proof.
  intros H.
  destruct (H counterexample_t (TMuS TUnit)
              phi_erase_t_epsteps_mus_unit_glm)
    as [t' [Hs Heq]].
  exact (no_epstep_to_mus_unit_glm t' Hs Heq).
Qed.

Print Assumptions phi_erase_t_epsteps_mus_unit_glm.
Print Assumptions epstep_counterexample_t_inv_glm.
Print Assumptions no_epstep_preimage_mus_unit_glm.
Print Assumptions phi_erase_epstep_counterexample_strong_glm.
Print Assumptions phi_erase_epstep_no_general_reflection_glm.
