(* GLM worker 4 — mueq simulation infrastructure, part 1: lifting.           *)
(*                                                                          *)
(* Closes the conditional lifting lemmas from the mueq development by        *)
(* instantiating conv_lift_compatible with the checked conv_lift_glm from    *)
(* worker 1's conv-lift bundle.                                             *)
(*                                                                          *)
(* NOTE: this file re-derives the (small) lifting compatibility layer of     *)
(* _luna_mueq_subst.v, which currently does not kernel-check on this        *)
(* toolchain (it references Nat.lt_trichotomy without importing PeanoNat).  *)
(* The statements and proofs are identical up to that import fix; the lift   *)
(* half of that file had already been checked verbatim before the failure    *)
(* point.  Once _luna_mueq_subst.v compiles again, worker 2 may prefer the   *)
(* originals; the names here carry a _glm suffix.                           *)

Require Import Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations TypeRules.
Require Import _luna_mueq _luna_mueq_equiv.
Require Import _glm_conv_lift_bundle_main.

(* The exceptional [me_muapp] case stores an arbitrary full [conv] proof;
   [conv_lift_compatible] names precisely the compatibility needed to
   transport that opaque proof through de Bruijn lifting.  It is exactly the
   type of the checked theorem [conv_lift_glm]. *)
Definition conv_lift_compatible : Prop :=
  forall t u, conv t u -> forall d k,
    conv (lift d k t) (lift d k u).

Definition lift_mubeq_branches (d k : nat)
    (bs : list (term * term)) : list (term * term) :=
  map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs.

Lemma mueq_lift_mut :
  conv_lift_compatible ->
  ((forall t u, mueq t u -> forall d k,
      mueq (lift d k t) (lift d k u)) /\
   (forall bs bs', mubeq bs bs' -> forall d k,
      mubeq (lift_mubeq_branches d k bs)
            (lift_mubeq_branches d k bs'))).
Proof.
  intros Hconv.
  unfold conv_lift_compatible in Hconv.
  apply mueq_mubeq_ind; cbn [lift_mubeq_branches]; intros.
  all: try solve [constructor].
  all: try solve [constructor; eauto].
  all: try solve [constructor; eauto; apply Hconv; assumption].
  all: try solve [cbn [lift]; destruct (Nat.ltb n k); constructor].
  all: try solve [cbn [lift]; apply me_muapp; eapply Hconv; eassumption].
  all: try solve [unfold lift_mubeq_branches; cbn; constructor; eauto].
  all: match goal with
  | H : conv (TApp (TMuS ?S1) ?i1) (TApp (TMuS ?S2) ?i2)
    |- mueq (lift ?d ?k (TApp (TMuS ?S1) ?i1))
             (lift ?d ?k (TApp (TMuS ?S2) ?i2)) =>
      change (mueq
        (TApp (TMuS (lift d k S1)) (lift d k i1))
        (TApp (TMuS (lift d k S2)) (lift d k i2)));
      apply me_muapp;
      exact (Hconv _ _ H d k)
  end.
Qed.

(* The requested closure: mueq/mubeq lifting with conv_lift_glm. *)
Lemma mueq_lift_glm : forall t u, mueq t u -> forall d k,
    mueq (lift d k t) (lift d k u).
Proof.
  intros t u H d k.
  exact (proj1 (mueq_lift_mut conv_lift_glm) t u H d k).
Qed.

Lemma mubeq_lift_glm : forall bs bs', mubeq bs bs' -> forall d k,
    mubeq (lift_mubeq_branches d k bs)
          (lift_mubeq_branches d k bs').
Proof.
  intros bs bs' H d k.
  exact (proj2 (mueq_lift_mut conv_lift_glm) bs bs' H d k).
Qed.

(* mueq lifting commutes with the TCase branch map, for reuse downstream. *)
Lemma mueq_case_lift_glm : forall M M' Q Q' bs bs' d k,
    mueq M M' -> mueq Q Q' -> mubeq bs bs' ->
    mueq (TCase (lift d k M) (lift d k Q) (lift_mubeq_branches d k bs))
         (TCase (lift d k M') (lift d k Q') (lift_mubeq_branches d k bs')).
Proof.
  intros M M' Q Q' bs bs' d k HM HQ Hbs.
  apply me_case;
    [exact (mueq_lift_glm _ _ HM d k)
    |exact (mueq_lift_glm _ _ HQ d k)
    |exact (mubeq_lift_glm _ _ Hbs d k)].
Qed.
