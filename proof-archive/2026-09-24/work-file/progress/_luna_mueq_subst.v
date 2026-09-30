Require Import _luna_mueq.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

(* The exceptional [me_muapp] case stores an arbitrary full [conv] proof.
   These two predicates name precisely the compatibility needed to transport
   that opaque proof through de Bruijn operations. *)
Definition conv_lift_compatible : Prop :=
  forall t u, conv t u -> forall d k,
    conv (lift d k t) (lift d k u).

Definition conv_subst_compatible : Prop :=
  forall t t' u u', conv t t' -> conv u u' -> forall k,
    conv (subst u k t) (subst u' k t').

Definition lift_mubeq_branches (d k : nat)
    (bs : list (term * term)) : list (term * term) :=
  map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs.

Definition subst_mubeq_branches (u : term) (k : nat)
    (bs : list (term * term)) : list (term * term) :=
  map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs.

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

Lemma mueq_lift : conv_lift_compatible ->
  forall t u, mueq t u -> forall d k,
    mueq (lift d k t) (lift d k u).
Proof.
  intros Hcompat t u H d k.
  exact (proj1 (mueq_lift_mut Hcompat) t u H d k).
Qed.

Lemma mubeq_lift : conv_lift_compatible ->
  forall bs bs', mubeq bs bs' -> forall d k,
    mubeq (lift_mubeq_branches d k bs)
          (lift_mubeq_branches d k bs').
Proof.
  intros Hcompat bs bs' H d k.
  exact (proj2 (mueq_lift_mut Hcompat) bs bs' H d k).
Qed.

Lemma mueq_subst_var : conv_lift_compatible ->
  forall n u u' k, mueq u u' ->
    mueq (subst u k (TVar n)) (subst u' k (TVar n)).
Proof.
  intros Hlift n u u' k Huu'.
  destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
  - assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
    cbn [subst]. rewrite Hlt. constructor.
  - subst n.
    assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [subst]. rewrite Hlt, Heq.
    eapply mueq_lift; eauto.
  - assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
    cbn [subst]. rewrite Hlt, Heq. constructor.
Qed.

Lemma mueq_subst_mut :
  conv_lift_compatible -> conv_subst_compatible ->
  ((forall t t', mueq t t' -> forall u u' k,
      mueq u u' -> mueq (subst u k t) (subst u' k t')) /\
   (forall bs bs', mubeq bs bs' -> forall u u' k,
      mueq u u' ->
      mubeq (subst_mubeq_branches u k bs)
            (subst_mubeq_branches u' k bs'))).
Proof.
  intros Hlift Hsubst.
  apply mueq_mubeq_ind; cbn [subst_mubeq_branches]; intros.
  - eapply mueq_subst_var; eauto.
  all: try solve [constructor].
  all: try solve [constructor; eauto].
  all: try solve [
    apply me_muapp;
    eapply Hsubst; [eassumption | apply mueq_conv; eassumption]].
Qed.

Lemma mueq_subst : conv_lift_compatible -> conv_subst_compatible ->
  forall t t' u u' k, mueq t t' -> mueq u u' ->
    mueq (subst u k t) (subst u' k t').
Proof.
  intros Hlift Hsubst t t' u u' k Htt' Huu'.
  exact (proj1 (mueq_subst_mut Hlift Hsubst)
    t t' Htt' u u' k Huu').
Qed.

Lemma mubeq_subst : conv_lift_compatible -> conv_subst_compatible ->
  forall bs bs' u u' k, mubeq bs bs' -> mueq u u' ->
    mubeq (subst_mubeq_branches u k bs)
          (subst_mubeq_branches u' k bs').
Proof.
  intros Hlift Hsubst bs bs' u u' k Hbs Huu'.
  exact (proj2 (mueq_subst_mut Hlift Hsubst)
    bs bs' Hbs u u' k Huu').
Qed.
