Require Import Progress _luna_mueq _luna_mueq_equiv.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma mueq_hshape_glm : forall t u, mueq t u ->
    forall h, hshape t h -> hshape u h.
Proof.
  intros t u Hm. induction Hm; intros h0 Hshape;
    inversion Hshape; subst.
  all: repeat match goal with
       | H : mueq (TMuI _) _ |- _ => inversion H; subst; clear H
       | H : mueq (TMuS _) _ |- _ => inversion H; subst; clear H
       end; eauto using hshape.
Qed.

Corollary mueq_hshape_rev_glm : forall t u, mueq t u ->
    forall h, hshape u h -> hshape t h.
Proof.
  intros t u Hm h Hshape. eapply mueq_hshape_glm.
  - apply mueq_sym; exact Hm.
  - exact Hshape.
Qed.
