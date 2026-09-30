Require Import Progress _tmp_epstep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma pstep_hshape_luna : forall t u h,
    pstep t u -> hshape t h -> hshape u h.
Proof.
  intros t u h Hp Hshape.
  inversion Hp; subst; inversion Hshape; subst; eauto using hshape;
    repeat match goal with
    | H : pstep (TMuI _) _ |- _ => inversion H; subst; clear H
    | H : pstep (TMuS _) _ |- _ => inversion H; subst; clear H
    end;
    constructor.
Qed.

Lemma epstep_hshape_luna : forall t u h,
    epstep t u -> hshape t h -> hshape u h.
Proof.
  intros t u h He Hshape.
  inversion He; subst; inversion Hshape; subst; eauto using hshape;
    repeat match goal with
    | H : epstep (TMuI _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TMuS _) _ |- _ => inversion H; subst; clear H
    end;
    constructor.
Qed.

