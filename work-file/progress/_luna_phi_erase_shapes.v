Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma phi_erase_hshape_luna : forall t h,
    hshape t h -> hshape (phi_erase t) h.
Proof.
  intros t h Hshape. induction Hshape; cbn [phi_erase]; constructor.
Qed.

Lemma phi_erase_eval_luna : forall t u,
    eval t u -> eval (phi_erase t) (phi_erase u).
Proof.
  intros t u Heval. induction Heval.
  - apply ev_refl.
  - eapply ev_step.
    + apply phi_erase_step. exact H.
    + exact IHHeval.
Qed.

