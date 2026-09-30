Require Import Progress _tmp_epstep _luna_eta_kfold.
Import TypeRules.

Lemma pstep_eta_kfold : forall k a b,
    pstep a b -> pstep (eta_kfold k a) (eta_kfold k b).
Proof.
  induction k as [|k IH]; intros a b H.
  - exact H.
  - cbn. apply ps_lam. apply ps_app.
    + apply pstep_lift. apply IH. exact H.
    + apply ps_var.
Qed.
