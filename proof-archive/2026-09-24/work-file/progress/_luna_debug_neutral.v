Require Import Progress.
Import TypeRules.
Lemma dbg : forall n, neutral n -> forall u, step n u -> neutral u.
Proof.
  intros n Hn. induction Hn; intros u Hu; inversion Hu; subst; eauto using neutral.
  all: idtac.
Abort.
