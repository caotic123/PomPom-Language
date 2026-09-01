Require Import Progress _tmp_epstep.
Import TypeRules.

Fixpoint eta_kfold (k : nat) (t : term) : term :=
  match k with
  | 0 => t
  | S n => TLam (TApp (lift 1 0 (eta_kfold n t)) (TVar 0))
  end.

Lemma epstep_eta_kfold : forall t t' k,
    epstep t t' -> epstep (eta_kfold k t) t'.
Proof.
  intros t t' k H.
  induction k as [|n IH].
  - exact H.
  - cbn. apply eps_eta. exact IH.
Qed.
