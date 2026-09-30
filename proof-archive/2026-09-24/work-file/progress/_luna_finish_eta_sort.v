Require Import Progress _tmp_epstep.
From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.
Import ListNotations TypeRules.

Definition bad_t : term :=
  TSnd (TLam (TApp (TPair (TMuS (TVar 0)) (TSort 0)) (TVar 0))).
Definition bad_u : term :=
  TSnd (TPair (TMuS TUnit) (TSort 0)).

Lemma bad_phi : phi_erase bad_t =
    TSnd (TLam (TApp (TPair (TMuS TUnit) (TSort 0)) (TVar 0))).
Proof. reflexivity. Qed.

Lemma bad_ep : epstep (phi_erase bad_t) bad_u.
Proof.
  unfold bad_t, bad_u.
  cbn [phi_erase].
  apply eps_snd.
  change (epstep (TLam (TApp (lift 1 0 (TPair (TMuS TUnit) (TSort 0))) (TVar 0)))
    (TPair (TMuS TUnit) (TSort 0))).
  apply eps_eta. apply epstep_refl.
Qed.

Lemma bad_u_sort : pstep bad_u (TSort 0).
Proof.
  unfold bad_u.
  eapply ps_snd_pair; apply pstep_refl.
Qed.

Print Assumptions bad_ep.
Print Assumptions bad_u_sort.

Lemma bad_pstep_id : forall u, pstep bad_t u -> u = bad_t.
Proof.
  intros u H. unfold bad_t in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : pstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TPair (TMuS (TVar 0)) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TMuS (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TVar 0) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  reflexivity.
Qed.

Print Assumptions bad_pstep_id.
