(* _parent_phi_erase_eta_root_sort.v — eta-root (eps_eta) backward with sort endpoint.
   Proves the eps_eta root case of phi_erase eta-backward: when the erased
   term is an eta redex contracting (via eps_eta shape) to a sort, the
   original term converts to that sort. The TMuS-collapsing obstruction
   (counterexample_t in _glm_phi_erase_epstep_counterexample.v) is discharged
   vacuously by the sort premise: here the redex function part is itself a
   sort (closed, lift-identity), so phi_erase preimage is forced to be that
   sort (erase_shape_lam/app + sort/var preimage), the original is itself an
   eta redex, and cv_eta + trans closes. A TMuS-headed preimage would erase
   to TMuS TUnit <> TSort, so case (b) is discriminate-impossible. *)

Require Import Progress _tmp_epstep
  _glm_phi_erase_pstep_reflect_shapes _parent_phi_erase_sort_algebra.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition is_eta_redex (a b : term) : Prop :=
  exists k, a = TLam (TApp (lift 1 0 (TSort k)) (TVar 0)) /\ b = TSort k.

Theorem phi_erase_eta_root_backward_glm : forall t u j,
  epstep (phi_erase t) u -> conv u (TSort j) ->
  (is_eta_redex (phi_erase t) u) -> conv t (TSort j).
Proof.
  intros t u j Hep Hconv Heta.
  destruct Heta as [k [HeqA HeqB]].
  subst u.
  destruct (erase_shape_lam_glm t _ HeqA) as [b0 [Ht Hb0]].
  subst t.
  cbn [lift] in Hb0.
  destruct (erase_shape_app_glm b0 _ _ Hb0) as [x [y [Hb0eq [Hpx Hpy]]]].
  subst b0.
  pose proof (phi_erase_sort_preimage_parent x k Hpx) as Hx.
  pose proof (phi_erase_var_preimage_parent y 0 Hpy) as Hy.
  subst x.
  subst y.
  eapply cv_trans.
  - exact (cv_eta (TSort k)).
  - exact Hconv.
Qed.

Print Assumptions phi_erase_eta_root_backward_glm.
