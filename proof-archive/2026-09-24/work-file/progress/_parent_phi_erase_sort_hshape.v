(* Direct erased-sort reflection for every already-classified stable head. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _work_cstep_invariants _luna_phi_erase_shapes
  _parent_phi_erase_sort_direct.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Theorem phi_erase_sort_reflect_hshape_parent : forall t h j,
    hshape t h -> rtc cstep (phi_erase t) (TSort j) ->
    conv t (TSort j).
Proof.
  intros t h j Hshape Hred.
  pose proof (rtc_cstep_hshape (phi_erase t) (TSort j) Hred h
    (phi_erase_hshape_luna t h Hshape)) as Hend.
  inversion Hend; subst h.
  inversion Hshape; subst t.
  cbn [phi_erase] in Hred.
  pose proof (rtc_cstep_sort_id k0 (TSort j) Hred) as Heq.
  inversion Heq. apply cv_refl.
Qed.

Print Assumptions phi_erase_sort_reflect_hshape_parent.
