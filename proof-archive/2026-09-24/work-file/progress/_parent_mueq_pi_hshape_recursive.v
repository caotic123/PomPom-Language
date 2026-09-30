(* Stable-head case for the direct Pi/sort endpoint transport.  Only an
   actual Pi can have a stable head and reach a Pi; its codomain is a strict
   subterm, so the smaller-source sort-transport hypothesis suffices. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _work_cstep_invariants _luna_mueq _glm_mueq_sim_close_rep
  _parent_mueq_eta_sort_recursive _parent_pi_sort_rep_normalize.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Theorem mueq_pi_endpoint_hshape_recursive_parent :
    forall t u A B j h,
      mueq_sort_transport_below_parent (tsize t) ->
      hshape t h -> mueq t u ->
      rtc cstep t (TPi A B) -> rtc cstep B (TSort j) ->
      exists A' B',
        rtc cstep u (TPi A' B') /\ rtc cstep B' (TSort j).
Proof.
  intros t u A B j h IH Hshape Hm Hpi Hsort.
  pose proof (rtc_cstep_hshape t (TPi A B) Hpi h Hshape) as Hend.
  inversion Hend; subst h.
  inversion Hshape; subst t.
  destruct (mueq_pi_shape_inv_glm A1 B1 u Hm)
    as [As [Bs [-> [_ HBm]]]].
  destruct (rtc_cstep_pi_inv A1 B1 (TPi A B) Hpi)
    as [Ae [Be [Heq [_ HB]]]].
  inversion Heq; subst Ae Be.
  assert (HB0sort : rtc cstep B1 (TSort j)).
  { eapply rtc_trans; [exact HB | exact Hsort]. }
  assert (Hsmall : tsize B1 < tsize (TPi A1 B1)).
  { pose proof (tsize_pos A1). cbn [tsize]. lia. }
  pose proof (IH B1 Bs j Hsmall HBm HB0sort) as HB0'sort.
  exists As, Bs. split; [apply rtc_refl | exact HB0'sort].
Qed.

Print Assumptions mueq_pi_endpoint_hshape_recursive_parent.
