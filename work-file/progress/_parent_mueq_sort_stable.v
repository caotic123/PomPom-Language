(* Every already-classified stable head is an immediate sort-transport case. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _work_cstep_invariants _luna_mueq.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Theorem mueq_sort_transport_hshape_parent : forall t u j h,
    hshape t h -> mueq t u -> rtc cstep t (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros t u j h Hshape Hm Hred.
  pose proof (rtc_cstep_hshape _ _ Hred h Hshape) as Hend.
  inversion Hend; subst h.
  inversion Hshape; subst t.
  inversion Hm; subst u.
  pose proof (rtc_cstep_sort_id _ _ Hred) as Heq.
  inversion Heq. apply rtc_refl.
Qed.

Lemma cstep_root_to_nonsort_parent : forall t q h,
    rtc cstep t q -> hshape q h -> h <> HSort ->
    forall j, ~ rtc cstep t (TSort j).
Proof.
  intros t q h Hroot Hshape Hneq j Hsort.
  destruct (cstep_confluent _ _ _ Hroot Hsort) as [w [Hqw Hsw]].
  rewrite (rtc_cstep_sort_id _ _ Hsw) in Hqw.
  pose proof (rtc_cstep_hshape _ _ Hqw h Hshape) as Hend.
  inversion Hend; subst. exact (Hneq eq_refl).
Qed.

Print Assumptions mueq_sort_transport_hshape_parent.
Print Assumptions cstep_root_to_nonsort_parent.
