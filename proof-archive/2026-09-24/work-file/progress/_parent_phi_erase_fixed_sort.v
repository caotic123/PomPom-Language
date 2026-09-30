(* Conversion to a sort collapses to an actual combined reduction whenever
   the source is already fixed by phi erasure. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma phi_fixed_conv_sort_reduces_parent : forall t j,
    phi_erase t = t -> conv t (TSort j) ->
    rtc cstep t (TSort j).
Proof.
  intros t j Hfix Hconv.
  pose proof (conv_phi_cjoin _ _ Hconv) as [w [Htw Hsw]].
  cbn [phi_erase] in Hsw.
  rewrite Hfix in Htw.
  pose proof (rtc_cstep_sort_id j w Hsw) as ->.
  exact Htw.
Qed.

Print Assumptions phi_fixed_conv_sort_reduces_parent.
