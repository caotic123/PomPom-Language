(* Direct, phase-order-independent erasure consumer.  The only premise is
   reflection of a combined path from an erased term to a stable sort. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition phi_erase_sort_endpoint_reflect_parent : Prop :=
  forall B j,
    rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j).

Definition conv_pi_sort_codomain_compatible_parent : Prop :=
  forall A0 A1 B1 j,
    conv (TPi A0 (TSort j)) (TPi A1 B1) -> conv B1 (TSort j).

Lemma cjoin_erased_sort_direct_parent :
    phi_erase_sort_endpoint_reflect_parent ->
    forall B j, cjoin (TSort j) (phi_erase B) -> conv B (TSort j).
Proof.
  intros REF B j [w [Hsw HBw]].
  pose proof (rtc_cstep_sort_id j w Hsw) as ->.
  exact (REF B j HBw).
Qed.

Theorem conv_pi_sort_codomain_from_phi_direct_parent :
    phi_erase_sort_endpoint_reflect_parent ->
    conv_pi_sort_codomain_compatible_parent.
Proof.
  intros REF A0 A1 B1 j Hconv.
  pose proof (conv_phi_cjoin _ _ Hconv) as Hjoin.
  cbn [phi_erase] in Hjoin.
  destruct (cjoin_pi_inv _ _ _ _ Hjoin) as [_ HB].
  apply (cjoin_erased_sort_direct_parent REF B1 j).
  exact HB.
Qed.

Print Assumptions cjoin_erased_sort_direct_parent.
Print Assumptions conv_pi_sort_codomain_from_phi_direct_parent.
