(* Minimal endpoint-directed consumer for the Pi/sort fact needed by
   [muapp_sort].  Arbitrary qconv intermediates need not be syntactic Pis, so
   we transport an honest cjoin-based Pi representation together with the
   fact that its codomain reaches the target sort. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _luna_mueq _glm_qconv_def _glm_qconv_main
  _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition mueq_pi_sort_rep_transport_parent : Prop :=
  forall t u A B j,
    mueq t u -> pi_rep t A B -> rtc cstep B (TSort j) ->
    exists A' B', pi_rep u A' B' /\ rtc cstep B' (TSort j).

Lemma pi_sort_rep_qconv_transport_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall t u, qconv t u -> forall A B j,
      pi_rep t A B -> rtc cstep B (TSort j) ->
      exists A' B', pi_rep u A' B' /\ rtc cstep B' (TSort j).
Proof.
  intros SIM t u Hq.
  induction Hq as [x | x y z Hxy Hyz IH]; intros A B j Hrep Hsort.
  - exists A, B. split; assumption.
  - destruct Hxy as [Hcj | Hm].
    + apply (IH A B j).
      * unfold pi_rep in *.
        eapply cjoin_trans; [apply cjoin_sym; exact Hcj | exact Hrep].
      * exact Hsort.
    + destruct (SIM x y A B j Hm Hrep Hsort)
        as [A1 [B1 [Hrep1 Hsort1]]].
      exact (IH A1 B1 j Hrep1 Hsort1).
Qed.

Theorem pi_sort_codomain_from_qconv_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall A0 A1 B1 j,
      qconv (TPi A0 (TSort j)) (TPi A1 B1) ->
      conv B1 (TSort j).
Proof.
  intros SIM A0 A1 B1 j Hq.
  assert (Hrep0 : pi_rep (TPi A0 (TSort j)) A0 (TSort j)).
  { unfold pi_rep. apply cjoin_refl. }
  destruct (pi_sort_rep_qconv_transport_parent SIM
      (TPi A0 (TSort j)) (TPi A1 B1) Hq A0 (TSort j) j
      Hrep0 (@rtc_refl term cstep (TSort j)))
    as [A' [B' [Hrep Hsort]]].
  unfold pi_rep in Hrep.
  destruct (cjoin_pi_inv A1 B1 A' B' Hrep) as [_ HB].
  eapply cv_trans.
  - apply cjoin_conv. exact HB.
  - apply rtc_cstep_conv. exact Hsort.
Qed.

Corollary conv_pi_sort_codomain_from_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    forall A0 A1 B1 j,
      conv (TPi A0 (TSort j)) (TPi A1 B1) ->
      conv B1 (TSort j).
Proof.
  intros SIM A0 A1 B1 j Hconv.
  apply (pi_sort_codomain_from_qconv_parent SIM A0 A1 B1 j).
  apply conv_qconv_glm. exact Hconv.
Qed.

Print Assumptions pi_sort_rep_qconv_transport_parent.
Print Assumptions pi_sort_codomain_from_qconv_parent.
Print Assumptions conv_pi_sort_codomain_from_endpoint_parent.
