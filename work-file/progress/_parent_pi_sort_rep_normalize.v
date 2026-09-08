(* Normalize the cjoin-based Pi/sort representation interface to a direct
   endpoint statement, which is often easier to prove by source-size
   induction. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _luna_mueq _glm_injectivity_close_rep
  _parent_pi_sort_rep_consumer.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma pi_sort_rep_to_endpoint_parent : forall t A B j,
    pi_rep t A B -> rtc cstep B (TSort j) ->
    exists A' B',
      rtc cstep t (TPi A' B') /\ rtc cstep B' (TSort j).
Proof.
  intros t A B j [w [Htw Hpiw]] Hsort.
  destruct (rtc_cstep_pi_inv A B w Hpiw)
    as [A' [B' [Hw [_ HB']]]].
  subst w.
  destruct (cstep_confluent B B' (TSort j) HB' Hsort)
    as [q [HB'q Hsq]].
  pose proof (rtc_cstep_sort_id j q Hsq) as ->.
  exists A', B'. split; assumption.
Qed.

Lemma pi_sort_endpoint_to_rep_parent : forall t A B j,
    rtc cstep t (TPi A B) -> rtc cstep B (TSort j) ->
    pi_rep t A B /\ rtc cstep B (TSort j).
Proof.
  intros t A B j Hpi Hsort. split; [|exact Hsort].
  unfold pi_rep. exists (TPi A B). split; [exact Hpi | apply rtc_refl].
Qed.

Definition mueq_pi_sort_endpoint_transport_parent : Prop :=
  forall t u A B j,
    mueq t u ->
    rtc cstep t (TPi A B) -> rtc cstep B (TSort j) ->
    exists A' B',
      rtc cstep u (TPi A' B') /\ rtc cstep B' (TSort j).

Definition mueq_pi_sort_endpoint_below_parent (N : nat) : Prop :=
  forall t u A B j,
    tsize t < N -> mueq t u ->
    rtc cstep t (TPi A B) -> rtc cstep B (TSort j) ->
    exists A' B',
      rtc cstep u (TPi A' B') /\ rtc cstep B' (TSort j).

Theorem pi_sort_endpoint_transport_implies_rep_parent :
    mueq_pi_sort_endpoint_transport_parent ->
    mueq_pi_sort_rep_transport_parent.
Proof.
  intros SIM t u A B j Hm Hrep Hsort.
  destruct (pi_sort_rep_to_endpoint_parent t A B j Hrep Hsort)
    as [A1 [B1 [Htpi HB1]]].
  destruct (SIM t u A1 B1 j Hm Htpi HB1)
    as [A2 [B2 [Hupi HB2]]].
  exists A2, B2. split; [|exact HB2].
  exact (proj1 (pi_sort_endpoint_to_rep_parent u A2 B2 j Hupi HB2)).
Qed.

Theorem pi_sort_rep_transport_implies_endpoint_parent :
    mueq_pi_sort_rep_transport_parent ->
    mueq_pi_sort_endpoint_transport_parent.
Proof.
  intros SIM t u A B j Hm Htpi Hsort.
  pose proof (pi_sort_endpoint_to_rep_parent t A B j Htpi Hsort)
    as [Hrep _].
  destruct (SIM t u A B j Hm Hrep Hsort)
    as [A1 [B1 [Hurep HB1]]].
  exact (pi_sort_rep_to_endpoint_parent u A1 B1 j Hurep HB1).
Qed.

Print Assumptions pi_sort_rep_to_endpoint_parent.
Print Assumptions pi_sort_endpoint_to_rep_parent.
Print Assumptions pi_sort_endpoint_transport_implies_rep_parent.
Print Assumptions pi_sort_rep_transport_implies_endpoint_parent.
