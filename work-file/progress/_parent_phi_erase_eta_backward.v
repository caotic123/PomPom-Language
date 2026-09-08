(* FULL factor premise: eta-step backward sort reflection.
   Competing independent attempt, SLOW SAFE strategy:
   Show after EVERY tactic, case-by-case, until Qed with no admits. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep
  _parent_phi_erase_sort_algebra _parent_phi_erase_sort_direct
  _parent_phi_erase_sort_factor
  _glm_phi_erase_pstep_reflect_shapes
  _parent_phi_erase_epstep_forward
  _work_conv_whd_pos
  _parent_mus_cstep_inv _parent_inert_cstep_inv _parent_epi_nonsort
  _parent_phi_erase_sort_hshape _parent_phi_erase_idem _parent_phi_erase_fixed_sort
  _glm_conv_lift_bundle_main.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Theorem phi_erase_eta_step_sort_backward_proved : phi_erase_eta_step_sort_backward_parent.
Proof.
  Show.
  unfold phi_erase_eta_step_sort_backward_parent.
  Show.
  intros t u j Hep Hconv.
  Show.
  pose proof (epstep_conv (phi_erase t) u Hep) as Hecu.
  Show.
  pose proof (cv_trans Hecu Hconv) as Herase_conv_sort.
  Show.
  pose proof (phi_erase_idempotent_parent t) as Hidem.
  Show.
  pose proof (phi_fixed_conv_sort_reduces_parent (phi_erase t) j) as Hfixlem.
  Show.
  assert (Hfixed : phi_erase (phi_erase t) = phi_erase t).
  Show.
  { rewrite Hidem.
    Show.
    reflexivity.
    Show. }
  Show.
  pose proof (Hfixlem Hfixed Herase_conv_sort) as Hrtc.
  Show.
  (* Hrtc : rtc cstep (phi_erase t) (TSort j).  Need conv t sort.
     Reduce to fixed-u case then size induction. *)
  admit.
Admitted.
