(* Unconditional pstep/mueq commuting square.  The older worker proof was
   parameterized by conversion substitution; the parent conversion bundle
   now supplies that premise as a closed theorem. *)

Require Import Progress _parent_conv_subst_all.
Load "_glm_mueq_sim_pstep".

Theorem pstep_mueq_sim_unconditional_luna : forall t t' u,
    pstep t t' -> mueq t u ->
    exists u', pstep u u' /\ mueq t' u'.
Proof.
  intros t t' u Hstep Hm.
  destruct (pstep_mueq_sim (conv_subst_compatible_parent)
      t t' Hstep u Hm) as [u' [Hu' Hm']].
  exists u'. split; assumption.
Qed.

Print Assumptions pstep_mueq_sim_unconditional_luna.
