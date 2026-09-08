Require Import Progress _luna_repair_erased_sort_sub
  _luna_repair_erased_subst _luna_repair_app_origin.
Require Import _parent_repair_muapp.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import _work_cjoin _work_cstep_invariants.

Lemma value_app_erased_sort_luna : forall f a T,
    check [] (TApp f a) T -> value (TApp f a) -> erased_sort T.
Proof.
  intros f a T HC HV.
  destruct (check_app_origin [] (TApp f a) T HC eq_refl f a eq_refl)
    as [X [HO HS]].
  apply (erased_sort_sub _ _ _ HS).
  destruct HO as [C HSYN | A B k Hformation HF HA].
  - pose proof (value_app_synth_sort f a C HV HSYN) as ->.
    exists 0. apply cjoin_refl.
  - assert (HFshape : (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf)).
    { inversion HV; subst; eauto. }
    destruct (mu_former_checked_erased_pi_origin_luna [] f A B HFshape HF)
      as [IT HPI].
    destruct (sub_mu_pi_erased_codomain_sort _ _ _ _ HPI) as [j Hj].
    exists j. apply erased_sort_cjoin_subst_luna, Hj.
Qed.

Print Assumptions value_app_erased_sort_luna.
