Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Require Import _luna_repair_sigma_join _luna_repair_pair_origin.

Lemma erased_sigma_cjoin_components_luna : forall A B A' B',
    cjoin (phi_erase (TSigma A B)) (phi_erase (TSigma A' B')) ->
    cjoin (phi_erase A) (phi_erase A') /\
    cjoin (phi_erase B) (phi_erase B').
Proof.
  intros A B A' B' H.
  cbn [phi_erase] in H.
  apply cjoin_sigma_inv_luna; exact H.
Qed.

Lemma checked_pair_sigma_origin_luna : forall a b T,
    check [] (TPair a b) T ->
    exists A B, check [] a A /\ check [] b (subst a 0 B) /\
      conv (TSigma A B) T.
Proof. intros; apply pair_origin; assumption. Qed.

Print Assumptions erased_sigma_cjoin_components_luna.
Print Assumptions checked_pair_sigma_origin_luna.
