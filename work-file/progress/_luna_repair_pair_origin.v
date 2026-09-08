Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma pair_origin_aux : forall G t T, check G t T -> forall a b, t = TPair a b ->
    exists A B, check G a A /\ check G b (subst a 0 B) /\
      conv (TSigma A B) T.
Proof.
  intros G t T HC; induction HC; intros aa bb Eqpair; try discriminate; inversion Eqpair; subst.
  - inversion H.
  - inversion H.
  - destruct (IHHC aa bb eq_refl) as [A0 [B0 [Ha [Hb HT]]]].
    exists A0, B0; repeat split; try assumption.
    eapply cv_trans; [exact HT | apply cv_sym; exact H].
  - exists A, B; repeat split; eauto using cv_refl.
Qed.

Lemma pair_origin : forall G a b T,
    check G (TPair a b) T ->
    exists A B, check G a A /\ check G b (subst a 0 B) /\
      conv (TSigma A B) T.
Proof. intros; eapply pair_origin_aux; eauto. Qed.

Print Assumptions pair_origin_aux.
Print Assumptions pair_origin.
