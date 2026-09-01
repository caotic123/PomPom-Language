Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma try_spine_mem_covers_join : forall a L1,
    spine_mem a L1 -> forall Psi L2,
    covers Psi L2 -> pjoin L1 L2 ->
    exists d, In d Psi /\ conv a d.
Proof.
  intros a L1 Hmem.
  induction Hmem as
      [Phi A c Phi' Heval Hac
      |Phi A c Phi' Heval Htail IH];
    intros Psi L2 Hcov Hjoin;
    pose proof (pjoin_eval_left _ _ _ Hjoin Heval) as Hleft;
    inversion Hcov; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [Hlabels _]].
    apply Exists_exists in H0.
    destruct H0 as [d [Hdin Hcd]].
    exists d. split; [exact Hdin |].
    eapply cv_trans; [exact Hac |].
    eapply cv_trans; [apply pjoin_conv; exact Hlabels | exact Hcd].
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [_ Htails]].
    eapply IH; eassumption.
Qed.

Lemma try_spine_covered : forall L a Psi,
    spine_mem a L -> covers Psi L ->
    exists d, In d Psi /\ conv a d.
Proof.
  intros L a Psi Hmem Hcov.
  eapply try_spine_mem_covers_join; eauto using pjoin_refl.
Qed.
