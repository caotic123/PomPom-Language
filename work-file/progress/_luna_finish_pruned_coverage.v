Require Import Progress SignatureLemmas.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma no_pjoin_lnil_neutral_luna : forall A n,
  neutral n -> ~ pjoin (TLNil A) n.
Proof.
  intros A n Hn [w [HL HN]].
  destruct (psteps_lnil_inv _ _ HL) as [A' [Hw _]].
  pose proof (luna_neutral_psteps n Hn w HN) as HH.
  rewrite Hw in HH. inversion HH.
Qed.

Lemma spine_phi_covers_join : forall S i L1 L3,
  spine_phi S i L1 L3 -> forall L2 bs, covers bs L2 ->
  pjoin L1 L2 -> covers bs L3.
Proof.
  intros S i L1 L3 Hphi. induction Hphi; intros L2 bs Hcov Hjoin.
  - apply cov_nil with (A:=A). apply ev_refl.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso. eapply no_pjoin_lcons_lnil; eapply pjoin_eval_right; eassumption.
    + pose proof (pjoin_eval_right _ _ _ Hleft H0) as Hboth.
      destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hheads Htails]].
      apply cov_cons with (Phi:=TLCons A c Psi') (A:=A) (c:=c) (Phi':=Psi'); [apply ev_refl| |].
      * apply Exists_exists in H1. destruct H1 as [d [Hd Hcd]].
        apply Exists_exists. exists d. split; [exact Hd|].
        eapply cv_trans; [apply pjoin_conv; exact Hheads|exact Hcd].
      * eapply IHHphi; eassumption.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso. eapply no_pjoin_lcons_lnil; eapply pjoin_eval_right; eassumption.
    + pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
      eapply IHHphi; eassumption.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso.
      pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      apply (no_pjoin_lnil_neutral_luna A Phin H0).
      apply pjoin_sym; exact Hboth.
    + exfalso. eapply luna_no_pjoin_lcons_neutral; [exact H0|].
      pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      apply pjoin_sym; exact Hboth.
Qed.

Lemma spine_phi_covers : forall S i Phi Psi bs,
  spine_phi S i Phi Psi -> covers bs Phi -> covers bs Psi.
Proof. intros; eapply spine_phi_covers_join; eauto using pjoin_refl. Qed.

Print Assumptions spine_phi_covers_join.
Print Assumptions spine_phi_covers.
