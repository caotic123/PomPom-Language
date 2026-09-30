Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* This is the direct signature-transport fact needed by [su_sig]. *)
Lemma luna_spine_mem_conv : forall a b L,
    conv a b -> spine_mem b L -> spine_mem a L.
Proof.
  intros a b L Hab H. induction H.
  - eapply sm_here; eauto using cv_trans.
  - eapply sm_there; eauto using cv_trans.
Qed.

Lemma luna_neutral_pstep : forall n, neutral n -> forall u,
    pstep n u -> neutral u.
Proof.
  intros n Hn. induction Hn; intros u Hp; inversion Hp; subst;
    eauto using neutral; try assumption.
  all: repeat match goal with
    | H : neutral (TLam _) |- _ => inversion H
    | H : neutral (TPair _ _) |- _ => inversion H
    | H : neutral (TIn _) |- _ => inversion H
    | H : neutral TEZero |- _ => inversion H
    | H : neutral (TESucc _) |- _ => inversion H
    end; eauto using neutral.
Qed.

Lemma luna_neutral_psteps : forall n, neutral n -> forall u,
    rtc pstep n u -> neutral u.
Proof.
  intros n Hn u H. revert Hn.
  induction H as [x | x y z Hxy Hyz IH]; intros Hn.
  - exact Hn.
  - apply IH. eapply luna_neutral_pstep; eassumption.
Qed.

Lemma luna_no_pjoin_lcons_neutral : forall A a l n,
    neutral n -> ~ pjoin (TLCons A a l) n.
Proof.
  intros A a l n Hn [w [Hl Hn']].
  destruct (psteps_lcons_inv _ _ _ _ Hl)
    as [A' [a' [l' [Hw _]]]].
  pose proof (luna_neutral_psteps n Hn w Hn') as Hnw.
  rewrite Hw in Hnw. inversion Hnw.
Qed.

Lemma luna_spine_mem_incl_join : forall a L1,
    spine_mem a L1 -> forall L2 L3,
    spine_incl L2 L3 -> pjoin L1 L2 -> spine_mem a L3.
Proof.
  intros a L1 Hmem.
  induction Hmem as
      [Phi A c Phi' Heval Hac
      |Phi A c Phi' Heval Htail IH];
    intros L2 L3 Hincl Hjoin;
    pose proof (pjoin_eval_left _ _ _ Hjoin Heval) as Hleft;
    inversion Hincl; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [Hlabels _]].
    apply luna_spine_mem_conv with (b := c0).
    + eapply cv_trans; [exact Hac |].
      apply pjoin_conv; exact Hlabels.
    + exact H0.
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [_ Htails]].
    eapply IH; eassumption.
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
Qed.

Lemma luna_spine_mem_incl : forall a Phi1 Phi2,
    spine_mem a Phi1 -> spine_incl Phi1 Phi2 -> spine_mem a Phi2.
Proof.
  intros a Phi1 Phi2 Hmem Hincl.
  eapply luna_spine_mem_incl_join; eauto using pjoin_refl.
Qed.

Print Assumptions luna_spine_mem_conv.
Print Assumptions luna_spine_mem_incl_join.
Print Assumptions luna_spine_mem_incl.
