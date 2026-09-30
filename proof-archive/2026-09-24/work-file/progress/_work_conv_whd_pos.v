Require Import Progress _work_mixed_closure _work_cjoin _work_cstep_invariants
  _luna_phi_erase_shapes.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma phi_erase_eval_csteps : forall t u, eval t u ->
    rtc cstep (phi_erase t) (phi_erase u).
Proof.
  intros t u H.
  apply rtc_one, cs_core, eval_psteps, phi_erase_eval_luna, H.
Qed.

Theorem conv_whd_proved : forall t u h1 h2,
    conv t u -> whd t h1 -> whd u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 Hconv [t' [Ht Htshape]] [u' [Hu Hushape]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Hjoin.
  pose proof (phi_erase_eval_csteps _ _ Ht) as Htred.
  pose proof (phi_erase_eval_csteps _ _ Hu) as Hured.
  assert (Hjoin' : cjoin (phi_erase t') (phi_erase u')).
  { eapply cjoin_reduce_right.
    - eapply cjoin_reduce_left; eassumption.
    - exact Hured. }
  destruct Hjoin' as [w [Htw Huw]].
  eapply hshape_tag_unique with (T := w).
  - eapply rtc_cstep_hshape; [exact Htw |].
    apply phi_erase_hshape_luna, Htshape.
  - eapply rtc_cstep_hshape; [exact Huw |].
    apply phi_erase_hshape_luna, Hushape.
Qed.

Theorem conv_pos_proved : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.
Proof.
  intros c d n m Hconv Hc Hd.
  destruct (conv_phi_cjoin _ _ Hconv) as [w [Hcw Hdw]].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hd) as Hed.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Ewc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Ewd.
  assert (Ecd : phi_erase c = phi_erase d) by congruence.
  eapply enum_pos_functional.
  - exact Hec.
  - rewrite Ecd. exact Hed.
Qed.
