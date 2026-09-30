(* A small typing-side obstruction for [muapp_sort].  Formation of the
   expected Pi only says that its codomain is itself a type; it does not say
   that the codomain is convertible to a sort.  This file gives a concrete
   checked Pi whose codomain has a rigid Pi head. *)

Require Import Progress _work_conv_whd_pos.
Import TypeRules.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

Lemma luna_check_sort0_sort1 : check [] (TSort 0) (TSort 1).
Proof.
  eapply ch_conv; [apply (sy_sort 0); apply wf_nil | apply cv_refl].
Qed.

Lemma luna_check_sort0_sort1_ctx :
    check [TSort 0] (TSort 0) (TSort 1).
Proof.
  eapply ch_conv; [apply (sy_sort 0);
    exact (@wf_cons [] (TSort 0) 1 wf_nil luna_check_sort0_sort1)
    | apply cv_refl].
Qed.

Lemma luna_check_sort0_sort1_ctx2 :
    check [TSort 0; TSort 0] (TSort 0) (TSort 1).
Proof.
  eapply ch_conv; [apply (sy_sort 0);
    exact (@wf_cons [TSort 0] (TSort 0) 1
      (@wf_cons [] (TSort 0) 1 wf_nil luna_check_sort0_sort1)
      luna_check_sort0_sort1_ctx)
    | apply cv_refl].
Qed.

(* The codomain below is a Pi, while the whole Pi is nevertheless well formed. *)
Lemma luna_pi_formation_countershape :
    check []
      (TPi (TSort 0) (TPi (TSort 0) (TSort 0)))
      (TSort 1).
Proof.
  eapply ch_conv.
  - eapply sy_pi; [exact luna_check_sort0_sort1 |].
    eapply ch_conv.
    + eapply sy_pi; [exact luna_check_sort0_sort1_ctx |].
      exact luna_check_sort0_sort1_ctx2.
    + apply cv_refl.
  - apply cv_refl.
Qed.

Lemma luna_pi_codomain_countershape :
    forall j, ~ conv (TPi (TSort 0) (TSort 0)) (TSort j).
Proof.
  intros j Hc.
  assert (Htag : HPi = HSort).
  { eapply conv_whd_proved; [exact Hc | apply whd_shape; constructor |
      apply whd_shape; constructor]. }
  discriminate Htag.
Qed.

(* Thus the [check Pi (Sort k)] premise in [app_origin]'s [ao_chk] branch
   cannot supply the needed codomain-sort fact.  The missing information must
   come from the fact that the checked function is the μ former, by transporting
   its synthesized Pi through conversion/subtyping. *)
Print Assumptions luna_pi_formation_countershape.
Print Assumptions luna_pi_codomain_countershape.
