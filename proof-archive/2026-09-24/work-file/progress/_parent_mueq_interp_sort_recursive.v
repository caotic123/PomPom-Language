(* The interpretation-variable root case for well-founded sort transport. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _work_cstep_invariants _luna_mueq _glm_mueq_pstep_conditional_inv
  _parent_mueq_eta_sort_recursive _parent_mueq_sort_stable.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma mueq_interp_inv_parent : forall D X u,
    mueq (TInterp D X) u ->
    exists D' X', u = TInterp D' X' /\ mueq D D' /\ mueq X X'.
Proof.
  intros D X u H. inversion H; subst.
  eexists; eexists. repeat split; try reflexivity; eassumption.
Qed.

Lemma interp_var_contractum_reaches_sort_parent : forall i X j,
    rtc cstep (TInterp (TIVar i) X) (TSort j) ->
    rtc cstep (TApp X i) (TSort j).
Proof.
  intros i X j Hsort.
  assert (Hroot : rtc cstep (TInterp (TIVar i) X) (TApp X i)).
  { apply rtc_one, pstep_cstep.
    exact (ps_interp_var i i X X (pstep_refl i) (pstep_refl X)). }
  destruct (cstep_confluent _ _ _ Hroot Hsort) as [w [Hcw Hsw]].
  rewrite (rtc_cstep_sort_id _ _ Hsw) in Hcw. exact Hcw.
Qed.

Theorem mueq_interp_var_sort_recursive_parent : forall i X u j,
    mueq_sort_transport_below_parent (tsize (TInterp (TIVar i) X)) ->
    mueq (TInterp (TIVar i) X) u ->
    rtc cstep (TInterp (TIVar i) X) (TSort j) ->
    rtc cstep u (TSort j).
Proof.
  intros i X u j IH Hm Hsort.
  destruct (mueq_interp_inv_parent _ _ _ Hm)
    as [D' [X' [-> [HD HX]]]].
  destruct (mueq_ivar_inv_glm _ _ HD) as [i' [-> Hi]].
  pose proof (interp_var_contractum_reaches_sort_parent i X j Hsort)
    as Hcontract.
  assert (Hsmall :
      tsize (TApp X i) < tsize (TInterp (TIVar i) X)).
  { cbn [tsize]. lia. }
  assert (Hmapp : mueq (TApp X i) (TApp X' i')).
  { apply me_app; assumption. }
  pose proof (IH _ _ j Hsmall Hmapp Hcontract) as Htarget.
  eapply rtc_step.
  - apply pstep_cstep.
    exact (ps_interp_var i' i' X' X' (pstep_refl i') (pstep_refl X')).
  - exact Htarget.
Qed.

Lemma interp_one_not_sort_parent : forall X j,
    ~ rtc cstep (TInterp TI1 X) (TSort j).
Proof.
  intros X j.
  eapply cstep_root_to_nonsort_parent with (q := TUnitT) (h := HUnitT).
  - apply rtc_one, pstep_cstep. exact (ps_interp_one X X (pstep_refl X)).
  - constructor.
  - discriminate.
Qed.

Lemma interp_prod_not_sort_parent : forall A B X j,
    ~ rtc cstep (TInterp (TIProd A B) X) (TSort j).
Proof.
  intros A B X j.
  eapply cstep_root_to_nonsort_parent with
    (q := TSigma (TInterp A X) (lift 1 0 (TInterp B X))) (h := HSigma).
  - apply rtc_one, pstep_cstep.
    exact (ps_interp_prod A A B B X X
      (pstep_refl A) (pstep_refl B) (pstep_refl X)).
  - constructor.
  - discriminate.
Qed.

Lemma interp_pi_not_sort_parent : forall S T X j,
    ~ rtc cstep (TInterp (TIPi S T) X) (TSort j).
Proof.
  intros S T X j.
  eapply cstep_root_to_nonsort_parent with
    (q := TPi S (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (h := HPi).
  - apply rtc_one, pstep_cstep.
    exact (ps_interp_pi S S T T X X
      (pstep_refl S) (pstep_refl T) (pstep_refl X)).
  - constructor.
  - discriminate.
Qed.

Lemma interp_sig_not_sort_parent : forall S T X j,
    ~ rtc cstep (TInterp (TISig S T) X) (TSort j).
Proof.
  intros S T X j.
  eapply cstep_root_to_nonsort_parent with
    (q := TSigma S (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (h := HSigma).
  - apply rtc_one, pstep_cstep.
    exact (ps_interp_sig S S T T X X
      (pstep_refl S) (pstep_refl T) (pstep_refl X)).
  - constructor.
  - discriminate.
Qed.

Lemma interp_choice_not_sort_parent : forall E T X j,
    ~ rtc cstep (TInterp (TIChoice E T) X) (TSort j).
Proof.
  intros E T X j.
  eapply cstep_root_to_nonsort_parent with
    (q := TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (h := HSigma).
  - apply rtc_one, pstep_cstep.
    exact (ps_interp_choice E E T T X X
      (pstep_refl E) (pstep_refl T) (pstep_refl X)).
  - constructor.
  - discriminate.
Qed.

Print Assumptions mueq_interp_var_sort_recursive_parent.
Print Assumptions interp_one_not_sort_parent.
Print Assumptions interp_prod_not_sort_parent.
Print Assumptions interp_pi_not_sort_parent.
Print Assumptions interp_sig_not_sort_parent.
Print Assumptions interp_choice_not_sort_parent.
