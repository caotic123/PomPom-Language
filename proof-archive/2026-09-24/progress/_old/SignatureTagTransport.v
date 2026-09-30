(* Enabled-tag transport for beta/eta conversion, and the limitation of
   recovering tags from branch erasure. Neither result proves transport
   through arbitrary mixed beta/eta/phi conversion. *)
Require Import Progress SignatureConversion ErasureCounterexample.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRulesCore.
Import Progress._work_cjoin.

Lemma signature_live_tag_transport_luna : forall S0 i0 S1 i1 c n bs,
    fconv (TApp (TMuS S0) i0) (TApp (TMuS S1) i1) ->
    enum_pos c n ->
    Forall (fun d => exists m, enum_pos d m) bs ->
    spine_mem c (labels (TApp S0 i0)) ->
    covers bs (labels (TApp S1 i1)) ->
    exists d, In d bs /\ enum_pos d n.
Proof.
  intros S0 i0 S1 i1 c n bs Hf Hpos Hbs Hmem Hcov.
  destruct (fconv_cjoin _ _ Hf) as [w [H0 H1]].
  destruct (cjoin_musapp_inv_luna _ _ _ _ (ex_intro _ w (conj H0 H1)))
    as [HS Hi].
  pose proof (cjoin_conv_bridge _ _ HS) as HSc.
  pose proof (cjoin_conv_bridge _ _ Hi) as Hic.
  apply erased_spine_covered_pos with
    (L1 := labels (TApp S0 i0)) (L2 := labels (TApp S1 i1))
    (bs := bs) (c := c) (n := n).
  - exact Hpos.
  - exact Hbs.
  - exact Hmem.
  - exact Hcov.
  - exact (cv_snd (cv_app HSc Hic)).
Qed.

Print Assumptions signature_live_tag_transport_luna.

Module BranchErasureLabelGap.
Import ListNotations TypeRulesCore.
Import Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Definition Sfull : term :=
  TLam (TPair (TLam TI1)
    (TLCons TUnitT TEZero (TLNil TUnitT))).
Definition Sempty : term :=
  TLam (TPair (TLam TI1) (TLNil TUnitT)).
Definition ifull : term := TApp Sfull TUnit.
Definition iempty : term := TApp Sempty TUnit.
Definition afull : term := TApp (TMuS Sfull) TUnit.
Definition aempty : term := TApp (TMuS Sempty) TUnit.

Lemma eval_labels_full : eval (labels ifull)
    (TLCons TUnitT TEZero (TLNil TUnitT)).
Proof.
  unfold labels, ifull, Sfull.
  eapply ev_step; [apply st_snd1; apply st_beta |].
  cbn [subst].
  eapply ev_step; [apply st_snd | apply ev_refl].
Qed.

Lemma eval_labels_empty : eval (labels iempty) (TLNil TUnitT).
Proof.
  unfold labels, iempty, Sempty.
  eapply ev_step; [apply st_snd1; apply st_beta |].
  cbn [subst].
  eapply ev_step; [apply st_snd | apply ev_refl].
Qed.

Lemma full_label_membership : spine_mem TEZero (labels ifull).
Proof.
  apply sm_here with (A:=TUnitT) (c':=TEZero) (Phi':=TLNil TUnitT).
  - exact eval_labels_full.
  - apply cv_refl.
Qed.

Lemma empty_label_covers : covers [] (labels iempty).
Proof.
  apply cov_nil with (A:=TUnitT).
  exact eval_labels_empty.
Qed.

Lemma phi_erased_app_cjoin :
    cjoin (phi_erase afull) (phi_erase aempty).
Proof.
  unfold afull, aempty.
  cbn [phi_erase].
  apply cjoin_refl.
Qed.

Lemma no_empty_position :
    ~ (exists d, In d [] /\ enum_pos d 0).
Proof.
  intros [d [Hd _]]. inversion Hd.
Qed.

Theorem erased_recovery_label_gap :
    spine_mem TEZero (labels ifull) /\
    covers [] (labels iempty) /\
    cjoin (phi_erase afull) (phi_erase aempty) /\
    ~ (exists d, In d [] /\ enum_pos d 0).
Proof.
  repeat split.
  - apply full_label_membership.
  - apply empty_label_covers.
  - apply phi_erased_app_cjoin.
  - apply no_empty_position.

Qed.
Print Assumptions erased_recovery_label_gap.

Lemma branch_wrapper_full :
  fconv
    (TLam (TFst (TApp (lift 1 0 (branch_erase Sfull)) (TVar 0))))
    (TLam (TLam TI1)).
Proof.
  apply (fconv_map (fun z => TLam z)).
  - intros x y Hxy. apply fs_lam. exact Hxy.
  - eapply fc_trans.
    + apply (fconv_map (fun z => TFst z)).
      * intros x y Hxy. apply fs_fst. exact Hxy.
      * apply fc_step. apply fs_step. apply st_beta.
    + cbn [subst].
      apply fc_step. apply fs_step. apply st_fst.
Qed.

Lemma branch_wrapper_empty :
  fconv
    (TLam (TFst (TApp (lift 1 0 (branch_erase Sempty)) (TVar 0))))
    (TLam (TLam TI1)).
Proof.
  apply (fconv_map (fun z => TLam z)).
  - intros x y Hxy. apply fs_lam. exact Hxy.
  - eapply fc_trans.
    + apply (fconv_map (fun z => TFst z)).
      * intros x y Hxy. apply fs_fst. exact Hxy.
      * apply fc_step. apply fs_step. apply st_beta.
    + cbn [subst]. apply fc_step. apply fs_step. apply st_fst.
Qed.

Lemma branch_erased_app_cjoin :
    cjoin (branch_erase afull) (branch_erase aempty).
Proof.
  unfold afull, aempty.
  cbn [branch_erase].
  assert (Hf : fconv
      (TApp (TMuS
        (TLam (TFst (TApp (lift 1 0 (branch_erase Sfull)) (TVar 0))))) TUnit)
      (TApp (TMuS (TLam (TLam TI1))) TUnit)).
  { apply (fconv_map (fun z => TApp z TUnit)).
    - intros x y Hxy. apply fs_app1. exact Hxy.
    - apply (fconv_map (fun z => TMuS z)).
      + intros x y Hxy. apply fs_mus. exact Hxy.
      + apply branch_wrapper_full. }
  assert (He : fconv
      (TApp (TMuS
        (TLam (TFst (TApp (lift 1 0 (branch_erase Sempty)) (TVar 0))))) TUnit)
      (TApp (TMuS (TLam (TLam TI1))) TUnit)).
  { apply (fconv_map (fun z => TApp z TUnit)).
    - intros x y Hxy. apply fs_app1. exact Hxy.
    - apply (fconv_map (fun z => TMuS z)).
      + intros x y Hxy. apply fs_mus. exact Hxy.
      + apply branch_wrapper_empty. }
  eapply cjoin_trans; [apply fconv_cjoin; exact Hf |].
  apply cjoin_sym. apply fconv_cjoin. exact He.
Qed.

Theorem branch_erased_recovery_label_gap :
    spine_mem TEZero (labels ifull) /\
    covers [] (labels iempty) /\
    cjoin (branch_erase afull) (branch_erase aempty) /\
    ~ (exists d, In d [] /\ enum_pos d 0).
Proof.
  repeat split.
  - apply full_label_membership.
  - apply empty_label_covers.
  - apply branch_erased_app_cjoin.
  - apply no_empty_position.
Qed.
Print Assumptions branch_erased_recovery_label_gap.

End BranchErasureLabelGap.
