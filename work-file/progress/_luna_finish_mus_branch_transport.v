Require Import Progress ErasureCounterexample SignatureLemmas.
Require Import _luna_finish_musapp_cjoin _parent_finish_cjoin_context
  _luna_finish_branch_erase_bridge.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants
  Progress._tmp_commute.

Lemma mus_branch_transport_luna : forall S1 S2 i1 i2 c,
    conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
    cjoin (phi_erase (TApp (branches (TApp S1 i1)) c))
      (phi_erase (TApp (branches (TApp S2 i2)) c)).
Proof.
  intros S1 S2 i1 i2 c Hconv.
  pose proof (branch_erase_conv
    (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) Hconv) as Hfc.
  pose proof (fconv_cjoin _ _ Hfc) as Hbranch.
  cbn [branch_erase branches] in Hbranch.
  destruct (cjoin_musapp_inv_luna
    (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
    (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
    (branch_erase i1) (branch_erase i2) Hbranch) as [HS Hi].
  pose proof (cjoin_app_parent _ _ _ _ HS Hi) as Happ.
  (* Contract the two erased MuS wrappers at the application head. *)
  assert (Hleft0 : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
        (branch_erase i1))
      (subst (branch_erase i1) 0
        (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))).
  { eapply rtc_step; [apply pstep_cstep; apply ps_beta; apply pstep_refl; apply pstep_refl | apply rtc_refl]. }
  assert (Hleft : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
        (branch_erase i1))
      (TFst (TApp (branch_erase S1) (branch_erase i1)))).
  { cbn [subst lift] in Hleft0.
    rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl in Hleft0.
    rewrite Progress._tmp_commute.lift_zero_id_local in Hleft0.
    rewrite subst_lift_zero in Hleft0. exact Hleft0. }
  assert (Hright0 : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
        (branch_erase i2))
      (subst (branch_erase i2) 0
        (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))).
  { eapply rtc_step; [apply pstep_cstep; apply ps_beta; apply pstep_refl; apply pstep_refl | apply rtc_refl]. }
  assert (Hright : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
        (branch_erase i2))
      (TFst (TApp (branch_erase S2) (branch_erase i2)))).
  { cbn [subst lift] in Hright0.
    rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl in Hright0.
    rewrite Progress._tmp_commute.lift_zero_id_local in Hright0.
    rewrite subst_lift_zero in Hright0. exact Hright0. }
  pose proof (cjoin_reduce_left _ _ _ Happ Hleft) as Hred1.
  pose proof (cjoin_reduce_right _ _ _ Hred1 Hright) as Hred2.
  apply cjoin_branch_to_phi_luna.
  apply cjoin_app_parent; [exact Hred2 | apply cjoin_refl].
Qed.

Print Assumptions mus_branch_transport_luna.
