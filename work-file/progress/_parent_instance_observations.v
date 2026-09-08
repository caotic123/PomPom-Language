Require Import Progress SignatureConversion SignatureInstances _parent_instance_pruning
  _luna_instance_membership.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._work_cjoin Progress._work_cstep_invariants
 Progress._work_conv_whd_pos Progress._tmp_epstep Progress._work_mixed_closure.

Lemma spine_mem_joined : forall c L, spine_mem c L ->
  joined_mem (phi_erase c) (phi_erase L).
Proof.
  intros c L H; induction H.
  - eapply jm_here with (A:=phi_erase A) (d:=phi_erase c') (R:=phi_erase Phi'); [exact (conv_phi_cjoin _ _ (conv_of_eval _ _ H))|].
    apply conv_phi_cjoin; exact H0.
  - eapply jm_there with (A:=phi_erase A) (d:=phi_erase c') (R:=phi_erase Phi'); [exact (conv_phi_cjoin _ _ (conv_of_eval _ _ H))|exact IHspine_mem].
Qed.

Lemma instance_erased_join : forall t,
 cjoin (phi_erase (instance_translate t)) (phi_erase t).
Proof.
  intro t. exists (phi_erase t). split; [apply rtc_one, cs_eta, rtc_one, instance_translate_erased_eta|apply rtc_refl].
Qed.

Lemma joined_tag_position : forall c n bs d,
 enum_pos c n -> Forall (fun d => exists m, enum_pos d m) bs ->
 In d bs -> cjoin (phi_erase c) (phi_erase d) -> enum_pos d n.
Proof.
  intros c n bs d Hc Hbs Hd Hcd.
  rewrite Forall_forall in Hbs. destruct (Hbs d Hd) as [m Hdm].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hdm) as Hed.
  destruct Hcd as [w [Hcw Hdw]].
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Hwc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Hwd.
  subst w. assert (Hmn : m = n).
  { eapply enum_pos_functional; [exact Hed|]. rewrite <- Hwd; exact Hec. }
  subst m; exact Hdm.
Qed.
Print Assumptions instance_erased_join.
