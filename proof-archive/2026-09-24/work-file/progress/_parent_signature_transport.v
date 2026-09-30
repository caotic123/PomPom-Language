Require Import Progress SignatureInstances SignatureConversion SignatureProgressReduction
 _parent_instance_pruning _luna_instance_membership _luna_instance_coverage
 _parent_instance_translation _parent_instance_join _parent_instance_observations
 _luna_instance_observer _luna_instance_conversion.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_cjoin
 Progress._work_cstep_invariants.

Lemma translated_instances_join : forall S0 i0 S1 i1,
 conv (TApp (TMuS S0) i0) (TApp (TMuS S1) i1) ->
 instance_join
  (signature_instance (instance_translate (branches (TApp S0 i0)))
    (instance_translate (labels (TApp S0 i0))) (instance_translate i0))
  (signature_instance (instance_translate (branches (TApp S1 i1)))
    (instance_translate (labels (TApp S1 i1))) (instance_translate i1)).
Proof.
 intros S0 i0 S1 i1 HC. apply instance_conv_join.
 eapply ic_trans.
 - apply ic_sym, ic_core, fc_step, fs_step, instance_translate_musapp.
 - eapply ic_trans; [apply instance_translate_conv_parent; exact HC|].
   apply ic_core, fc_step, fs_step, instance_translate_musapp.
Qed.

Lemma signature_tag_transport_proved : signature_tag_transport.
Proof.
 intros N S0 i0 S1 i1 c n xs X bs HP Hsz Hxs HC Hpos Hbs Hmem Hcov.
 set (B0 := instance_translate (branches (TApp S0 i0))).
 set (L0 := instance_translate (labels (TApp S0 i0))).
 set (B1 := instance_translate (branches (TApp S1 i1))).
 set (L1 := instance_translate (labels (TApp S1 i1))).
 set (P := exists xs', step xs xs').
 assert (Hdead : forall B d,
   cjoin (phi_erase B0) (phi_erase B) ->
   cjoin (phi_erase c) (phi_erase d) -> instance_dead (TApp B d) -> P).
 { intros B d HB Hd HD. unfold P.
   eapply instance_dead_progress; [exact HP|exact Hsz|exact Hxs| |exact HD].
   cbn. apply cjoin_interp_parent; [apply cjoin_app_parent; [|exact Hd]|apply cjoin_refl].
   eapply cjoin_trans; [apply cjoin_sym; exact (instance_erased_join (branches (TApp S0 i0)))|exact HB]. }
 assert (HM : joined_mem (phi_erase c) (phi_erase L0)).
 { eapply joined_mem_transport; [apply spine_mem_joined; exact Hmem|].
   apply cjoin_sym, instance_erased_join. }
 assert (HCov : joined_covers bs (phi_erase L1)).
 { eapply joined_covers_transport; [apply covers_joined; exact Hcov|].
   apply cjoin_sym, instance_erased_join. }
 destruct (translated_instances_join _ _ _ _ HC) as [t [Hleft Hright]].
 assert (Hs : instance_observation B0
    (fun L => joined_mem (phi_erase c) (phi_erase L) \/ P) t).
 { eapply instance_path_observation; [| |exact Hleft|].
   - intros L L' HLL [Hm|Hp]; [left; eapply joined_mem_transport; eassumption|right; exact Hp].
   - intros B L L' HB Hpl [Hm|Hp]; [|right; exact Hp].
     eapply prune_labels_joined_mem; [exact Hpl|exact Hm|].
     intros d Hd HD. eapply Hdead; eassumption.
   - exists B0, L0, (instance_translate i0). split; [reflexivity|].
     split; [apply cjoin_refl|left; exact HM]. }
 assert (Ht : instance_observation B1
    (fun L => joined_covers bs (phi_erase L)) t).
 { eapply instance_path_observation; [| |exact Hright|].
   - intros L L' HLL Hcov'. eapply joined_covers_transport; eassumption.
   - intros B L L' HB Hpl Hcov'. eapply prune_labels_joined_covers; eassumption.
   - exists B1, L1, (instance_translate i1). split; [reflexivity|].
     split; [apply cjoin_refl|exact HCov]. }
 destruct Hs as [B [L [i [Heq [HB [Hm|Hp]]]]]]; [|right; exact Hp].
 destruct Ht as [B' [L' [i' [Heq' [HB' Hcov']]]]].
 unfold signature_instance in Heq, Heq'. rewrite Heq in Heq'. inversion Heq'; subst.
 destruct (joined_mem_covered _ _ _ Hm Hcov') as [d [Hd Hcd]].
 left; exists d. split; [exact Hd|]. eapply joined_tag_position; eassumption.
Qed.
Print Assumptions signature_tag_transport_proved.

Theorem progress_without_signature_axiom : forall t A, check [] t A ->
 value t \/ exists t', step t t'.
Proof. apply progress_from_signature_tag_transport, signature_tag_transport_proved. Qed.
Print Assumptions progress_without_signature_axiom.
