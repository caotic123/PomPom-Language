Require Import Progress SignatureInstances _parent_instance_pruning _luna_instance_conversion _luna_instance_step_prune.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Ltac ic_congruence :=
  first [apply (ic_map TSort)|apply (ic_map TLam)|apply (ic_map TFst)|
    apply (ic_map TSnd)|apply (ic_map TEnumT)|apply (ic_map TESucc)|
    apply (ic_map TIDesc)|apply (ic_map TIVar)|apply (ic_map TMuI)|
    apply (ic_map TIn)|apply (ic_map TList)|apply (ic_map TLNil)|
    apply (ic_map2 TPi)|apply (ic_map2 TApp)|apply (ic_map2 TSigma)|
    apply (ic_map2 TPair)|apply (ic_map2 TConsE)|apply (ic_map2 TEPi)|
    apply (ic_map2 TIProd)|apply (ic_map2 TIPi)|apply (ic_map2 TISig)|
    apply (ic_map2 TIChoice)|apply (ic_map2 TInterp)|apply (ic_map3 TLCons)|
    apply (ic_map4 TSwitch)|apply (ic_map4 TIAll)|apply (ic_map5 TInd)|apply (ic_map5 THyps)];
  intros; try assumption;
  try solve [constructor; assumption];
  try solve [constructor; first [assumption|apply prune_term_refl]].

Lemma instance_translate_conv_parent : forall t u, conv t u ->
  instance_conv (instance_translate t) (instance_translate u).
Proof.
  intros t u H. induction H;
    try solve [cbn [instance_translate]; ic_congruence].
  - apply ic_core, fc_step, fs_step, instance_translate_step; assumption.
  - apply ic_refl.
  - apply ic_sym; assumption.
  - eapply ic_trans; eassumption.
  - cbn [instance_translate]. rewrite instance_translate_lift. apply ic_core, fc_step, fs_eta.
  - eapply ic_phi; eassumption.
  - apply ic_translate_mus; assumption.
  - cbn [instance_translate]. apply (ic_map2 (fun M Q => TCase M Q
       (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)));
      intros; try assumption.
    + apply fs_case1; assumption.
    + apply fs_case2; assumption.
    + apply pt_case; first [assumption|apply prune_term_refl|apply prune_branches_refl].
    + apply pt_case; first [assumption|apply prune_term_refl|apply prune_branches_refl].
  - cbn [instance_translate]. rewrite !map_app. cbn.
    apply (ic_map2 (fun c b => TCase (instance_translate M) (instance_translate Q)
       (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs1 ++
         (c,b) :: map (fun '(c,b) => (instance_translate c, instance_translate b)) bs2)));
      intros; try assumption; try solve [apply fs_case_br1; assumption|apply fs_case_br2; assumption].
    + apply pt_case; try apply prune_term_refl.
      apply prune_branches_app; [apply prune_branches_refl|].
      constructor; first [assumption|apply prune_term_refl|apply prune_branches_refl].
    + apply pt_case; try apply prune_term_refl.
      apply prune_branches_app; [apply prune_branches_refl|].
      constructor; first [assumption|apply prune_term_refl|apply prune_branches_refl].
Qed.
Print Assumptions instance_translate_conv_parent.
