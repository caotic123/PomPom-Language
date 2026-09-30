(* Live row handlers have a unique action on each inhabited closed payload.
   This is the row-dispatch component of coherence, not function extensionality. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesObservationalLaws.
Import ListNotations.

Lemma closed_bottom_absurd : forall t, ~ typing empty_ctx t Bot.
Proof.
  intros t HT; destruct (observation_termination _ _ HT) as [v [HE HV]].
  eapply (bottom_no_value raw_join_typed); [|exact HV].
  eapply observation_eval_preservation; eassumption.
Qed.

Lemma dead_payload_absurd : forall IT D X d xs,
  dead empty_ctx IT D X d -> typing empty_ctx xs (TInterp IT D X) -> False.
Proof.
  intros IT D X d xs HD Hxs; apply (closed_bottom_absurd (TApp d xs)).
  eapply arrow_apply_regular; [exact named_type_correctness| |exact Hxs].
  exact (dead_from_rules named_weakening _ _ _ _ _ HD).
Qed.

Theorem row_handlers_live_at : forall IT X Y target source hs,
  row_handlers empty_ctx IT X Y target source hs ->
  forall n name D xs,
  nth_error source n = Some (name,D) ->
  typing empty_ctx xs (TInterp IT D X) ->
  exists m D', nth_error target m = Some (name,D') /\
    nth_error hs n = Some (retag_handler m).
Proof.
  intros IT X Y target source hs H; induction H;
    intros [|j] tag C xs Hnth Hxs; cbn [nth_error] in Hnth; try discriminate.
  - inversion Hnth; subst; eauto.
  - eapply IHrow_handlers; eassumption.
  - inversion Hnth; subst; exfalso; eapply dead_payload_absurd; eassumption.
  - eapply IHrow_handlers; eassumption.
Qed.

Lemma switch_handlers_position : forall source hs n name D h k P,
  nth_error source n = Some (name,D) -> nth_error hs n = Some h ->
  eval (TSwitch k (row_enum source) P (tuple hs) (enum_position n)) h.
Proof.
  induction source as [|[tag C] source IH]; intros [|h0 hs] [|n] name D h k P Hs Hh;
    cbn in Hs, Hh; try discriminate.
  - inversion Hh; subst. eapply ev_step; [apply st_root; reflexivity|constructor].
  - eapply ev_step; [apply st_root; reflexivity|]. eapply IH; eassumption.
Qed.

Lemma row_map_beta : forall k IT rs X Y hs a,
  conv (TApp (row_map k IT rs X Y hs) a)
    (TApp (TSwitch k (row_enum rs) (handler_motive IT rs X Y)
      (tuple hs) (TFst a)) (TSnd a)).
Proof.
  intros k IT rs X Y hs a.
  unfold row_map; set (P := handler_motive IT rs X Y).
  set (p := fresh [IT; row_tuple rs; X; Y; P; tuple hs]).
  apply cv_step, st_root; cbn [root_step].
  change (Some (TApp
    (TSwitch k (subst a p (row_enum rs)) (subst a p P) (subst a p (tuple hs))
      (TFst (if p =? p then a else TVar p)))
    (TSnd (if p =? p then a else TVar p))) =
    Some (TApp (TSwitch k (row_enum rs) P (tuple hs) (TFst a)) (TSnd a))).
  rewrite Nat.eqb_refl.
  rewrite (subst_fresh (row_enum rs)) by (rewrite row_enum_closed; tauto).
  rewrite (subst_fresh P), (subst_fresh (tuple hs));
    try reflexivity; apply fresh_not_free; cbn; tauto.
Qed.

Lemma row_map_selected : forall k IT rs X Y hs n name D h xs,
  nth_error rs n = Some (name,D) -> nth_error hs n = Some h ->
  conv (TApp (row_map k IT rs X Y hs) (TPair (enum_position n) xs)) (TApp h xs).
Proof.
  intros k IT rs X Y hs n name D h xs Hrs Hhs.
  eapply cv_trans; [apply row_map_beta|].
  eapply cv_trans with (u:=TApp
    (TSwitch k (row_enum rs) (handler_motive IT rs X Y) (tuple hs) (enum_position n)) xs).
  - apply cv_compatible, cp_TApp.
    + apply cv_compatible, cp_TSwitch; try apply cv_refl.
      apply cv_step, st_root; reflexivity.
    + apply cv_step, st_root; reflexivity.
  - apply cv_compatible, cp_TApp; [|apply cv_refl].
    apply eval_conversion; eapply switch_handlers_position; eassumption.
Qed.

Lemma retag_handler_beta : forall n xs,
  conv (TApp (retag_handler n) xs) (TPair (enum_position n) xs).
Proof.
  intros n xs; unfold retag_handler; apply cv_step, st_root; cbn [root_step].
  change (Some (TPair (subst xs (fresh [enum_position n]) (enum_position n))
    (if fresh [enum_position n] =? fresh [enum_position n] then xs else TVar (fresh [enum_position n]))) =
    Some (TPair (enum_position n) xs)).
  rewrite Nat.eqb_refl, subst_fresh by (apply fresh_not_free; cbn; auto).
  reflexivity.
Qed.

Theorem row_maps_closed_branch_coherence : forall IT X Y target source hs hs' n name D xs,
  NoDup (row_names target) ->
  row_handlers empty_ctx IT X Y target source hs ->
  row_handlers empty_ctx IT X Y target source hs' ->
  nth_error source n = Some (name,D) ->
  typing empty_ctx xs (TInterp IT D X) ->
  conv (TApp (row_map 0 IT source X Y hs) (TPair (enum_position n) xs))
       (TApp (row_map 0 IT source X Y hs') (TPair (enum_position n) xs)).
Proof.
  intros IT X Y target source hs hs' n name D xs Hnd Hh Hh' Hn Hxs.
  destruct (row_handlers_live_at _ _ _ _ _ _ Hh _ _ _ _ Hn Hxs)
    as [m [C [Hm HC]]].
  destruct (row_handlers_live_at _ _ _ _ _ _ Hh' _ _ _ _ Hn Hxs)
    as [m' [C' [Hm' HC']]].
  assert (m=m') by (eapply row_position_unique; eassumption); subst m'.
  eapply cv_trans; [eapply row_map_selected; eassumption|].
  apply cv_sym; eapply row_map_selected; eassumption.
Qed.

Theorem row_payload_canonical : forall IT rs X t,
  row_input empty_ctx IT rs -> typing empty_ctx X (Family IT) ->
  typing empty_ctx t (TInterp IT (row_code IT rs) X) ->
  exists name D n xs, nth_error rs n = Some (name,D) /\
    conv t (TPair (enum_position n) xs) /\
    typing empty_ctx xs (TInterp IT D X).
Proof.
  intros IT rs X t Hrow HX HT.
  destruct Hrow as [HIT [Hnames Hcodes]].
  assert (Hbranches : typing empty_ctx (row_branches IT rs)
    (arrow (TEnumT (row_enum rs)) (TIDesc IT))).
  { apply row_branches_from_weakening; [exact named_weakening|exact HIT|exact Hcodes]. }
  destruct (observation_termination _ _ HT) as [v [HE HV]].
  pose proof (observation_eval_preservation _ _ _ _ HT HE) as Hvt.
  destruct (choice_value_shape _ _ _ _ _ _ HIT (row_enum_typing _ rs wf_nil)
    Hbranches HX Hvt HV) as [a [b ->]].
  assert (Ha : typing empty_ctx a (TEnumT (row_enum rs))).
  { eapply named_preservation with (t:=TFst (TPair a b)).
    - eapply interp_choice_fst; eauto using named_weakening, row_enum_typing, wf_nil.
    - apply st_root; reflexivity. }
  destruct (enum_normal_form named_preservation observation_termination _ _ Ha)
    as [n [name [D [Hnth Han]]]].
  assert (Hb : typing empty_ctx b
    (TInterp IT (TApp (row_branches IT rs) (TFst (TPair a b))) X)).
  { eapply named_preservation with (t:=TSnd (TPair a b)).
    - eapply interp_choice_snd; eauto using named_weakening, row_enum_typing, wf_nil.
    - apply st_root; reflexivity. }
  exists name,D,n,b; split; [exact Hnth|]; split.
  - eapply cv_trans; [exact (eval_conversion _ _ HE)|].
    apply cv_compatible, cp_TPair; [exact (eval_conversion _ _ Han)|apply cv_refl].
  - eapply ty_conv; [exact Hb| |].
    + apply ty_interp; [exact HIT| |exact HX].
      apply Forall_forall with (x:=(name,D)) in Hcodes;
        [exact Hcodes|eapply nth_error_In; exact Hnth].
    + apply interp_conversion.
      eapply cv_trans with (u:=TApp (row_branches IT rs) (enum_position n)).
      * apply cv_compatible, cp_TApp; [apply cv_refl|].
        eapply cv_trans; [apply cv_step, st_root; reflexivity|now apply eval_conversion].
      * eapply row_branches_position; eassumption.
Qed.

Theorem row_maps_closed_pointwise_coherence : forall IT X Y target source hs hs' t,
  NoDup (row_names target) -> row_input empty_ctx IT source ->
  typing empty_ctx X (Family IT) ->
  row_handlers empty_ctx IT X Y target source hs ->
  row_handlers empty_ctx IT X Y target source hs' ->
  typing empty_ctx t (TInterp IT (row_code IT source) X) ->
  conv (TApp (row_map 0 IT source X Y hs) t)
       (TApp (row_map 0 IT source X Y hs') t).
Proof.
  intros IT X Y target source hs hs' t Hnd Hrow HX Hh Hh' HT.
  destruct (row_payload_canonical _ _ _ _ Hrow HX HT)
    as [name [D [n [xs [Hnth [HC Hxs]]]]]].
  eapply cv_trans with (u:=TApp (row_map 0 IT source X Y hs) (TPair (enum_position n) xs)).
  - apply cv_compatible, cp_TApp; auto using cv_refl.
  - eapply cv_trans.
    + eapply row_maps_closed_branch_coherence; eassumption.
    + apply cv_compatible, cp_TApp; auto using cv_refl, cv_sym.
Qed.

Print Assumptions row_handlers_live_at.
Print Assumptions row_maps_closed_branch_coherence.
Print Assumptions row_payload_canonical.
Print Assumptions row_maps_closed_pointwise_coherence.
