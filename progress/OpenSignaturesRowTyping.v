(* Row computation is axiom-free. Row typing assumes weakening explicitly. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesDataTyping OpenSignaturesElaboration.
Import ListNotations.

Lemma row_enum_typing : forall Gamma rs,
  wf Gamma -> typing Gamma (row_enum rs) TEnumU.
Proof.
  intros Gamma rs Hctx. induction rs as [|[name D] rs IH]; cbn;
    auto using ty_nile, ty_conse, ty_tag.
Qed.

Lemma row_enum_closed : forall rs, free_vars (row_enum rs) = [].
Proof. induction rs as [|[name D] rs IH]; cbn; auto. Qed.

Lemma row_tuple_free : forall rs x,
  In x (free_vars (row_tuple rs)) ->
  exists D, In D (map snd rs) /\ In x (free_vars D).
Proof.
  induction rs as [|[name D] rs IH]; intros x Hin; cbn in Hin; [contradiction|].
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - exists D; cbn; auto.
  - destruct (IH x Hin) as [T [HT Hx]]. exists T; cbn; auto.
Qed.

Lemma constant_epi_cons : forall k tag E A,
  conv (TEPi k (TConsE tag E) (constant A))
    (product A (TEPi k E (constant A))).
Proof.
  intros k tag E A. eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  apply product_conversion; [apply constant_application|].
  apply cv_compatible, cp_TEPi; [apply cv_refl|].
  apply constant_lambda_conversion; [|apply constant_application].
  intro Hin. apply (fresh_not_free [tag; E; constant A] (constant A) ltac:(cbn; auto)).
  now apply constant_free_vars.
Qed.

Lemma row_tuple_fresh : forall IT rs,
  ~ In (fresh (IT :: map snd rs)) (free_vars (row_tuple rs)).
Proof.
  intros IT rs Hin. destruct (row_tuple_free _ _ Hin) as [D [HD HinD]].
  exact (fresh_not_free (IT :: map snd rs) D ltac:(cbn; auto) HinD).
Qed.

Lemma row_branches_beta : forall IT rs a,
  root_step (TApp (row_branches IT rs) a) =
  Some (TSwitch 1 (row_enum rs)
    (TLam (S (fresh (IT :: map snd rs))) (TIDesc IT)) (row_tuple rs) a).
Proof.
  intros IT rs a. unfold row_branches. cbn [root_step].
  change (Some (TSwitch 1 (subst a (fresh (IT :: map snd rs)) (row_enum rs))
    (subst a (fresh (IT :: map snd rs)) (TLam (S (fresh (IT :: map snd rs))) (TIDesc IT)))
    (subst a (fresh (IT :: map snd rs)) (row_tuple rs))
    (if fresh (IT :: map snd rs) =? fresh (IT :: map snd rs) then a else TVar (fresh (IT :: map snd rs)))) =
    Some (TSwitch 1 (row_enum rs)
      (TLam (S (fresh (IT :: map snd rs))) (TIDesc IT)) (row_tuple rs) a)).
  rewrite Nat.eqb_refl.
  rewrite (subst_fresh (row_enum rs)) by (rewrite row_enum_closed; cbn; tauto).
  rewrite (subst_fresh (TLam _ _)).
  - now rewrite (subst_fresh (row_tuple rs)) by apply row_tuple_fresh.
  - cbn [free_vars]. rewrite in_remove_iff. intros [Hin _].
    exact (fresh_not_free (IT :: map snd rs) IT ltac:(cbn; auto) Hin).
Qed.

Lemma switch_row_position : forall rs n name D k P,
  nth_error rs n = Some (name, D) ->
  eval (TSwitch k (row_enum rs) P (row_tuple rs) (enum_position n)) D.
Proof.
  induction rs as [|[tag T] rs IH]; intros [|n] name D k P H;
    cbn in H; try discriminate.
  - inversion H; subst. eapply ev_step; [apply st_root; reflexivity|constructor].
  - eapply ev_step; [apply st_root; reflexivity|]. eapply IH; exact H.
Qed.

Lemma row_branches_position : forall IT rs n name D,
  nth_error rs n = Some (name, D) ->
  conv (TApp (row_branches IT rs) (enum_position n)) D.
Proof.
  intros IT rs n name D H.
  eapply cv_trans; [apply cv_step, st_root, row_branches_beta|].
  pose proof (switch_row_position rs n name D 1
    (TLam (S (fresh (IT :: map snd rs))) (TIDesc IT)) H) as Heval.
  induction Heval; eauto using conv.
Qed.

Lemma row_position_typing : forall Gamma rs n name D,
  wf Gamma -> nth_error rs n = Some (name, D) ->
  typing Gamma (enum_position n) (TEnumT (row_enum rs)).
Proof.
  intros Gamma rs. induction rs as [|[tag T] rs IH];
    intros [|n] name D Hctx H; cbn in H; try discriminate; cbn.
  - apply ty_zero; auto using ty_tag, row_enum_typing.
  - apply ty_succ; eauto using ty_tag, row_enum_typing.
Qed.

Section RowTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma row_input_weaken : forall Gamma IT rs x A k,
  row_input Gamma IT rs -> fresh_in Gamma x -> typing Gamma A (TSort k) ->
  row_input (extend Gamma x A) IT rs.
Proof.
  intros Gamma IT rs x A k [HIT [Hnames Hrows]] Hx HA.
  split; [eapply weaken; eassumption|]. split; [exact Hnames|].
  eapply Forall_impl; [|exact Hrows]. intros entry Hentry. eapply weaken; eassumption.
Qed.

Lemma constant_epi_formation : forall Gamma k E A,
  typing Gamma E TEnumU -> typing Gamma A (TSort k) ->
  typing Gamma (TEPi k E (constant A)) (TSort k).
Proof.
  intros Gamma k E A HE HA. apply ty_epi; [exact HE|].
  eapply constant_typing; [exact weaken|exact HA|now apply ty_enumt|].
  apply ty_sort. eapply typing_context; exact HE.
Qed.

Lemma row_tuple_typing : forall Gamma rs A k,
  typing Gamma A (TSort k) ->
  Forall (fun entry => typing Gamma (snd entry) A) rs ->
  typing Gamma (row_tuple rs) (TEPi k (row_enum rs) (constant A)).
Proof.
  intros Gamma rs A k HA Hrows. pose proof (typing_context _ _ _ HA) as Hctx.
  induction Hrows as [|[name D] rs HD Hrows IH].
  - eapply ty_conv with (A := TUnitT); [apply ty_unit; exact Hctx| |].
    + apply constant_epi_formation; [apply ty_nile; exact Hctx|exact HA].
    + apply cv_sym, cv_step, st_root. reflexivity.
  - eapply ty_conv with (A := product A (TEPi k (row_enum rs) (constant A))).
    + eapply product_pair; [exact weaken|exact HA| |exact HD|exact IH].
      apply constant_epi_formation; [now apply row_enum_typing|exact HA].
    + apply constant_epi_formation; [now apply row_enum_typing|exact HA].
    + apply cv_sym, constant_epi_cons.
Qed.

Theorem row_branches_from_weakening : forall Gamma IT rs,
  typing Gamma IT (TSort 0) ->
  Forall (fun entry => typing Gamma (snd entry) (TIDesc IT)) rs ->
  typing Gamma (row_branches IT rs) (arrow (TEnumT (row_enum rs)) (TIDesc IT)).
Proof.
  intros Gamma IT rs HIT Hrows.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  pose (e := fresh (IT :: map snd rs)).
  pose (Q := TLam (S e) (TIDesc IT)).
  assert (HeIT : ~ In e (free_vars IT)) by (apply fresh_not_free; cbn; auto).
  assert (HmIT : ~ In (S e) (free_vars IT)).
  { eapply above_fresh_not_free with (ts := IT :: map snd rs); [cbn; left; reflexivity|unfold e; lia]. }
  assert (HeQ : ~ In e (free_vars Q)).
  { unfold Q. cbn [free_vars]. rewrite in_remove_iff. tauto. }
  assert (HeTuple : ~ In e (free_vars (row_tuple rs))).
  { intro Hin. destruct (row_tuple_free rs e Hin) as [D [HD HeD]].
    apply (fresh_not_free (IT :: map snd rs) D ltac:(cbn; auto)); exact HeD. }
  assert (HE : typing Gamma (TEnumT (row_enum rs)) (TSort 0))
    by (apply ty_enumt; now apply row_enum_typing).
  assert (HD : typing Gamma (TIDesc IT) (TSort 1)) by now apply ty_idesc.
  assert (HQ : typing Gamma Q (arrow (TEnumT (row_enum rs)) (TSort 1))).
  { eapply constant_lambda_typing; [exact weaken|exact HD|exact HE| |exact HmIT].
    apply ty_sort; exact Hctx. }
  assert (HQconv : conv Q (constant (TIDesc IT))).
  { apply constant_lambda_conversion; [exact HmIT|apply cv_refl]. }
  assert (HTuple : typing Gamma (row_tuple rs) (TEPi 1 (row_enum rs) Q)).
  { eapply ty_conv; [apply row_tuple_typing; eassumption| |].
    - apply ty_epi; [now apply row_enum_typing|exact HQ].
    - apply cv_compatible, cp_TEPi; [apply cv_refl|now apply cv_sym]. }
  unfold row_branches. fold e Q.
  eapply arrow_intro_fresh; [exact weaken|exact HE|exact HD|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (TEnumT (row_enum rs)))
    (TSwitch 1 (subst (TVar y) e (row_enum rs)) (subst (TVar y) e Q)
      (subst (TVar y) e (row_tuple rs)) (if e =? e then TVar y else TVar e)) (TIDesc IT)).
  rewrite Nat.eqb_refl.
  rewrite (subst_fresh (row_enum rs)) by (rewrite row_enum_closed; cbn; tauto).
  rewrite (subst_fresh Q) by exact HeQ.
  rewrite (subst_fresh (row_tuple rs)) by exact HeTuple.
  eapply ty_conv with (A := TApp Q (TVar y)).
  - apply ty_switch; try solve [eapply weaken; eassumption].
    + apply row_enum_typing. eapply wf_cons; eassumption.
    + apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
  - eapply weaken; eassumption.
  - eapply cv_trans with (u := TApp (constant (TIDesc IT)) (TVar y)).
    + apply cv_compatible, cp_TApp; [exact HQconv|apply cv_refl].
    + apply constant_application.
Qed.

Theorem row_code_from_weakening : forall Gamma IT rs,
  row_input Gamma IT rs -> typing Gamma (row_code IT rs) (TIDesc IT).
Proof.
  intros Gamma IT rs [HIT [_ Hrows]]. apply ty_ichoice; [exact HIT| |].
  - apply row_enum_typing. eapply typing_context; exact HIT.
  - apply row_branches_from_weakening; assumption.
Qed.

Theorem signature_from_weakening : forall Gamma x IT rs,
  fresh_in Gamma x -> typing Gamma IT (TSort 0) ->
  row_input (extend Gamma x IT) IT rs ->
  typing Gamma (signature x IT rs) (Def IT).
Proof.
  intros Gamma x IT rs Hx HIT Hrows.
  eapply ty_conv with (A := arrow IT (TIDesc IT)).
  - eapply arrow_intro; [exact weaken|exact HIT|now apply ty_idesc|exact Hx|].
    now apply row_code_from_weakening.
  - apply def_formation; assumption.
  - apply cv_alpha, constant_pi_alpha; cbn [free_vars]; apply fresh_not_free; cbn; auto.
Qed.

Lemma row_injection_typing : forall Gamma IT rs X n name D b,
  row_input Gamma IT rs -> typing Gamma X (Family IT) ->
  nth_error rs n = Some (name, D) -> typing Gamma b (TInterp IT D X) ->
  typing Gamma (TPair (enum_position n) b) (TInterp IT (row_code IT rs) X).
Proof.
  intros Gamma IT rs X n name D b Hinput HX Hnth Hb.
  destruct Hinput as [HIT [Hnames Hrows]].
  pose proof (typing_context _ _ _ HIT) as Hctx.
  assert (HE : typing Gamma (row_enum rs) TEnumU) by now apply row_enum_typing.
  assert (HP : typing Gamma (enum_position n) (TEnumT (row_enum rs)))
    by (eapply row_position_typing; eassumption).
  assert (Hbranches : typing Gamma (row_branches IT rs)
    (arrow (TEnumT (row_enum rs)) (TIDesc IT))) by now apply row_branches_from_weakening.
  apply interp_choice_pair; try assumption.
  eapply ty_conv; [exact Hb| |].
  - apply ty_interp; [exact HIT| |exact HX].
    eapply arrow_app with (A := TEnumT (row_enum rs)); eauto using ty_enumt, ty_idesc.
  - apply cv_compatible, cp_TInterp; try apply cv_refl.
    apply cv_sym. eapply row_branches_position; exact Hnth.
Qed.

Lemma close_row_constructor : forall Gamma IT F G i rs n name D b,
  close_input Gamma IT F G i -> row_input Gamma IT rs ->
  conv (TApp F i) (row_code IT rs) -> nth_error rs n = Some (name, D) ->
  typing Gamma b (TInterp IT D (carrier IT G)) ->
  typing Gamma (TIn (TPair (enum_position n) b)) (CloseAt IT F G i).
Proof.
  intros Gamma IT F G i rs n name D b Hinput Hrows Hconv Hnth Hb.
  destruct Hinput as [HIT [HF [HG Hi]]]. apply ty_in_close; try assumption.
  eapply ty_conv with (A := TInterp IT (row_code IT rs) (carrier IT G)).
  - eapply row_injection_typing; [exact Hrows|now apply ty_close|exact Hnth|exact Hb].
  - apply payload_formation; [exact weaken|repeat split; assumption].
  - apply cv_compatible, cp_TInterp; try apply cv_refl. now apply cv_sym.
Qed.

End RowTyping.
