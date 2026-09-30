From Stdlib Require Import List Arith String Bool Lia.
Require Export OpenSignaturesRowTyping.
Import ListNotations.

Lemma handler_motive_beta : forall IT rs X Y a,
  let branches := row_branches IT rs in
  let e := fresh [IT; branches; X; Y] in
  root_step (TApp (handler_motive IT rs X Y) a) =
  Some (TPi (S e) (TInterp IT (TApp branches a) X) Y).
Proof.
  intros IT rs X Y a branches e. unfold handler_motive. fold branches e.
  cbn [root_step].
  rewrite subst_constant_pi by (apply fresh_not_free; cbn; tauto).
  change (Some (TPi (S e)
    (TInterp (subst a e IT)
      (TApp (subst a e branches) (if e =? e then a else TVar e)) (subst a e X)) Y) =
    Some (TPi (S e) (TInterp IT (TApp branches a) X) Y)).
  rewrite Nat.eqb_refl, !subst_fresh by (apply fresh_not_free; cbn; tauto).
  reflexivity.
Qed.

Lemma handler_motive_position : forall IT rs X Y n name D,
  nth_error rs n = Some (name, D) ->
  conv (TApp (handler_motive IT rs X Y) (enum_position n))
    (arrow (TInterp IT D X) Y).
Proof.
  intros IT rs X Y n name D Hnth.
  eapply cv_trans; [apply cv_step, st_root, handler_motive_beta|].
  eapply cv_trans with
    (u := arrow (TInterp IT (TApp (row_branches IT rs) (enum_position n)) X) Y).
  - apply cv_alpha, constant_pi_alpha.
    + eapply above_fresh_not_free with (ts := [IT; row_branches IT rs; X; Y]);
        [cbn; tauto|lia].
    + apply fresh_not_free; cbn; auto.
  - apply arrow_conversion; [|apply cv_refl].
    apply cv_compatible, cp_TInterp; try apply cv_refl.
    eapply row_branches_position; exact Hnth.
Qed.

Lemma handler_motive_application : forall IT rs X Y a,
  conv (TApp (handler_motive IT rs X Y) a)
    (arrow (TInterp IT (TApp (row_branches IT rs) a) X) Y).
Proof.
  intros. eapply cv_trans; [apply cv_step, st_root, handler_motive_beta|].
  apply cv_alpha, constant_pi_alpha.
  - eapply above_fresh_not_free with (ts := [IT; row_branches IT rs; X; Y]);
      [cbn; tauto|lia].
  - apply fresh_not_free; cbn; auto.
Qed.

Lemma forall2_nth : forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys -> forall n a b,
  nth_error xs n = Some a -> nth_error ys n = Some b -> R a b.
Proof.
  intros A B R xs ys H; induction H; intros [|n] a b Ha Hb;
    cbn in *; try discriminate; eauto; inversion Ha; inversion Hb; subst; assumption.
Qed.

Lemma forall2_length : forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys -> List.length ys = List.length xs.
Proof. intros A B R xs ys H; induction H; cbn; congruence. Qed.

Lemma enum_tail_application : forall x P a,
  ~ In x (free_vars P) ->
  conv (TApp (TLam x (TApp P (TESucc (TVar x)))) a) (TApp P (TESucc a)).
Proof.
  intros x P a Hx. apply cv_step, st_root.
  change (Some (TApp (subst a x P) (TESucc (if x =? x then a else TVar x))) =
    Some (TApp P (TESucc a))).
  now rewrite Nat.eqb_refl, subst_fresh.
Qed.

Lemma constant_lambda_application : forall x A t,
  ~ In x (free_vars A) -> conv (TApp (TLam x A) t) A.
Proof.
  intros x A t Hx. apply cv_step, st_root. cbn [root_step].
  now rewrite subst_fresh.
Qed.

Section CaseTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma enum_tail_typing : forall Gamma k tag E P x,
  typing Gamma tag TUId -> typing Gamma E TEnumU ->
  typing Gamma P (arrow (TEnumT (TConsE tag E)) (TSort k)) ->
  ~ In x (free_vars P) ->
  typing Gamma (TLam x (TApp P (TESucc (TVar x)))) (arrow (TEnumT E) (TSort k)).
Proof.
  intros Gamma k tag E P x Htag HE HP Hx.
  pose proof (typing_context _ _ _ HE) as Hctx.
  assert (Hdom : typing Gamma (TEnumT E) (TSort 0)) by now apply ty_enumt.
  assert (Hfull : typing Gamma (TEnumT (TConsE tag E)) (TSort 0))
    by (apply ty_enumt, ty_conse; assumption).
  eapply arrow_intro_fresh; [exact weaken|exact Hdom|apply ty_sort; exact Hctx|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (TEnumT E))
    (TApp (subst (TVar y) x P) (TESucc (if x =? x then TVar y else TVar x))) (TSort k)).
  rewrite Nat.eqb_refl, subst_fresh by exact Hx.
  eapply arrow_app with (A := TEnumT (TConsE tag E)); [exact weaken| | | |].
  - eapply weaken; eassumption.
  - apply ty_sort. eapply wf_cons; eassumption.
  - eapply weaken; eassumption.
  - apply ty_succ; try solve [eapply weaken; eassumption].
    apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
Qed.

Lemma tuple_epi_typing : forall Gamma rs hs k P,
  List.length hs = List.length rs ->
  typing Gamma P (arrow (TEnumT (row_enum rs)) (TSort k)) ->
  (forall n name D h, nth_error rs n = Some (name, D) -> nth_error hs n = Some h ->
    typing Gamma h (TApp P (enum_position n))) ->
  typing Gamma (tuple hs) (TEPi k (row_enum rs) P).
Proof.
  intros Gamma rs. induction rs as [|[name D] rs IH];
    intros [|h hs] k P Hlen HP Htyped; cbn in Hlen; try discriminate.
  - eapply ty_conv with (A := TUnitT).
    + apply ty_unit. eapply typing_context; exact HP.
    + apply ty_epi; [apply ty_nile; eapply typing_context; exact HP|exact HP].
    + apply cv_sym, cv_step, st_root. reflexivity.
  - pose proof (typing_context _ _ _ HP) as Hctx.
    assert (Htag : typing Gamma (TTag name) TUId) by now apply ty_tag.
    assert (HE : typing Gamma (row_enum rs) TEnumU) by now apply row_enum_typing.
    pose (x := fresh [TTag name; row_enum rs; P]).
    pose (Q := TLam x (TApp P (TESucc (TVar x)))).
    assert (Hx : ~ In x (free_vars P)) by (apply fresh_not_free; cbn; auto).
    assert (HQ : typing Gamma Q (arrow (TEnumT (row_enum rs)) (TSort k)))
      by (eapply enum_tail_typing; eassumption).
    assert (Hhead : typing Gamma (TApp P TEZero) (TSort k)).
    { eapply arrow_app with (A := TEnumT (TConsE (TTag name) (row_enum rs)));
        [exact weaken| |now apply ty_sort|exact HP|];
        auto using ty_enumt, ty_conse, ty_zero. }
    assert (Htail : typing Gamma (TEPi k (row_enum rs) Q) (TSort k)) by now apply ty_epi.
    eapply ty_conv with (A := product (TApp P TEZero) (TEPi k (row_enum rs) Q)).
    + apply product_pair with (j := k) (k := k); [exact weaken|exact Hhead|exact Htail| |].
      * exact (Htyped 0 name D h eq_refl eq_refl).
      * apply IH; [lia|exact HQ|]. intros n tag T h' Hnth Hhs.
        eapply ty_conv with (A := TApp P (enum_position (S n))).
        -- apply (Htyped (S n) tag T h'); assumption.
        -- eapply arrow_app with (A := TEnumT (row_enum rs));
             [exact weaken|now apply ty_enumt|now apply ty_sort|exact HQ|].
           eapply row_position_typing; eassumption.
        -- apply cv_sym, enum_tail_application. exact Hx.
    + apply ty_epi; [apply ty_conse; assumption|exact HP].
    + apply cv_sym, cv_step, st_root. reflexivity.
Qed.

Lemma handler_motive_typing : forall Gamma IT rs X Y k,
  row_input Gamma IT rs -> typing Gamma X (Family IT) -> typing Gamma Y (TSort k) ->
  typing Gamma (handler_motive IT rs X Y) (arrow (TEnumT (row_enum rs)) (TSort k)).
Proof.
  intros Gamma IT rs X Y k [HIT [Hnames Hrows]] HX HY.
  pose proof (typing_context _ _ _ HIT) as Hctx.
  pose (branches := row_branches IT rs).
  pose (e := fresh [IT; branches; X; Y]).
  assert (HE : typing Gamma (TEnumT (row_enum rs)) (TSort 0))
    by (apply ty_enumt; now apply row_enum_typing).
  assert (HD : typing Gamma branches (arrow (TEnumT (row_enum rs)) (TIDesc IT)))
    by (apply row_branches_from_weakening; assumption).
  assert (Hp : ~ In (S e) (free_vars Y)).
  { eapply above_fresh_not_free with (ts := [IT; branches; X; Y]); [cbn; tauto|unfold e; lia]. }
  unfold handler_motive. fold branches e.
  eapply arrow_intro_fresh; [exact weaken|exact HE|now apply ty_sort|].
  intros y Hy Hfree.
  pose proof (handler_motive_beta IT rs X Y (TVar y)) as Hbeta.
  change (Some (subst (TVar y) e
    (TPi (S e) (TInterp IT (TApp branches (TVar e)) X) Y)) =
    Some (TPi (S e) (TInterp IT (TApp branches (TVar y)) X) Y)) in Hbeta.
  apply (f_equal (fun o : option term => match o with Some tm => tm | None => TUnit end)) in Hbeta.
  change (subst (TVar y) e (TPi (S e) (TInterp IT (TApp branches (TVar e)) X) Y) =
    TPi (S e) (TInterp IT (TApp branches (TVar y)) X) Y) in Hbeta.
  rewrite Hbeta.
  change (TSort k) with (TSort (Nat.max 0 k)).
  apply constant_pi_formation; [exact weaken| | |exact Hp].
  - apply ty_interp; try solve [eapply weaken; eassumption].
    eapply arrow_app with (A := TEnumT (row_enum rs)); [exact weaken| | | |].
    + eapply weaken; eassumption.
    + apply ty_idesc. eapply weaken; eassumption.
    + eapply weaken; eassumption.
    + apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
  - eapply weaken; eassumption.
Qed.

Lemma row_handlers_tuple : forall Gamma IT rs X Y k hs,
  row_input Gamma IT rs -> typing Gamma X (Family IT) -> typing Gamma Y (TSort k) ->
  Forall2 (fun entry h => typing Gamma h (arrow (TInterp IT (snd entry) X) Y)) rs hs ->
  typing Gamma (tuple hs) (TEPi k (row_enum rs) (handler_motive IT rs X Y)).
Proof.
  intros Gamma IT rs X Y k hs Hinput HX HY Hhandlers.
  pose proof (typing_context _ _ _ HY) as Hctx.
  assert (HP : typing Gamma (handler_motive IT rs X Y)
    (arrow (TEnumT (row_enum rs)) (TSort k))) by now apply handler_motive_typing.
  apply tuple_epi_typing; [eapply forall2_length; exact Hhandlers|exact HP|].
  intros n name D h Hnth Hhs. eapply ty_conv with (A := arrow (TInterp IT D X) Y).
  - exact (forall2_nth _ _ _ _ _ Hhandlers n (name,D) h Hnth Hhs).
  - eapply arrow_app with (A := TEnumT (row_enum rs)); [exact weaken| |now apply ty_sort|exact HP|].
    + apply ty_enumt. now apply row_enum_typing.
    + eapply row_position_typing; eassumption.
  - apply cv_sym. eapply handler_motive_position; exact Hnth.
Qed.

Lemma dead_handler_typing : forall Gamma k A Y d,
  typing Gamma A (TSort 0) -> typing Gamma Y (TSort k) ->
  typing Gamma d (arrow A Bot) ->
  typing Gamma (dead_handler k Y d) (arrow A Y).
Proof.
  intros Gamma k A Y d HA HY Hd. pose proof (typing_context _ _ _ HA) as Hctx.
  pose (p := fresh [Y; d]).
  assert (HpY : ~ In p (free_vars Y)) by (apply fresh_not_free; cbn; auto).
  assert (Hpd : ~ In p (free_vars d)) by (apply fresh_not_free; cbn; auto).
  assert (HpQ : ~ In p (free_vars (constant Y))) by (rewrite constant_free_vars; exact HpY).
  unfold dead_handler. fold p. eapply arrow_intro_fresh; [exact weaken|exact HA|exact HY|].
  intros y Hy Hfree.
  change (typing (extend Gamma y A)
    (TSwitch k TNilE (subst (TVar y) p (constant Y)) TUnit
      (TApp (subst (TVar y) p d) (if p =? p then TVar y else TVar p))) Y).
  rewrite Nat.eqb_refl, !subst_fresh by assumption.
  apply abort_from_weakening; [exact weaken|eapply weaken; eassumption|].
  eapply arrow_app with (A := A); [exact weaken|eapply weaken; eassumption| | |].
  - apply ty_enumt, ty_nile. eapply wf_cons; eassumption.
  - eapply weaken; eassumption.
  - apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
Qed.

Lemma row_map_typing : forall Gamma k IT rs X Y hs,
  row_input Gamma IT rs -> typing Gamma X (Family IT) -> typing Gamma Y (TSort k) ->
  typing Gamma (tuple hs) (TEPi k (row_enum rs) (handler_motive IT rs X Y)) ->
  typing Gamma (row_map k IT rs X Y hs) (arrow (TInterp IT (row_code IT rs) X) Y).
Proof.
  intros Gamma k IT rs X Y hs Hinput HX HY Hhs.
  destruct Hinput as [HIT [Hnames Hrows]].
  pose proof (typing_context _ _ _ HIT) as Hctx.
  pose (P := handler_motive IT rs X Y).
  pose (p := fresh [IT; row_tuple rs; X; Y; P; tuple hs]).
  assert (Hdom : typing Gamma (TInterp IT (row_code IT rs) X) (TSort 0)).
  { apply ty_interp; [exact HIT| |exact HX].
    apply row_code_from_weakening; [exact weaken|repeat split; assumption]. }
  assert (Hbranches : typing Gamma (row_branches IT rs)
    (arrow (TEnumT (row_enum rs)) (TIDesc IT)))
    by (apply row_branches_from_weakening; assumption).
  assert (HP : typing Gamma P (arrow (TEnumT (row_enum rs)) (TSort k))).
  { apply handler_motive_typing; [repeat split; assumption|exact HX|exact HY]. }
  assert (HpP : ~ In p (free_vars P)) by (apply fresh_not_free; cbn; tauto).
  assert (Hphs : ~ In p (free_vars (tuple hs))) by (apply fresh_not_free; cbn; tauto).
  unfold row_map. fold P p. eapply arrow_intro_fresh; [exact weaken|exact Hdom|exact HY|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (TInterp IT (row_code IT rs) X))
    (TApp (TSwitch k (subst (TVar y) p (row_enum rs)) (subst (TVar y) p P)
      (subst (TVar y) p (tuple hs)) (TFst (if p =? p then TVar y else TVar p)))
      (TSnd (if p =? p then TVar y else TVar p))) Y).
  rewrite Nat.eqb_refl.
  rewrite (subst_fresh (row_enum rs)) by (rewrite row_enum_closed; cbn; tauto).
  rewrite (subst_fresh P) by exact HpP.
  rewrite (subst_fresh (tuple hs)) by exact Hphs.
  pose (Delta := extend Gamma y (TInterp IT (row_code IT rs) X)).
  assert (HDelta : wf Delta) by (eapply wf_cons; eassumption).
  assert (HIT' : typing Delta IT (TSort 0)) by (eapply weaken; eassumption).
  assert (HX' : typing Delta X (Family IT)) by (eapply weaken; eassumption).
  assert (HY' : typing Delta Y (TSort k)) by (eapply weaken; eassumption).
  assert (HE' : typing Delta (row_enum rs) TEnumU) by now apply row_enum_typing.
  assert (Hbranches' : typing Delta (row_branches IT rs)
    (arrow (TEnumT (row_enum rs)) (TIDesc IT))) by (eapply weaken; eassumption).
  assert (Hvar : typing Delta (TVar y) (TInterp IT (row_code IT rs) X))
    by (apply ty_var; [exact HDelta|apply lookup_extend_same]).
  assert (Hfst : typing Delta (TFst (TVar y)) (TEnumT (row_enum rs)))
    by (eapply interp_choice_fst; eassumption).
  assert (Hsnd : typing Delta (TSnd (TVar y))
    (TInterp IT (TApp (row_branches IT rs) (TFst (TVar y))) X))
    by (eapply interp_choice_snd; eassumption).
  assert (Hpart : typing Delta (TInterp IT (TApp (row_branches IT rs) (TFst (TVar y))) X) (TSort 0)).
  { apply ty_interp; [exact HIT'| |exact HX'].
    eapply arrow_app with (A := TEnumT (row_enum rs)); eauto using ty_enumt, ty_idesc. }
  eapply arrow_app; [exact weaken|exact Hpart|exact HY'| |exact Hsnd].
  eapply ty_conv with (A := TApp P (TFst (TVar y))).
  - apply ty_switch; try assumption; eapply weaken; eassumption.
  - apply arrow_formation; eassumption.
  - apply handler_motive_application.
Qed.

Lemma close_case_constant_typing : forall Gamma k IT F G i Y b t q,
  close_input Gamma IT F G i -> typing Gamma Y (TSort k) -> ~ In q (free_vars Y) ->
  typing Gamma b (arrow (payload IT F G i) Y) -> typing Gamma t (CloseAt IT F G i) ->
  typing Gamma (TCloseCase k IT F G i (TLam q Y) b t) Y.
Proof.
  intros Gamma k IT F G i Y b t q Hinput HY Hq Hb Ht.
  destruct Hinput as [HIT [HF [HG Hi]]].
  pose (C := payload IT F G i). pose (Q := TLam q Y).
  assert (HC : typing Gamma C (TSort 0))
    by (apply payload_formation; [exact weaken|repeat split; assumption]).
  assert (HB : typing Gamma (CloseAt IT F G i) (TSort 0))
    by (apply close_at_formation; assumption).
  assert (Hctx : wf Gamma) by (eapply typing_context; exact HIT).
  assert (HQ : typing Gamma Q (arrow (CloseAt IT F G i) (TSort k)))
    by (eapply constant_lambda_typing; eauto using ty_sort).
  pose (x := fresh [IT; F; G; i; Q]).
  assert (HxQ : ~ In x (free_vars Q)) by (apply fresh_not_free; cbn; tauto).
  assert (HxY : ~ In x (free_vars Y)).
  { intro Hin. apply HxQ. apply in_in_remove; [intro E; rewrite E in Hin; contradiction|exact Hin]. }
  assert (Hmethod : typing Gamma (close_case_method IT F G i Q) (TSort k)).
  { change (typing Gamma (TPi x C (TApp Q (TIn (TVar x)))) (TSort (Nat.max 0 k))).
    apply pi_formation_fresh; [exact HC|]. intros y Hy Hfree.
    change (typing (extend Gamma y C)
      (TApp (subst (TVar y) x Q) (TIn (if x =? x then TVar y else TVar x))) (TSort k)).
    rewrite Nat.eqb_refl, subst_fresh by exact HxQ.
    eapply arrow_app with (A := CloseAt IT F G i); [exact weaken| | | |].
    - eapply weaken; eassumption.
    - apply ty_sort. eapply wf_cons; eassumption.
    - eapply weaken; eassumption.
    - apply ty_in_close; try solve [eapply weaken; eassumption].
      apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same]. }
  assert (Hb' : typing Gamma b (close_case_method IT F G i Q)).
  { eapply ty_conv; [exact Hb|exact Hmethod|].
    eapply cv_trans with (u := TPi x C Y).
    - apply cv_alpha, constant_pi_alpha; [apply fresh_not_free; cbn; auto|exact HxY].
    - apply cv_compatible, cp_TPi; [apply cv_refl|].
      apply cv_sym, constant_lambda_application. exact Hq. }
  eapply ty_conv with (A := TApp Q t); [|exact HY|now apply constant_lambda_application].
  apply ty_close_case; assumption.
Qed.

Lemma case_term_typing : forall Gamma k IT F G i Y rs hs t,
  close_input Gamma IT F G i -> row_view Gamma IT (TApp F i) rs ->
  typing Gamma Y (TSort k) -> typing Gamma t (CloseAt IT F G i) ->
  typing Gamma (tuple hs)
    (TEPi k (row_enum rs) (handler_motive IT rs (carrier IT G) Y)) ->
  typing Gamma (case_term k IT F G i Y rs hs t) Y.
Proof.
  intros Gamma k IT F G i Y rs hs t Hinput Hview HY Ht Hhs.
  destruct Hview as [rs Hrows HD Hconv].
  assert (HX : typing Gamma (carrier IT G) (Family IT)).
  { destruct Hinput as [HIT [HF [HG Hi]]]. apply ty_close; assumption. }
  assert (HC : typing Gamma (payload IT F G i) (TSort 0))
    by (apply payload_formation; assumption).
  apply close_case_constant_typing; try assumption.
  - apply fresh_not_free; cbn; tauto.
  - eapply ty_conv with
      (A := arrow (TInterp IT (row_code IT rs) (carrier IT G)) Y).
    + apply row_map_typing; assumption.
    + apply arrow_formation; eassumption.
    + apply arrow_conversion; [|apply cv_refl].
      apply cv_compatible, cp_TInterp; try apply cv_refl. now apply cv_sym.
Qed.

End CaseTyping.
