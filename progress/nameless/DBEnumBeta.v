From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBMuBeta.
Import ListNotations.

Lemma reduction_conse : forall a b t, reduction (TConsE a b) t ->
  exists a' b', t = TConsE a' b' /\ rtc reduction a a' /\ rtc reduction b b'.
Proof.
  intros a b t H; inversion H; subst; cbn [root_step] in *; try discriminate;
    eauto 7 using rtc_refl, rtc_one.
Qed.
Lemma conversion_conse : forall a b c d, conv (TConsE a b) (TConsE c d) -> conv a c /\ conv b d.
Proof. apply (conversion_binary TConsE reduction_conse); intros; inversion H; auto. Qed.

Lemma conse_generation : forall Gamma t T, typing Gamma t T -> forall tag E,
  t = TConsE tag E -> typing Gamma tag TUId /\ typing Gamma E TEnumU.
Proof.
  intros Gamma t T H; induction H; intros tag' E' HE; try discriminate; eauto.
  inversion HE; subst; auto.
Qed.
Lemma succ_generation : forall Gamma t T, typing Gamma t T -> forall n,
  t = TESucc n -> exists tag E,
  typing Gamma n (TEnumT E) /\ conv (TEnumT (TConsE tag E)) T.
Proof.
  intros Gamma t T H; induction H; intros nn HE; try discriminate.
  - destruct (IHtyping1 _ HE) as [tag [E [Hn HC]]].
    exists tag,E; split; eauto using cv_trans.
  - destruct (IHtyping _ HE) as [tag [E [Hn HC]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - inversion HE; subst; eauto using cv_refl.
  - destruct (IHtyping1 _ HE) as [tag [E [Hn HC]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.
Lemma succ_inversion : forall Gamma tag E n,
  typing Gamma E TEnumU -> typing Gamma (TESucc n) (TEnumT (TConsE tag E)) ->
  typing Gamma n (TEnumT E).
Proof.
  intros Gamma tag E n HE Hn.
  destruct (succ_generation _ _ _ Hn _ eq_refl) as [tag' [E' [Hn' HC]]].
  apply conversion_enumt, conversion_conse in HC. destruct HC as [_ HC].
  eapply ty_conv; [exact Hn'|now apply ty_enumt|apply cv_compatible, cp_TEnumT; exact HC].
Qed.

Definition enum_tail_motive P := TLam (TApp (lift 1 0 P) (TESucc (TVar 0))).

Lemma enum_tail_motive_typing : forall Gamma k tag E P,
  typing Gamma tag TUId -> typing Gamma E TEnumU ->
  typing Gamma P (TPi (TEnumT (TConsE tag E)) (TSort k)) ->
  typing Gamma (enum_tail_motive P) (TPi (TEnumT E) (TSort k)).
Proof.
  intros Gamma k tag E P Htag HE HP.
  pose proof (ty_enumt _ _ HE) as HA.
  apply regular_lambda; [exists 0; exact HA|].
  pose proof (weakening _ _ _ _ _ HP HA) as HP'. cbn [lift] in HP'.
  pose proof (weakening _ _ _ _ _ HE HA) as HE'.
  pose proof (weakening _ _ _ _ _ Htag HA) as Htag'.
  assert (Hv : typing (TEnumT E::Gamma) (TVar 0) (TEnumT (lift 1 0 E)))
    by (change (typing (TEnumT E::Gamma) (TVar 0) (lift 1 0 (TEnumT E)));
      apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
  exact (regular_application _ _ _ _ _ HP' (smart_succ _ _ _ _ Htag' HE' Hv)).
Qed.

Lemma epi_cons_beta : forall Gamma k tag E P,
  typing Gamma tag TUId -> typing Gamma E TEnumU ->
  typing Gamma P (TPi (TEnumT (TConsE tag E)) (TSort k)) ->
  typing Gamma (product (TApp P TEZero) (TEPi k E (enum_tail_motive P))) (TSort k).
Proof.
  intros Gamma k tag E P Htag HE HP.
  replace k with (Nat.max k k) at 2 by lia.
  apply product_formation.
  - exact (regular_application _ _ _ _ _ HP (smart_zero _ _ _ Htag HE)).
  - apply ty_epi; [exact HE|eapply enum_tail_motive_typing; eassumption].
Qed.

Theorem epi_beta : forall Gamma k E P u,
  typing Gamma E TEnumU -> typing Gamma P (TPi (TEnumT E) (TSort k)) ->
  root_step (TEPi k E P) = Some u -> typing Gamma u (TSort k).
Proof.
  intros Gamma k E P u HE HP Hr. destruct E; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
  - apply ty_unitT; eauto using typing_context.
  - destruct (conse_generation _ _ _ HE _ _ eq_refl) as [Htag HE'].
    eapply epi_cons_beta; eassumption.
Qed.

Lemma epi_pair_components : forall Gamma k tag E P p ps,
  typing Gamma tag TUId -> typing Gamma E TEnumU ->
  typing Gamma P (TPi (TEnumT (TConsE tag E)) (TSort k)) ->
  typing Gamma (TPair p ps) (TEPi k (TConsE tag E) P) ->
  typing Gamma p (TApp P TEZero) /\ typing Gamma ps (TEPi k E (enum_tail_motive P)).
Proof.
  intros Gamma k tag E P p ps Htag HE HP Hp.
  assert (Hprod : typing Gamma (TPair p ps) (product (TApp P TEZero) (TEPi k E (enum_tail_motive P)))).
  { eapply ty_conv; [exact Hp|eapply epi_cons_beta; eassumption|apply cv_step, st_root; reflexivity]. }
  pose proof (pair_second _ _ _ _ _ Hprod) as Hps. rewrite subst_lift_zero in Hps.
  split; eauto using pair_first.
Qed.

Theorem switch_beta : forall Gamma k E P p e u,
  typing Gamma E TEnumU -> typing Gamma P (TPi (TEnumT E) (TSort k)) ->
  typing Gamma p (TEPi k E P) -> typing Gamma e (TEnumT E) ->
  root_step (TSwitch k E P p e) = Some u -> typing Gamma u (TApp P e).
Proof.
  intros Gamma k E P p e u HE HP Hp He Hr.
  destruct E; cbn [root_step] in Hr; try discriminate.
  destruct p; try discriminate. destruct e; try discriminate; inversion Hr; subst.
  - destruct (conse_generation _ _ _ HE _ _ eq_refl) as [Htag HE'].
    exact (proj1 (epi_pair_components _ _ _ _ _ _ _ Htag HE' HP Hp)).
  - destruct (conse_generation _ _ _ HE _ _ eq_refl) as [Htag HE'].
    destruct (epi_pair_components _ _ _ _ _ _ _ Htag HE' HP Hp) as [Hhead Htail].
    eapply ty_conv.
    + eapply smart_switch; [exact HE'|eapply enum_tail_motive_typing; eassumption|exact Htail|].
      eapply succ_inversion; eassumption.
    + exact (regular_application _ _ _ _ _ HP He).
    + eapply cv_trans; [apply cv_step, st_root; reflexivity|].
      cbn [enum_tail_motive subst]. rewrite ?subst_lift_zero, ?lift_zero_id. apply cv_refl.
Qed.
