(* Eta contractions cannot expose a data constructor through a lambda
   in a well-typed elimination. This invariant supports postponement. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEtaTyping nameless.DBParallelPreservation.

Definition not_lambda t := match t with TLam _ => false | _ => true end.
Definition tests_payload D :=
  match D with TI1 | TIProd _ _ | TISig _ _ | TIChoice _ _ => true | _ => false end.
Definition local_eta_safe t :=
  match t with
  | TFst p | TSnd p => not_lambda p
  | TEPi _ E _ => not_lambda E
  | TSwitch _ E _ p e => not_lambda E && not_lambda e &&
      (match E with TConsE _ _ => not_lambda p | _ => true end)
  | TInterp _ D _ => not_lambda D
  | TIAll _ D _ x _ | THyps _ D _ _ _ x =>
      not_lambda D && (if tests_payload D then not_lambda x else true)
  | TInd _ _ _ _ _ x | TCloseCase _ _ _ _ _ _ _ x
  | TCloseInd _ _ _ _ _ _ x => not_lambda x
  | _ => true
  end.
Fixpoint eta_safe t : bool :=
  match t with
  | TVar n => local_eta_safe t && (true)
  | TSort k => local_eta_safe t && (true)
  | TPi A B => local_eta_safe t && (eta_safe A && (eta_safe B && (true)))
  | TLam b => local_eta_safe t && (eta_safe b && (true))
  | TApp f a => local_eta_safe t && (eta_safe f && (eta_safe a && (true)))
  | TSigma A B => local_eta_safe t && (eta_safe A && (eta_safe B && (true)))
  | TPair a b => local_eta_safe t && (eta_safe a && (eta_safe b && (true)))
  | TFst p => local_eta_safe t && (eta_safe p && (true))
  | TSnd p => local_eta_safe t && (eta_safe p && (true))
  | TUnitT => local_eta_safe t && (true)
  | TUnit => local_eta_safe t && (true)
  | TUId => local_eta_safe t && (true)
  | TTag s => local_eta_safe t && (true)
  | TEnumU => local_eta_safe t && (true)
  | TNilE => local_eta_safe t && (true)
  | TConsE tag E => local_eta_safe t && (eta_safe tag && (eta_safe E && (true)))
  | TEnumT E => local_eta_safe t && (eta_safe E && (true))
  | TEZero => local_eta_safe t && (true)
  | TESucc n => local_eta_safe t && (eta_safe n && (true))
  | TEPi k E P => local_eta_safe t && (eta_safe E && (eta_safe P && (true)))
  | TSwitch k E P p e => local_eta_safe t && (eta_safe E && (eta_safe P && (eta_safe p && (eta_safe e && (true)))))
  | TIDesc IT => local_eta_safe t && (eta_safe IT && (true))
  | TIVar i => local_eta_safe t && (eta_safe i && (true))
  | TI1 => local_eta_safe t && (true)
  | TIBot => local_eta_safe t && (true)
  | TIProd A B => local_eta_safe t && (eta_safe A && (eta_safe B && (true)))
  | TIPi A D => local_eta_safe t && (eta_safe A && (eta_safe D && (true)))
  | TISig A D => local_eta_safe t && (eta_safe A && (eta_safe D && (true)))
  | TIChoice E D => local_eta_safe t && (eta_safe E && (eta_safe D && (true)))
  | TInterp IT D X => local_eta_safe t && (eta_safe IT && (eta_safe D && (eta_safe X && (true))))
  | TMuI IT D => local_eta_safe t && (eta_safe IT && (eta_safe D && (true)))
  | TIn x => local_eta_safe t && (eta_safe x && (true))
  | TInd IT D P s i x => local_eta_safe t && (eta_safe IT && (eta_safe D && (eta_safe P && (eta_safe s && (eta_safe i && (eta_safe x && (true)))))))
  | TIAll IT D X x P => local_eta_safe t && (eta_safe IT && (eta_safe D && (eta_safe X && (eta_safe x && (eta_safe P && (true))))))
  | THyps IT D X P h x => local_eta_safe t && (eta_safe IT && (eta_safe D && (eta_safe X && (eta_safe P && (eta_safe h && (eta_safe x && (true)))))))
  | TClose IT F G => local_eta_safe t && (eta_safe IT && (eta_safe F && (eta_safe G && (true))))
  | TCloseCase k IT F G i Q b x => local_eta_safe t && (eta_safe IT && (eta_safe F && (eta_safe G && (eta_safe i && (eta_safe Q && (eta_safe b && (eta_safe x && (true))))))))
  | TCloseInd IT G P s F i x => local_eta_safe t && (eta_safe IT && (eta_safe G && (eta_safe P && (eta_safe s && (eta_safe F && (eta_safe i && (eta_safe x && (true))))))))
  end.

Lemma not_lambda_lift : forall t d c, not_lambda (lift d c t) = not_lambda t.
Proof. destruct t; intros; cbn [lift not_lambda]; try reflexivity.
  destruct (n <? c); reflexivity. Qed.
Lemma tests_payload_lift : forall t d c, tests_payload (lift d c t) = tests_payload t.
Proof. destruct t; intros; cbn [lift tests_payload]; try reflexivity.
  destruct (n <? c); reflexivity. Qed.
Lemma local_eta_safe_lift : forall t d c,
  local_eta_safe (lift d c t) = local_eta_safe t.
Proof.
  destruct t; intros; cbn [lift local_eta_safe];
    try rewrite !not_lambda_lift; try rewrite tests_payload_lift; try reflexivity.
  - destruct (n <? c); reflexivity.
  - destruct t1; cbn [lift]; try reflexivity; destruct (n <? c); reflexivity.
Qed.
Lemma eta_safe_lift : forall t d c, eta_safe (lift d c t) = eta_safe t.
Proof.
  induction t; intros; cbn [lift eta_safe];
    try rewrite local_eta_safe_lift;
    try solve [destruct (n <? c); reflexivity];
    repeat match goal with H : forall d c, eta_safe (lift d c ?t) = eta_safe ?t
      |- context [eta_safe (lift ?d ?c ?t)] => rewrite (H d c) end;
    try reflexivity.
  all: cbn [local_eta_safe]; rewrite ?not_lambda_lift, ?tests_payload_lift; try reflexivity.
  destruct t1; cbn [lift]; try reflexivity; destruct (n <? c); reflexivity.
Qed.

Lemma typed_not_lambda : forall Gamma t T U h,
  typing Gamma t T -> conv T U -> term_head U = Some h -> h <> h_pi ->
  not_lambda t = true.
Proof.
  intros Gamma t T U h Ht HC HH Hne.
  destruct t; try reflexivity.
  destruct (lambda_generation _ _ _ Ht _ eq_refl) as [A [B [k [HP [Hb Hconv]]]]].
  exfalso; apply Hne; symmetry.
  apply (conversion_head (TPi A B) U); auto.
  eapply cv_trans; eassumption.
Qed.

Ltac exclude_lambda :=
  eapply typed_not_lambda; [eassumption|apply cv_refl|reflexivity|discriminate].

Lemma interpreted_payload_not_lambda : forall Gamma IT D X x,
  typing Gamma x (TInterp IT D X) -> tests_payload D = true -> not_lambda x = true.
Proof.
  intros Gamma IT D X x Hx HD; destruct D; cbn [tests_payload] in HD; try discriminate.
  all: eapply typed_not_lambda; [exact Hx|apply cv_step, st_root;reflexivity|reflexivity|discriminate].
Qed.
Lemma epi_pair_not_lambda : forall Gamma k tag E P p,
  typing Gamma p (TEPi k (TConsE tag E) P) -> not_lambda p = true.
Proof.
  intros; eapply typed_not_lambda;
    [eassumption|apply cv_step, st_root;reflexivity|reflexivity|discriminate].
Qed.

Theorem typing_eta_safe : forall Gamma t T,
  typing Gamma t T -> eta_safe t = true.
Proof.
  intros Gamma t T H; induction H; cbn [eta_safe local_eta_safe];
    repeat rewrite Bool.andb_true_iff; try tauto.
  all: repeat split; try assumption; try reflexivity; try solve [exclude_lambda].
  - destruct E; try reflexivity; eapply epi_pair_not_lambda; eassumption.
  - destruct (tests_payload D) eqn:HD; [eapply interpreted_payload_not_lambda; eassumption|reflexivity].
  - destruct (tests_payload D) eqn:HD; [eapply interpreted_payload_not_lambda; eassumption|reflexivity].
Qed.

Print Assumptions typing_eta_safe.

Lemma epstep_not_lambda : forall t u, epstep t u ->
  not_lambda t = true -> not_lambda u = true.
Proof. intros t u H; destruct H; cbn [not_lambda]; intros; congruence. Qed.

Lemma epstep_handler_test : forall E E' p p',
  epstep E E' -> epstep p p' -> not_lambda E = true ->
  (match E with TConsE _ _ => not_lambda p | _ => true end) = true ->
  (match E' with TConsE _ _ => not_lambda p' | _ => true end) = true.
Proof.
  intros E E' p p' HE Hp; destruct HE; cbn [not_lambda]; intros; try reflexivity; try discriminate.
  eapply epstep_not_lambda; eassumption.
Qed.
Lemma epstep_payload_test : forall D D' x x',
  epstep D D' -> epstep x x' -> not_lambda D = true ->
  (if tests_payload D then not_lambda x else true) = true ->
  (if tests_payload D' then not_lambda x' else true) = true.
Proof.
  intros D D' x x' HD Hx; destruct HD;
    cbn [not_lambda tests_payload]; intros; try reflexivity; try discriminate.
  all: eapply epstep_not_lambda; eassumption.
Qed.

Lemma local_eta_safe_compatible : forall t u, compatible epstep t u ->
  local_eta_safe t = true -> local_eta_safe u = true.
Proof.
  intros t u H; destruct H; cbn [local_eta_safe]; intros HS;
    repeat rewrite Bool.andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; try reflexivity;
    eauto using epstep_not_lambda, epstep_handler_test, epstep_payload_test.
Qed.

Theorem epstep_eta_safe : forall t u, epstep t u ->
  eta_safe t = true -> eta_safe u = true.
Proof.
  intros t u H; induction H; intro HS; cbn [eta_safe] in *;
    repeat rewrite Bool.andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try rewrite eta_safe_lift in *;
    repeat split; try reflexivity; eauto.
  all: match goal with H : local_eta_safe ?t = true |- local_eta_safe ?u = true =>
    apply (local_eta_safe_compatible t u); [constructor; eassumption|exact H]
  end.
Qed.
