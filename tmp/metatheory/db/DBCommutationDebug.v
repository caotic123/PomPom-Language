From Stdlib Require Import List Arith Lia PeanoNat String.
Require Export ProofDB.DBEta.
Import ListNotations.

Lemma pstep_lift_inverse : forall t T,
  pstep t T -> forall original cutoff, t = lift 1 cutoff original ->
  exists u, T = lift 1 cutoff u /\ pstep original u.
Proof.
  intros t T Hstep; induction Hstep; intros original cutoff Heq.
  all: repeat match goal with
  | E : ?source = lift 1 ?q ?x |- _ =>
      destruct x; cbn [lift] in E;
      repeat match type of E with
      | context [Nat.ltb ?a ?b] => destruct (Nat.ltb a b) eqn:?
      end; try discriminate; inversion E; subst; clear E
  end.
  all: repeat match goal with
    | IH : forall f k, lift 1 ?q ?tm = lift 1 k f ->
        exists u, ?out = lift 1 k u /\ pstep f u |- _ =>
      let new := fresh "new" in let E := fresh "E" in let Hnew := fresh "Hnew" in
      destruct (IH tm q eq_refl) as [new [E Hnew]]; clear IH; subst out
    end.
  all: try solve [eexists; split; [|constructor; eassumption]; cbn [lift];
    repeat match goal with H : Nat.ltb _ _ = _ |- _ => rewrite H end; reflexivity].
  all: eexists; split; cycle 1;
    [apply_root ltac:(eassumption)|cbn [lift]; lift_norm;
      repeat rewrite lift_subst_zero_comm; reflexivity].
Qed.

Lemma eta_star_congr1 : forall (F : term -> term),
  (forall a0 b0, epstep a0 b0 -> epstep (F a0) (F b0)) ->
  forall a0 b0, rtc epstep a0 b0 -> rtc epstep (F a0) (F b0).
Proof.
  intros F HF a0 b0 H0.
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F z)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr2 : forall (F : term -> term -> term),
  (forall a0 b0 a1 b1, epstep a0 b0 -> epstep a1 b1 -> epstep (F a0 a1) (F b0 b1)) ->
  forall a0 b0 a1 b1, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep (F a0 a1) (F b0 b1).
Proof.
  intros F HF a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr3 : forall (F : term -> term -> term -> term),
  (forall a0 b0 a1 b1 a2 b2, epstep a0 b0 -> epstep a1 b1 -> epstep a2 b2 -> epstep (F a0 a1 a2) (F b0 b1 b2)) ->
  forall a0 b0 a1 b1 a2 b2, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep a2 b2 -> rtc epstep (F a0 a1 a2) (F b0 b1 b2).
Proof.
  intros F HF a0 b0 a1 b1 a2 b2 H0 H1 H2.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1 a2)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z a2)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 z)); [|exact H2].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr4 : forall (F : term -> term -> term -> term -> term),
  (forall a0 b0 a1 b1 a2 b2 a3 b3, epstep a0 b0 -> epstep a1 b1 -> epstep a2 b2 -> epstep a3 b3 -> epstep (F a0 a1 a2 a3) (F b0 b1 b2 b3)) ->
  forall a0 b0 a1 b1 a2 b2 a3 b3, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep a2 b2 -> rtc epstep a3 b3 -> rtc epstep (F a0 a1 a2 a3) (F b0 b1 b2 b3).
Proof.
  intros F HF a0 b0 a1 b1 a2 b2 a3 b3 H0 H1 H2 H3.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1 a2 a3)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z a2 a3)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 z a3)); [|exact H2].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 z)); [|exact H3].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr5 : forall (F : term -> term -> term -> term -> term -> term),
  (forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4, epstep a0 b0 -> epstep a1 b1 -> epstep a2 b2 -> epstep a3 b3 -> epstep a4 b4 -> epstep (F a0 a1 a2 a3 a4) (F b0 b1 b2 b3 b4)) ->
  forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep a2 b2 -> rtc epstep a3 b3 -> rtc epstep a4 b4 -> rtc epstep (F a0 a1 a2 a3 a4) (F b0 b1 b2 b3 b4).
Proof.
  intros F HF a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 H0 H1 H2 H3 H4.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1 a2 a3 a4)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z a2 a3 a4)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 z a3 a4)); [|exact H2].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 z a4)); [|exact H3].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 z)); [|exact H4].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr6 : forall (F : term -> term -> term -> term -> term -> term -> term),
  (forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5, epstep a0 b0 -> epstep a1 b1 -> epstep a2 b2 -> epstep a3 b3 -> epstep a4 b4 -> epstep a5 b5 -> epstep (F a0 a1 a2 a3 a4 a5) (F b0 b1 b2 b3 b4 b5)) ->
  forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep a2 b2 -> rtc epstep a3 b3 -> rtc epstep a4 b4 -> rtc epstep a5 b5 -> rtc epstep (F a0 a1 a2 a3 a4 a5) (F b0 b1 b2 b3 b4 b5).
Proof.
  intros F HF a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 H0 H1 H2 H3 H4 H5.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1 a2 a3 a4 a5)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z a2 a3 a4 a5)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 z a3 a4 a5)); [|exact H2].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 z a4 a5)); [|exact H3].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 z a5)); [|exact H4].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 b4 z)); [|exact H5].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_congr7 : forall (F : term -> term -> term -> term -> term -> term -> term -> term),
  (forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6, epstep a0 b0 -> epstep a1 b1 -> epstep a2 b2 -> epstep a3 b3 -> epstep a4 b4 -> epstep a5 b5 -> epstep a6 b6 -> epstep (F a0 a1 a2 a3 a4 a5 a6) (F b0 b1 b2 b3 b4 b5 b6)) ->
  forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6, rtc epstep a0 b0 -> rtc epstep a1 b1 -> rtc epstep a2 b2 -> rtc epstep a3 b3 -> rtc epstep a4 b4 -> rtc epstep a5 b5 -> rtc epstep a6 b6 -> rtc epstep (F a0 a1 a2 a3 a4 a5 a6) (F b0 b1 b2 b3 b4 b5 b6).
Proof.
  intros F HF a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 H0 H1 H2 H3 H4 H5 H6.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F z a1 a2 a3 a4 a5 a6)); [|exact H0].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 z a2 a3 a4 a5 a6)); [|exact H1].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 z a3 a4 a5 a6)); [|exact H2].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 z a4 a5 a6)); [|exact H3].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 z a5 a6)); [|exact H4].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 b4 z a6)); [|exact H5].
    intros z w Hzw. apply HF; auto using epstep_refl. }
  eapply (rtc_map_rel _ _ epstep epstep (fun z => F b0 b1 b2 b3 b4 b5 z)); [|exact H6].
    intros z w Hzw. apply HF; auto using epstep_refl.
Qed.

Lemma eta_star_lift : forall t u, rtc epstep t u -> forall d c,
  rtc epstep (lift d c t) (lift d c u).
Proof. intros t u H d c; eapply rtc_map_rel; [|exact H]; intros; now apply epstep_lift. Qed.
Lemma eta_star_subst : forall t t' u u' c,
  rtc epstep t t' -> rtc epstep u u' ->
  rtc epstep (subst u c t) (subst u' c t').
Proof.
  intros; eapply eta_star_congr2 with (F := fun b a => subst a c b);
    [intros; now apply epstep_subst|assumption|assumption].
Qed.
Ltac eta_congr := solve [eassumption | apply epstep_refl |
  match goal with
  | |- epstep (lift ?d ?c ?t) (lift ?d ?c ?u) => apply epstep_lift; eta_congr
  | |- epstep (subst ?a ?c ?t) (subst ?b ?c ?u) => apply epstep_subst; eta_congr
  end | constructor; eta_congr].
Ltac eta_star_congr := solve [eassumption | apply rtc_refl |
  match goal with
  | |- rtc epstep (lift ?d ?c ?t) (lift ?d ?c ?u) => apply eta_star_lift; eta_star_congr
  | |- rtc epstep (subst ?a ?c ?t) (subst ?b ?c ?u) => apply eta_star_subst; eta_star_congr
  | |- rtc epstep (?F ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6) (?F ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6) =>
    eapply eta_star_congr7 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0 ?a1 ?a2 ?a3 ?a4 ?a5) (?F ?b0 ?b1 ?b2 ?b3 ?b4 ?b5) =>
    eapply eta_star_congr6 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0 ?a1 ?a2 ?a3 ?a4) (?F ?b0 ?b1 ?b2 ?b3 ?b4) =>
    eapply eta_star_congr5 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0 ?a1 ?a2 ?a3) (?F ?b0 ?b1 ?b2 ?b3) =>
    eapply eta_star_congr4 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0 ?a1 ?a2) (?F ?b0 ?b1 ?b2) =>
    eapply eta_star_congr3 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0 ?a1) (?F ?b0 ?b1) =>
    eapply eta_star_congr2 with (F:=F); [intros; constructor; eassumption|eta_star_congr|eta_star_congr]
  | |- rtc epstep (?F ?a0) (?F ?b0) =>
    eapply eta_star_congr1 with (F:=F); [intros; constructor; eassumption|eta_star_congr]
  end | apply rtc_one; eta_congr].

Definition eta_app (f : term) := TApp (lift 1 0 f) (TVar 0).
Lemma pstep_eta_app_cases : forall f q, pstep (eta_app f) q ->
  (exists g, q = eta_app g /\ pstep f g) \/
  (exists b b', f = TLam b /\ q = b' /\ pstep b b').
Proof.
  intros f q H; unfold eta_app in H. inversion H; subst.
  - match goal with H : pstep (TVar 0) _ |- _ => inversion H; subst end.
    match goal with H : pstep (lift 1 0 f) ?f' |- _ =>
      destruct (pstep_lift_inverse _ _ H f 0 eq_refl) as [g [Hg Hfg]];
      subst f'; left; exists g; now split end.
  - destruct f; cbn [lift] in H0; try discriminate.
    inversion H0; subst; clear H0.
    match goal with H : pstep (TVar 0) _ |- _ => inversion H; subst end.
    match goal with H : pstep (lift 1 1 ?f) ?b' |- _ =>
      destruct (pstep_lift_inverse _ _ H f 1 eq_refl) as [bd [Hbd Hfbd]];
      subst b'; rewrite subst_eta_beta_cancel;
      right; exists f, bd; repeat split; assumption end.
Qed.
Lemma eta_lambda_critical : forall f u b', epstep f u ->
  (forall z, epstep (eta_app f) z -> exists q, rtc epstep b' q /\ pstep z q) ->
  exists v, rtc epstep (TLam b') v /\ pstep u v.
Proof.
  intros f u b' Hfu IH.
  assert (Hbody : epstep (eta_app f) (eta_app u)) by (unfold eta_app; eta_congr).
  destruct (IH _ Hbody) as [q [Hbq Huq]].
  destruct (pstep_eta_app_cases u q Huq) as
    [[g [Hq Hug]]|[body [body' [Hu [Hq Hbodycore]]]]].
  - subst q. exists g. split; [|assumption].
    eapply rtc_trans with (y:=TLam (eta_app g)).
    + apply eta_star_congr1 with (F:=TLam); [intros; now constructor|exact Hbq].
    + apply rtc_one. unfold eta_app. apply eps_eta, epstep_refl.
  - subst u q. exists (TLam body'). split.
    + apply eta_star_congr1 with (F:=TLam); [intros; now constructor|exact Hbq].
    + now constructor.
Qed.

Ltac take_commute := match goal with
  | IH : forall z, epstep ?s z -> exists w, rtc epstep ?t w /\ pstep z w,
    H : epstep ?s ?z |- _ =>
    let w := fresh "w" in let He := fresh "Heta" in let Hp := fresh "Hcore" in
    destruct (IH z H) as [w [He Hp]]; clear IH
  end.
Ltac eta_invert_known :=
  match goal with
  | H : epstep (TLam _) _ |- _ => inversion H; subst; clear H
  | H : epstep (TPair _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep TNilE _ |- _ => inversion H; subst; clear H
  | H : epstep (TConsE _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep TEZero _ |- _ => inversion H; subst; clear H
  | H : epstep (TESucc _) _ |- _ => inversion H; subst; clear H
  | H : epstep TUnit _ |- _ => inversion H; subst; clear H
  | H : epstep (TIVar _) _ |- _ => inversion H; subst; clear H
  | H : epstep TI1 _ |- _ => inversion H; subst; clear H
  | H : epstep TIBot _ |- _ => inversion H; subst; clear H
  | H : epstep (TIProd _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep (TIPi _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep (TISig _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep (TIChoice _ _) _ |- _ => inversion H; subst; clear H
  | H : epstep (TIn _) _ |- _ => inversion H; subst; clear H
  end.

Lemma pstep_epstep_commute : forall s t u, pstep s t -> epstep s u ->
  exists v, rtc epstep t v /\ pstep u v.
Proof.
  intros s t u H; revert u. induction H; intros u Hother;
    inversion Hother; subst; clear Hother.
  all: repeat eta_invert_known.
  all: repeat take_commute.
  all: try solve [eexists; split; cycle 1;
    [constructor; eauto using pstep_lift, pstep_subst, pstep_refl|eta_star_congr]].
  all: try solve [eexists; split; cycle 1;
    [apply_root ltac:(eassumption)|eta_star_congr]].
  all: try solve [eapply eta_lambda_critical; eassumption].
  all: try solve [match goal with
    | IH : forall z, epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      Hfu : epstep ?f ?fu,
      Hea : rtc epstep ?a ?aw,
      Hca : pstep ?a0 ?aw
      |- exists v, rtc epstep (subst ?a 0 ?b) v /\ pstep (TApp ?fu ?a0) v =>
      assert (Hbody : epstep (TApp (lift 1 0 f) (TVar 0))
        (TApp (lift 1 0 fu) (TVar 0))) by eta_congr;
      destruct (IH _ Hbody) as [q [Hbq Hfq]];
      exists (subst aw 0 q); split;
      [apply eta_star_subst; eassumption|
        pose proof (pstep_subst _ _ Hfq a0 aw 0 Hca) as Hsub;
        rewrite subst_eta_app in Hsub; exact Hsub]
    end].
Show.
Abort.
