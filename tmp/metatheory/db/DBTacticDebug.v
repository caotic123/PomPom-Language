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

Goal forall a b, rtc epstep a b -> rtc epstep (TLam a) (TLam b).
Proof.
  intros a b H.
  match goal with |- rtc epstep (?F ?a) (?F ?b) => idtac F a b end.
  eapply eta_star_congr1 with (F:=TLam).
  - intros. constructor. eassumption.
  - eta_star_congr.
Qed.
Goal forall a b, rtc epstep a b -> rtc epstep (TLam a) (TLam b).
Proof.
  intros a b H.
  match goal with |- rtc epstep (?F ?a0) (?F ?b0) =>
    eapply eta_star_congr1 with (F:=F); [intros; constructor; eassumption|eta_star_congr]
  end.
Qed.
