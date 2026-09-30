Require Import Progress _tmp_epstep _tmp_epstep_subst.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma rtc_map_rel : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> Y),
    (forall x y, R x y -> S (F x) (F y)) ->
    forall x y, rtc R x y -> rtc S (F x) (F y).
Proof.
  intros X Y R S F HF x y H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact H | exact IHrtc].
Qed.

Lemma rtc_map_rel2 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> Y),
    (forall x y z, R x y -> S (F x z) (F y z)) ->
    (forall z x y, R x y -> S (F z x) (F z y)) ->
    forall a a' b b', rtc R a a' -> rtc R b b' ->
      rtc S (F a b) (F a' b').
Proof.
  intros X Y R S F H1 H2 a a' b b' Ha Hb. eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b));
      [intros; apply H1; assumption | exact Ha].
  - eapply (rtc_map_rel X Y R S (fun x => F a' x));
      [intros; apply H2; assumption | exact Hb].
Qed.

Lemma rtc_map_rel3 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> Y),
    (forall x y b c, R x y -> S (F x b c) (F y b c)) ->
    (forall a x y c, R x y -> S (F a x c) (F a y c)) ->
    (forall a b x y, R x y -> S (F a b x) (F a b y)) ->
    forall a a' b b' c c',
      rtc R a a' -> rtc R b b' -> rtc R c c' ->
      rtc S (F a b c) (F a' b' c').
Proof.
  intros X Y R S F H1 H2 H3 a a' b b' c c' Ha Hb Hc.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c));
        [intros; apply H2; assumption | exact Hb].
    + eapply (rtc_map_rel X Y R S (fun x => F a' b' x));
        [intros; apply H3; assumption | exact Hc].
Qed.

Lemma rtc_map_rel4 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> X -> Y),
    (forall x y b c d, R x y -> S (F x b c d) (F y b c d)) ->
    (forall a x y c d, R x y -> S (F a x c d) (F a y c d)) ->
    (forall a b x y d, R x y -> S (F a b x d) (F a b y d)) ->
    (forall a b c x y, R x y -> S (F a b c x) (F a b c y)) ->
    forall a a' b b' c c' d d',
      rtc R a a' -> rtc R b b' -> rtc R c c' -> rtc R d d' ->
      rtc S (F a b c d) (F a' b' c' d').
Proof.
  intros X Y R S F H1 H2 H3 H4 a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c d));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c d));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' x d));
          [intros; apply H3; assumption | exact Hc].
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' c' x));
          [intros; apply H4; assumption | exact Hd].
Qed.

Lemma rtc_map_rel5 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> X -> X -> Y),
    (forall x y b c d e, R x y -> S (F x b c d e) (F y b c d e)) ->
    (forall a x y c d e, R x y -> S (F a x c d e) (F a y c d e)) ->
    (forall a b x y d e, R x y -> S (F a b x d e) (F a b y d e)) ->
    (forall a b c x y e, R x y -> S (F a b c x e) (F a b c y e)) ->
    (forall a b c d x y, R x y -> S (F a b c d x) (F a b c d y)) ->
    forall a a' b b' c c' d d' e e',
      rtc R a a' -> rtc R b b' -> rtc R c c' -> rtc R d d' ->
      rtc R e e' -> rtc S (F a b c d e) (F a' b' c' d' e').
Proof.
  intros X Y R S F H1 H2 H3 H4 H5
    a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c d e));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c d e));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' x d e));
          [intros; apply H3; assumption | exact Hc].
      * eapply rtc_trans.
        -- eapply (rtc_map_rel X Y R S (fun x => F a' b' c' x e));
             [intros; apply H4; assumption | exact Hd].
        -- eapply (rtc_map_rel X Y R S (fun x => F a' b' c' d' x));
             [intros; apply H5; assumption | exact He].
Qed.

Lemma rtc_epstep_lift : forall t u,
    rtc epstep t u -> forall d k, rtc epstep (lift d k t) (lift d k u).
Proof.
  intros t u H d k. eapply rtc_map_rel; [|exact H].
  intros x y Hxy. eapply epstep_lift. exact Hxy.
Qed.

Lemma rtc_epstep_congr1 : forall (F : term -> term),
    (forall x y, epstep x y -> epstep (F x) (F y)) ->
    forall x y, rtc epstep x y -> rtc epstep (F x) (F y).
Proof. intros F HF x y H; eapply rtc_map_rel; eauto. Qed.

Lemma rtc_epstep_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', epstep a a' -> epstep b b' ->
      epstep (F a b) (F a' b')) ->
    forall a a' b b', rtc epstep a a' -> rtc epstep b b' ->
      rtc epstep (F a b) (F a' b').
Proof.
  intros F HF a a' b b' Ha Hb.
  eapply rtc_map_rel2 with (F := F).
  - intros x y z Hxy. apply HF; [exact Hxy | apply epstep_refl].
  - intros z x y Hxy. apply HF; [apply epstep_refl | exact Hxy].
  - exact Ha.
  - exact Hb.
Qed.

Lemma rtc_epstep_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      epstep a a' -> epstep b b' -> epstep c c' ->
      epstep (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep (F a b c) (F a' b' c').
Proof.
  intros F HF a a' b b' c c' Ha Hb Hc.
  eapply rtc_map_rel3 with (F := F).
  - intros x y z w Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
Qed.

Lemma rtc_epstep_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep d d' -> rtc epstep (F a b c d) (F a' b' c' d').
Proof.
  intros F HF a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_map_rel4 with (F := F).
  - intros x y z w q Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w q Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y q Hxy. apply HF; eauto using epstep_refl.
  - intros z w q x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
Qed.

Lemma rtc_epstep_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep e e' -> epstep (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep d d' -> rtc epstep e e' ->
      rtc epstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F HF a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_map_rel5 with (F := F).
  - intros x y z w q r Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w q r Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y q r Hxy. apply HF; eauto using epstep_refl.
  - intros z w q x y r Hxy. apply HF; eauto using epstep_refl.
  - intros z w q r x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
  - exact He.
Qed.

Lemma rtc_epstep_subst : forall t t' u u' k,
    rtc epstep t t' -> rtc epstep u u' ->
    rtc epstep (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' k Ht Hu.
  eapply rtc_map_rel2 with (F := fun body arg => subst arg k body).
  - intros x y arg Hxy. eapply epstep_subst; [exact Hxy | apply epstep_refl].
  - intros body x y Hxy. eapply epstep_subst; [apply epstep_refl | exact Hxy].
  - exact Ht.
  - exact Hu.
Qed.

Lemma rtc_epbranches_cons : forall c c' b b' bs bs',
    rtc epstep c c' -> rtc epstep b b' -> rtc epbranches bs bs' ->
    rtc epbranches ((c,b)::bs) ((c',b')::bs').
Proof.
  intros c c' b b' bs bs' Hc Hb Hbs. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => (x,b)::bs); [|exact Hc].
    intros x y Hxy. constructor; [exact Hxy | apply epstep_refl | apply epbranches_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => (c',x)::bs); [|exact Hb].
      intros x y Hxy. constructor; [apply epstep_refl | exact Hxy | apply epbranches_refl].
    + eapply rtc_map_rel with (F := fun xs => (c',b')::xs); [|exact Hbs].
      intros xs ys Hxy. constructor; [apply epstep_refl | apply epstep_refl | exact Hxy].
Qed.

Lemma rtc_epstep_case : forall M M' Q Q' bs bs',
    rtc epstep M M' -> rtc epstep Q Q' -> rtc epbranches bs bs' ->
    rtc epstep (TCase M Q bs) (TCase M' Q' bs').
Proof.
  intros M M' Q Q' bs bs' HM HQ Hbs. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => TCase x Q bs); [|exact HM].
    intros x y Hxy. constructor; [exact Hxy | apply epstep_refl | apply epbranches_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => TCase M' x bs); [|exact HQ].
      intros x y Hxy. constructor; [apply epstep_refl | exact Hxy | apply epbranches_refl].
    + eapply rtc_map_rel with (F := fun xs => TCase M' Q' xs); [|exact Hbs].
      intros xs ys Hxy. constructor; [apply epstep_refl | apply epstep_refl | exact Hxy].
Qed.
