Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* A pstep-specific copy of the generic closure maps.  The suffix keeps
   this scratch module independent of the eta closure library. *)
Lemma rtc_map_rel_pstep : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> Y),
    (forall x y, R x y -> S (F x) (F y)) ->
    forall x y, rtc R x y -> rtc S (F x) (F y).
Proof.
  intros X Y R S F HF x y H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact H | exact IHrtc].
Qed.

Lemma rtc_map_rel2_pstep : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> Y),
    (forall x y z, R x y -> S (F x z) (F y z)) ->
    (forall z x y, R x y -> S (F z x) (F z y)) ->
    forall a a' b b', rtc R a a' -> rtc R b b' ->
      rtc S (F a b) (F a' b').
Proof.
  intros X Y R S F H1 H2 a a' b b' Ha Hb. eapply rtc_trans.
  - eapply (rtc_map_rel_pstep X Y R S (fun x => F x b));
      [intros; apply H1; assumption | exact Ha].
  - eapply (rtc_map_rel_pstep X Y R S (fun x => F a' x));
      [intros; apply H2; assumption | exact Hb].
Qed.

Lemma rtc_map_rel3_pstep : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
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
  - eapply (rtc_map_rel_pstep X Y R S (fun x => F x b c));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel_pstep X Y R S (fun x => F a' x c));
        [intros; apply H2; assumption | exact Hb].
    + eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' x));
        [intros; apply H3; assumption | exact Hc].
Qed.

Lemma rtc_map_rel4_pstep : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
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
  - eapply (rtc_map_rel_pstep X Y R S (fun x => F x b c d));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel_pstep X Y R S (fun x => F a' x c d));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' x d));
          [intros; apply H3; assumption | exact Hc].
      * eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' c' x));
          [intros; apply H4; assumption | exact Hd].
Qed.

Lemma rtc_map_rel5_pstep : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
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
  - eapply (rtc_map_rel_pstep X Y R S (fun x => F x b c d e));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel_pstep X Y R S (fun x => F a' x c d e));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' x d e));
          [intros; apply H3; assumption | exact Hc].
      * eapply rtc_trans.
        -- eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' c' x e));
             [intros; apply H4; assumption | exact Hd].
        -- eapply (rtc_map_rel_pstep X Y R S (fun x => F a' b' c' d' x));
             [intros; apply H5; assumption | exact He].
Qed.

Lemma rtc_pstep_lift : forall t u,
    rtc pstep t u -> forall d k, rtc pstep (lift d k t) (lift d k u).
Proof.
  intros t u H d k. eapply rtc_map_rel_pstep; [|exact H].
  intros x y Hxy. eapply pstep_lift. exact Hxy.
Qed.

Lemma rtc_pstep_congr1 : forall (F : term -> term),
    (forall x y, pstep x y -> pstep (F x) (F y)) ->
    forall x y, rtc pstep x y -> rtc pstep (F x) (F y).
Proof. intros F HF x y H; eapply rtc_map_rel_pstep; eauto. Qed.

Lemma rtc_pstep_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', pstep a a' -> pstep b b' ->
      pstep (F a b) (F a' b')) ->
    forall a a' b b', rtc pstep a a' -> rtc pstep b b' ->
      rtc pstep (F a b) (F a' b').
Proof.
  intros F HF a a' b b' Ha Hb.
  eapply rtc_map_rel2_pstep with (F := F).
  - intros x y z Hxy. apply HF; [exact Hxy | apply pstep_refl].
  - intros z x y Hxy. apply HF; [apply pstep_refl | exact Hxy].
  - exact Ha.
  - exact Hb.
Qed.

Lemma rtc_pstep_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      pstep a a' -> pstep b b' -> pstep c c' ->
      pstep (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      rtc pstep a a' -> rtc pstep b b' -> rtc pstep c c' ->
      rtc pstep (F a b c) (F a' b' c').
Proof.
  intros F HF a a' b b' c c' Ha Hb Hc.
  eapply rtc_map_rel3_pstep with (F := F).
  - intros x y z w Hxy. apply HF; eauto using pstep_refl.
  - intros z x y w Hxy. apply HF; eauto using pstep_refl.
  - intros z w x y Hxy. apply HF; eauto using pstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
Qed.

Lemma rtc_pstep_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      rtc pstep a a' -> rtc pstep b b' -> rtc pstep c c' ->
      rtc pstep d d' -> rtc pstep (F a b c d) (F a' b' c' d').
Proof.
  intros F HF a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_map_rel4_pstep with (F := F).
  - intros x y z w q Hxy. apply HF; eauto using pstep_refl.
  - intros z x y w q Hxy. apply HF; eauto using pstep_refl.
  - intros z w x y q Hxy. apply HF; eauto using pstep_refl.
  - intros z w q x y Hxy. apply HF; eauto using pstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
Qed.

Lemma rtc_pstep_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep e e' -> pstep (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      rtc pstep a a' -> rtc pstep b b' -> rtc pstep c c' ->
      rtc pstep d d' -> rtc pstep e e' ->
      rtc pstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F HF a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_map_rel5_pstep with (F := F).
  - intros x y z w q r Hxy. apply HF; eauto using pstep_refl.
  - intros z x y w q r Hxy. apply HF; eauto using pstep_refl.
  - intros z w x y q r Hxy. apply HF; eauto using pstep_refl.
  - intros z w q x y r Hxy. apply HF; eauto using pstep_refl.
  - intros z w q r x y Hxy. apply HF; eauto using pstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
  - exact He.
Qed.

Lemma rtc_pstep_subst : forall t t' u u' k,
    rtc pstep t t' -> rtc pstep u u' ->
    rtc pstep (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' k Ht Hu.
  eapply rtc_map_rel2_pstep with (F := fun body arg => subst arg k body).
  - intros x y arg Hxy. eapply pstep_subst; [exact Hxy | apply pstep_refl].
  - intros body x y Hxy. eapply pstep_subst; [apply pstep_refl | exact Hxy].
  - exact Ht.
  - exact Hu.
Qed.

Lemma rtc_pbranches_cons : forall c c' b b' bs bs',
    rtc pstep c c' -> rtc pstep b b' -> rtc pbranches bs bs' ->
    rtc pbranches ((c,b)::bs) ((c',b')::bs').
Proof.
  intros c c' b b' bs bs' Hc Hb Hbs. eapply rtc_trans.
  - eapply rtc_map_rel_pstep with (F := fun x => (x,b)::bs); [|exact Hc].
    intros x y Hxy. constructor; [exact Hxy | apply pstep_refl | apply pbranches_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel_pstep with (F := fun x => (c',x)::bs); [|exact Hb].
      intros x y Hxy. constructor; [apply pstep_refl | exact Hxy | apply pbranches_refl].
    + eapply rtc_map_rel_pstep with (F := fun xs => (c',b')::xs); [|exact Hbs].
      intros xs ys Hxy. constructor; [apply pstep_refl | apply pstep_refl | exact Hxy].
Qed.
