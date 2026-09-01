Require Import Progress _tmp_epstep _work_epstep_rtc _luna_pstep_rtc
  _work_mixed_closure _work_cjoin.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(** A context which preserves both parallel relations preserves a whole
    combined phase. *)
Lemma cstep_congr1 : forall (F : term -> term),
    (forall x y, pstep x y -> pstep (F x) (F y)) ->
    (forall x y, epstep x y -> epstep (F x) (F y)) ->
    forall x y, cstep x y -> cstep (F x) (F y).
Proof.
  intros F Hp He x y Hxy. destruct Hxy as [x y Hxy | x y Hxy].
  - apply cs_core. eapply rtc_pstep_congr1; eassumption.
  - apply cs_eta. eapply rtc_epstep_congr1; eassumption.
Qed.

Lemma rtc_cstep_congr1 : forall (F : term -> term),
    (forall x y, pstep x y -> pstep (F x) (F y)) ->
    (forall x y, epstep x y -> epstep (F x) (F y)) ->
    forall x y, rtc cstep x y -> rtc cstep (F x) (F y).
Proof.
  intros F Hp He x y Hxy. eapply rtc_map_rel; [|exact Hxy].
  intros a b Hab. eapply cstep_congr1; eassumption.
Qed.

(** Several component paths may use different kinds of phases.  They are
    therefore composed as an [rtc cstep] path, one argument at a time. *)
Lemma rtc_cstep_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', pstep a a' -> pstep b b' ->
      pstep (F a b) (F a' b')) ->
    (forall a a' b b', epstep a a' -> epstep b b' ->
      epstep (F a b) (F a' b')) ->
    forall a a' b b', rtc cstep a a' -> rtc cstep b b' ->
      rtc cstep (F a b) (F a' b').
Proof.
  intros F Hp He a a' b b' Ha Hb.
  eapply rtc_map_rel2 with (R := cstep) (S := cstep) (F := F).
  - intros x y z Hxy. eapply (cstep_congr1 (fun q => F q z)).
    + intros q r Hqr. apply Hp; [exact Hqr | apply pstep_refl].
    + intros q r Hqr. apply He; [exact Hqr | apply epstep_refl].
    + exact Hxy.
  - intros z x y Hxy. eapply (cstep_congr1 (fun q => F z q)).
    + intros q r Hqr. apply Hp; [apply pstep_refl | exact Hqr].
    + intros q r Hqr. apply He; [apply epstep_refl | exact Hqr].
    + exact Hxy.
  - exact Ha.
  - exact Hb.
Qed.

Lemma rtc_cstep_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      pstep a a' -> pstep b b' -> pstep c c' ->
      pstep (F a b c) (F a' b' c')) ->
    (forall a a' b b' c c',
      epstep a a' -> epstep b b' -> epstep c c' ->
      epstep (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      rtc cstep a a' -> rtc cstep b b' -> rtc cstep c c' ->
      rtc cstep (F a b c) (F a' b' c').
Proof.
  intros F Hp He a a' b b' c c' Ha Hb Hc.
  eapply rtc_map_rel3 with (R := cstep) (S := cstep) (F := F).
  - intros x y z w Hxy. eapply (cstep_congr1 (fun q => F q z w)).
    + intros q r Hqr. apply Hp; eauto using pstep_refl.
    + intros q r Hqr. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z x y w Hxy. eapply (cstep_congr1 (fun q => F z q w)).
    + intros q r Hqr. apply Hp; eauto using pstep_refl.
    + intros q r Hqr. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w x y Hxy. eapply (cstep_congr1 (fun q => F z w q)).
    + intros q r Hqr. apply Hp; eauto using pstep_refl.
    + intros q r Hqr. apply He; eauto using epstep_refl.
    + exact Hxy.
  - exact Ha.
  - exact Hb.
  - exact Hc.
Qed.

Lemma rtc_cstep_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep (F a b c d) (F a' b' c' d')) ->
    (forall a a' b b' c c' d d',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      rtc cstep a a' -> rtc cstep b b' -> rtc cstep c c' ->
      rtc cstep d d' -> rtc cstep (F a b c d) (F a' b' c' d').
Proof.
  intros F Hp He a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_map_rel4 with (R := cstep) (S := cstep) (F := F).
  - intros x y z w q Hxy. eapply (cstep_congr1 (fun u => F u z w q)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z x y w q Hxy. eapply (cstep_congr1 (fun u => F z u w q)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w x y q Hxy. eapply (cstep_congr1 (fun u => F z w u q)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w q x y Hxy. eapply (cstep_congr1 (fun u => F z w q u)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
Qed.

Lemma rtc_cstep_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep e e' -> pstep (F a b c d e) (F a' b' c' d' e')) ->
    (forall a a' b b' c c' d d' e e',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep e e' -> epstep (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      rtc cstep a a' -> rtc cstep b b' -> rtc cstep c c' ->
      rtc cstep d d' -> rtc cstep e e' ->
      rtc cstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F Hp He a a' b b' c c' d d' e e' Ha Hb Hc Hd He'.
  eapply rtc_map_rel5 with (R := cstep) (S := cstep) (F := F).
  - intros x y z w q r Hxy. eapply (cstep_congr1 (fun u => F u z w q r)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z x y w q r Hxy. eapply (cstep_congr1 (fun u => F z u w q r)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w x y q r Hxy. eapply (cstep_congr1 (fun u => F z w u q r)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w q x y r Hxy. eapply (cstep_congr1 (fun u => F z w q u r)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - intros z w q r x y Hxy. eapply (cstep_congr1 (fun u => F z w q r u)).
    + intros u v Huv. apply Hp; eauto using pstep_refl.
    + intros u v Huv. apply He; eauto using epstep_refl.
    + exact Hxy.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
  - exact He'.
Qed.

(** Joinability is a congruence for any context preserving both parallel
    relations. *)
Lemma cjoin_congr1 : forall (F : term -> term),
    (forall x y, pstep x y -> pstep (F x) (F y)) ->
    (forall x y, epstep x y -> epstep (F x) (F y)) ->
    forall x y, cjoin x y -> cjoin (F x) (F y).
Proof.
  intros F Hp He x y [w [Hxw Hyw]]. exists (F w). split;
    eapply rtc_cstep_congr1; eassumption.
Qed.

Lemma cjoin_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', pstep a a' -> pstep b b' ->
      pstep (F a b) (F a' b')) ->
    (forall a a' b b', epstep a a' -> epstep b b' ->
      epstep (F a b) (F a' b')) ->
    forall a a' b b', cjoin a a' -> cjoin b b' ->
      cjoin (F a b) (F a' b').
Proof.
  intros F Hp He a a' b b' [wa [Hawa Ha'wa]] [wb [Hbwb Hb'wb]].
  exists (F wa wb). split; eapply rtc_cstep_congr2; eassumption.
Qed.

Lemma cjoin_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      pstep a a' -> pstep b b' -> pstep c c' ->
      pstep (F a b c) (F a' b' c')) ->
    (forall a a' b b' c c',
      epstep a a' -> epstep b b' -> epstep c c' ->
      epstep (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      cjoin a a' -> cjoin b b' -> cjoin c c' ->
      cjoin (F a b c) (F a' b' c').
Proof.
  intros F Hp He a a' b b' c c'
    [wa [Hawa Ha'wa]] [wb [Hbwb Hb'wb]] [wc [Hcwc Hc'wc]].
  exists (F wa wb wc). split; eapply rtc_cstep_congr3; eassumption.
Qed.

Lemma cjoin_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep (F a b c d) (F a' b' c' d')) ->
    (forall a a' b b' c c' d d',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      cjoin a a' -> cjoin b b' -> cjoin c c' -> cjoin d d' ->
      cjoin (F a b c d) (F a' b' c' d').
Proof.
  intros F Hp He a a' b b' c c' d d'
    [wa [Hawa Ha'wa]] [wb [Hbwb Hb'wb]]
    [wc [Hcwc Hc'wc]] [wd [Hdwd Hd'wd]].
  exists (F wa wb wc wd). split; eapply rtc_cstep_congr4; eassumption.
Qed.

Lemma cjoin_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      pstep a a' -> pstep b b' -> pstep c c' -> pstep d d' ->
      pstep e e' -> pstep (F a b c d e) (F a' b' c' d' e')) ->
    (forall a a' b b' c c' d d' e e',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep e e' -> epstep (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      cjoin a a' -> cjoin b b' -> cjoin c c' -> cjoin d d' ->
      cjoin e e' -> cjoin (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F Hp He a a' b b' c c' d d' e e'
    [wa [Hawa Ha'wa]] [wb [Hbwb Hb'wb]] [wc [Hcwc Hc'wc]]
    [wd [Hdwd Hd'wd]] [we [Hewe He'we]].
  exists (F wa wb wc wd we). split; eapply rtc_cstep_congr5; eassumption.
Qed.

(** Constructor-specific interface used by conversion proofs. *)
Lemma cjoin_pi : forall A A' B B', cjoin A A' -> cjoin B B' ->
    cjoin (TPi A B) (TPi A' B').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_lam : forall b b', cjoin b b' -> cjoin (TLam b) (TLam b').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_app : forall f f' a a', cjoin f f' -> cjoin a a' ->
    cjoin (TApp f a) (TApp f' a').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_sigma : forall A A' B B', cjoin A A' -> cjoin B B' ->
    cjoin (TSigma A B) (TSigma A' B').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_pair : forall a a' b b', cjoin a a' -> cjoin b b' ->
    cjoin (TPair a b) (TPair a' b').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_fst : forall p p', cjoin p p' -> cjoin (TFst p) (TFst p').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_snd : forall p p', cjoin p p' -> cjoin (TSnd p) (TSnd p').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_conse : forall t t' E E', cjoin t t' -> cjoin E E' ->
    cjoin (TConsE t E) (TConsE t' E').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_enumt : forall E E', cjoin E E' ->
    cjoin (TEnumT E) (TEnumT E').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_esucc : forall n n', cjoin n n' ->
    cjoin (TESucc n) (TESucc n').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_epi : forall E E' P P', cjoin E E' -> cjoin P P' ->
    cjoin (TEPi E P) (TEPi E' P').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_switch : forall E E' P P' p p' e e',
    cjoin E E' -> cjoin P P' -> cjoin p p' -> cjoin e e' ->
    cjoin (TSwitch E P p e) (TSwitch E' P' p' e').
Proof.
  intros. eapply cjoin_congr4; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_idesc : forall I I', cjoin I I' ->
    cjoin (TIDesc I) (TIDesc I').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_ivar : forall i i', cjoin i i' -> cjoin (TIVar i) (TIVar i').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_iprod : forall A A' B B', cjoin A A' -> cjoin B B' ->
    cjoin (TIProd A B) (TIProd A' B').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_ipi : forall S S' T T', cjoin S S' -> cjoin T T' ->
    cjoin (TIPi S T) (TIPi S' T').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_isig : forall S S' T T', cjoin S S' -> cjoin T T' ->
    cjoin (TISig S T) (TISig S' T').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_ichoice : forall E E' T T', cjoin E E' -> cjoin T T' ->
    cjoin (TIChoice E T) (TIChoice E' T').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_interp : forall D D' X X', cjoin D D' -> cjoin X X' ->
    cjoin (TInterp D X) (TInterp D' X').
Proof.
  intros. eapply cjoin_congr2; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_mui : forall R R', cjoin R R' -> cjoin (TMuI R) (TMuI R').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_mus : forall S S', cjoin S S' -> cjoin (TMuS S) (TMuS S').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_in : forall x x', cjoin x x' -> cjoin (TIn x) (TIn x').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_ind : forall R R' P P' s s' i i' x x',
    cjoin R R' -> cjoin P P' -> cjoin s s' -> cjoin i i' ->
    cjoin x x' -> cjoin (TInd R P s i x) (TInd R' P' s' i' x').
Proof.
  intros. eapply cjoin_congr5; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_iall : forall D D' X X' xs xs' P P',
    cjoin D D' -> cjoin X X' -> cjoin xs xs' -> cjoin P P' ->
    cjoin (TIAll D X xs P) (TIAll D' X' xs' P').
Proof.
  intros. eapply cjoin_congr4; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_hyps : forall D D' X X' P P' h h' xs xs',
    cjoin D D' -> cjoin X X' -> cjoin P P' -> cjoin h h' ->
    cjoin xs xs' -> cjoin (THyps D X P h xs) (THyps D' X' P' h' xs').
Proof.
  intros. eapply cjoin_congr5; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_list : forall A A', cjoin A A' -> cjoin (TList A) (TList A').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_lnil : forall A A', cjoin A A' -> cjoin (TLNil A) (TLNil A').
Proof.
  intros. eapply cjoin_congr1; try eassumption;
    intros; constructor; assumption.
Qed.

Lemma cjoin_lcons : forall A A' a a' l l',
    cjoin A A' -> cjoin a a' -> cjoin l l' ->
    cjoin (TLCons A a l) (TLCons A' a' l').
Proof.
  intros. eapply cjoin_congr3; try eassumption;
    intros; constructor; assumption.
Qed.

Print Assumptions cstep_congr1.
Print Assumptions rtc_cstep_congr5.
Print Assumptions cjoin_congr5.
Print Assumptions cjoin_ind.
Print Assumptions cjoin_hyps.
