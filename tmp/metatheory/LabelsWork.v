From Stdlib Require Import List Arith Bool String Lia.
Require Export NamedConfluence OpenSignaturesElaboration.
Import ListNotations.

Lemma raw_head : forall t u h k, conv t u ->
  term_head t = Some h -> term_head u = Some k -> h = k.
Proof.
  intros t u h k H Ht Hu.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  pose proof (reduces_head _ _ Hw _ Ht) as Hwh.
  pose proof (reduces_head _ _ Hw' _ Hu) as Hwk.
  pose proof (alpha_head _ _ Ha _ Hwh). congruence.
Qed.
Lemma reduces_tag : forall s u, reduces (TTag s) u -> u = TTag s.
Proof.
  intros s u H; remember (TTag s) as t eqn:E; induction H; subst; auto.
  inversion H; subst; cbn [root_step] in *; discriminate.
Qed.
Lemma conv_tags : forall a b, conv (TTag a) (TTag b) -> a = b.
Proof.
  intros a b H. destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  apply reduces_tag in Hw; apply reduces_tag in Hw'; subst.
  cbn [alpha_equiv alpha_eqb alpha_eqb_in] in Ha. now apply String.eqb_eq in Ha.
Qed.
Lemma reduction_conse : forall a E t, reduction (TConsE a E) t ->
  exists b F, t = TConsE b F /\ reduces a b /\ reduces E F.
Proof.
  intros a E t H; inversion H; subst; cbn [root_step] in *;
    try discriminate; eauto 6 using reduces.
Qed.
Lemma reduces_conse : forall a E t, reduces (TConsE a E) t ->
  exists b F, t = TConsE b F /\ reduces a b /\ reduces E F.
Proof.
  intros a E t H; remember (TConsE a E) as src eqn:Heq.
  revert a E Heq; induction H; intros a F Heq; subst.
  - eauto using reduces.
  - destruct (reduction_conse _ _ _ H) as [b [G [-> [Hb HG]]]].
    destruct (IHreduces b G eq_refl) as [c [J [-> [Hc HJ]]]].
    exists c, J; repeat split; eauto using reduces_trans.
Qed.
Lemma joined_conv : forall t t' u u', reduces t t' -> reduces u u' ->
  alpha_equiv t' u' -> conv t u.
Proof.
  intros t t' u u' Ht Hu Ha.
  eapply cv_trans; [exact (reduces_conv _ _ Ht)|].
  eapply cv_trans; [apply cv_alpha;exact Ha|apply cv_sym;exact (reduces_conv _ _ Hu)].
Qed.
Lemma conv_conse : forall a E b F, conv (TConsE a E) (TConsE b F) ->
  conv a b /\ conv E F.
Proof.
  intros a E b F H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_conse _ _ _ Hw) as [a' [E' [-> [Ha' HE']]]].
  destruct (reduces_conse _ _ _ Hw') as [b' [F' [-> [Hb' HF']]]].
  change (alpha_eqb a' b' && alpha_eqb E' F' = true) in Ha.
  apply Bool.andb_true_iff in Ha. destruct Ha as [Hab HEF].
  split; eapply joined_conv; eassumption.
Qed.

Lemma label_row_position : forall E name label, label_at E name label ->
  forall rs, conv E (row_enum rs) ->
  exists n D, nth_error rs n = Some (name,D) /\ conv label (enum_position n).
Proof.
  intros E name label H; induction H; intros rs Hrs.
  - destruct rs as [|[s D] rs].
    + exfalso; pose proof (raw_head _ _ _ _ Hrs eq_refl eq_refl); discriminate.
    + cbn [row_enum] in Hrs. apply conv_conse in Hrs; destruct Hrs as [Hs HE].
      apply conv_tags in Hs; subst s. exists 0, D; split; [reflexivity|apply cv_refl].
  - destruct rs as [|[s D] rs].
    + exfalso; pose proof (raw_head _ _ _ _ Hrs eq_refl eq_refl); discriminate.
    + cbn [row_enum] in Hrs. apply conv_conse in Hrs; destruct Hrs as [Hs HE].
      destruct (IHlabel_at rs HE) as [n [D' [Hn Hlabel]]].
      exists (S n), D'; split; [exact Hn|].
      apply cv_compatible, cp_TESucc; assumption.
  - destruct (IHlabel_at rs (cv_trans H Hrs)) as [n [D [Hn Hlabel]]].
    exists n, D; split; [assumption|].
    eapply cv_trans with (u:=label); [apply cv_sym; exact H0|exact Hlabel].
Qed.
Lemma row_position_unique : forall rs name n m D E,
  NoDup (row_names rs) -> nth_error rs n = Some (name,D) ->
  nth_error rs m = Some (name,E) -> n = m.
Proof.
  induction rs as [|[s T] rs IH]; intros name n m D E Hnd Hn Hm;
    destruct n, m; cbn in *; try discriminate.
  - reflexivity.
  - inversion Hn; subst. inversion Hnd as [|? ? Hnot Htail]; subst.
    exfalso; apply Hnot. apply in_map_iff. exists (name,E); split;
      [reflexivity|eapply nth_error_In;exact Hm].
  - inversion Hm; subst. inversion Hnd as [|? ? Hnot Htail]; subst.
    exfalso; apply Hnot. apply in_map_iff. exists (name,D); split;
      [reflexivity|eapply nth_error_In;exact Hn].
  - inversion Hnd as [|? ? Hnot Htail]; subst. f_equal. eapply IH; eassumption.
Qed.
Theorem labels_unique : forall rs name a b,
  NoDup (row_names rs) -> label_at (row_enum rs) name a ->
  label_at (row_enum rs) name b -> conv a b.
Proof.
  intros rs name a b Hnd Ha Hb.
  destruct (label_row_position _ _ _ Ha rs (cv_refl _)) as [n [D [Hn Ha']]].
  destruct (label_row_position _ _ _ Hb rs (cv_refl _)) as [m [E [Hm Hb']]].
  assert (n = m) by (eapply row_position_unique; eassumption). subst m.
  eapply cv_trans; [exact Ha'|now apply cv_sym].
Qed.
