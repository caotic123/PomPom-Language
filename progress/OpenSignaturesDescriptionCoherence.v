(* Description coercions agree by conversion on every closed input.
   Contextual equivalence of the coercion functions is a separate obligation. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRowViews.
Import ListNotations.

Lemma identity_for_beta : forall ts t, conv (TApp (identity_for ts) t) t.
Proof.
  intros; unfold identity_for; apply cv_step, st_root.
  cbn [root_step subst substitute]; now rewrite Nat.eqb_refl.
Qed.

Lemma row_branch_typing : forall Gamma IT rs n name D,
  row_input Gamma IT rs -> nth_error rs n = Some (name,D) ->
  typing Gamma D (TIDesc IT).
Proof.
  intros Gamma IT rs n name D [_ [_ Hcodes]] Hnth.
  apply Forall_forall with (x:=(name,D)) in Hcodes;
    [exact Hcodes|eapply nth_error_In; exact Hnth].
Qed.

Lemma row_views_convertible_codes : forall Gamma IT D D' rs rt,
  row_view Gamma IT D rs -> row_view Gamma IT D' rt -> conv D D' ->
  conv (row_code IT rs) (row_code IT rt).
Proof.
  intros Gamma IT D D' rs rt Hrs Hrt H.
  destruct Hrs as [rs Hr HD HC], Hrt as [rt Ht HD' HC'].
  eapply cv_trans; [apply cv_sym; exact HC|].
  eapply cv_trans; eassumption.
Qed.

Lemma row_maps_convertible_views : forall IT X Y source source' target target' hs hs' t,
  row_input empty_ctx IT source -> row_input empty_ctx IT source' ->
  NoDup (row_names target') -> typing empty_ctx X (Family IT) ->
  conv (row_code IT source) (row_code IT source') ->
  conv (row_code IT target) (row_code IT target') ->
  row_handlers empty_ctx IT X Y target source hs ->
  row_handlers empty_ctx IT X Y target' source' hs' ->
  typing empty_ctx t (TInterp IT (row_code IT source) X) ->
  conv (TApp (row_map 0 IT source X Y hs) t)
       (TApp (row_map 0 IT source' X Y hs') t).
Proof.
  intros IT X Y source source' target target' hs hs' t Hr Hr' Hnd HX Hs Ht HH HH' HT.
  destruct (row_payload_canonical _ _ _ _ Hr HX HT)
    as [name [D [n [xs [Hnth [HC Hxs]]]]]].
  destruct (row_code_position_transport _ _ _ _ Hs _ _ _ Hnth) as [D' [Hnth' HDD']].
  assert (Hxs' : typing empty_ctx xs (TInterp IT D' X)).
  { eapply ty_conv; [exact Hxs| |now apply interp_conversion].
    apply ty_interp; [exact (proj1 Hr')|eapply row_branch_typing; eassumption|exact HX]. }
  destruct (row_handlers_live_at _ _ _ _ _ _ HH _ _ _ _ Hnth Hxs)
    as [m [C [Hm Hhm]]].
  destruct (row_handlers_live_at _ _ _ _ _ _ HH' _ _ _ _ Hnth' Hxs')
    as [m' [C' [Hm' Hhm']]].
  destruct (row_code_position_transport _ _ _ _ Ht _ _ _ Hm) as [C'' [Hm'' _]].
  assert (m=m') by (eapply row_position_unique; [exact Hnd|exact Hm''|exact Hm']); subst m'.
  assert (Hleft : conv (TApp (row_map 0 IT source X Y hs) t) (TApp (retag_handler m) xs)).
  { eapply cv_trans; [apply cv_compatible, cp_TApp; [apply cv_refl|exact HC]|].
    eapply row_map_selected; eassumption. }
  eapply cv_trans; [exact Hleft|apply cv_sym].
  eapply cv_trans; [apply cv_compatible, cp_TApp; [apply cv_refl|exact HC]|].
  eapply row_map_selected; eassumption.
Qed.

Lemma row_map_convertible_identity : forall IT X Y source target hs t,
  row_input empty_ctx IT source -> NoDup (row_names target) ->
  typing empty_ctx X (Family IT) ->
  conv (row_code IT source) (row_code IT target) ->
  row_handlers empty_ctx IT X Y target source hs ->
  typing empty_ctx t (TInterp IT (row_code IT source) X) ->
  conv (TApp (row_map 0 IT source X Y hs) t) t.
Proof.
  intros IT X Y source target hs t Hr Hnd HX Hconv HH HT.
  destruct (row_payload_canonical _ _ _ _ Hr HX HT)
    as [name [D [n [xs [Hnth [HC Hxs]]]]]].
  destruct (row_code_position_transport _ _ _ _ Hconv _ _ _ Hnth) as [D' [Hn' _]].
  destruct (row_handlers_live_at _ _ _ _ _ _ HH _ _ _ _ Hnth Hxs)
    as [m [C [Hm Hhm]]].
  assert (n=m) by (eapply row_position_unique; eassumption); subst m.
  eapply cv_trans; [apply cv_compatible, cp_TApp; [apply cv_refl|exact HC]|].
  eapply cv_trans; [eapply row_map_selected; eassumption|].
  eapply cv_trans; [apply retag_handler_beta|now apply cv_sym].
Qed.

Lemma row_view_payload_typing : forall IT D X rs t,
  row_view empty_ctx IT D rs -> typing empty_ctx X (Family IT) ->
  typing empty_ctx t (TInterp IT D X) ->
  typing empty_ctx t (TInterp IT (row_code IT rs) X).
Proof.
  intros IT D X rs t Hrow HX HT; destruct Hrow as [rs Hr HD HC].
  eapply ty_conv; [exact HT| |now apply interp_conversion].
  apply ty_interp; [exact (proj1 Hr)| |exact HX].
  exact (row_code_from_weakening named_weakening _ _ _ Hr).
Qed.

Theorem description_conversion_identity : forall IT D D' X q t,
  desc_sub empty_ctx IT D D' X q -> conv D D' ->
  typing empty_ctx t (TInterp IT D X) -> conv (TApp q t) t.
Proof.
  intros IT D D' X q t Hsub HC HT.
  remember empty_ctx as Gamma eqn:EG in Hsub, HT; destruct Hsub; subst Gamma.
  - apply identity_for_beta.
  - exfalso; eapply dead_payload_absurd; eassumption.
  - destruct H as [HIT [HD HX]].
    eapply row_map_convertible_identity.
    + inversion H1; assumption.
    + inversion H2; subst; match goal with Hrow : row_input _ _ rt |- _ => exact (proj1 (proj2 Hrow)) end.
    + exact HX.
    + eapply row_views_convertible_codes; eassumption.
    + exact H3.
    + eapply row_view_payload_typing; eassumption.
Qed.

Theorem description_coercions_closed_pointwise_coherence : forall IT D D' X q r t,
  desc_sub empty_ctx IT D D' X q -> desc_sub empty_ctx IT D D' X r ->
  typing empty_ctx t (TInterp IT D X) -> conv (TApp q t) (TApp r t).
Proof.
  intros IT D D' X q r t Hq Hr HT; pose proof Hq as Hq0; pose proof Hr as Hr0.
  remember empty_ctx as Gamma eqn:EG in Hq, Hr, HT, Hq0, Hr0.
  destruct Hq as [G IT D D' X Hi Hi' HC|G IT D D' X d Hd Hi'|
    G IT D D' X rs rt hs Hi Hi' Hrs Hrt HH].
  - subst G; eapply cv_trans; [apply identity_for_beta|apply cv_sym].
    eapply description_conversion_identity; eassumption.
  - subst G; exfalso; eapply dead_payload_absurd; eassumption.
  - destruct Hr as [G IT D D' X Hj Hj' HC|G IT D D' X d Hd Hj'|
      G IT D D' X rs' rt' hs' Hj Hj' Hrs' Hrt' HH']; subst G.
    + eapply cv_trans; [eapply description_conversion_identity; eassumption|].
      apply cv_sym, identity_for_beta.
    + exfalso; eapply dead_payload_absurd; eassumption.
    + destruct Hi as [HIT [HD HX]].
      eapply row_maps_convertible_views.
      * inversion Hrs; assumption.
      * inversion Hrs'; assumption.
      * inversion Hrt'; subst; match goal with Hrow : row_input _ _ rt' |- _ => exact (proj1 (proj2 Hrow)) end.
      * exact HX.
      * eapply row_views_convertible_codes; [exact Hrs|exact Hrs'|apply cv_refl].
      * eapply row_views_convertible_codes; [exact Hrt|exact Hrt'|apply cv_refl].
      * exact HH.
      * exact HH'.
      * eapply row_view_payload_typing; eassumption.
Qed.

Print Assumptions description_conversion_identity.
Print Assumptions description_coercions_closed_pointwise_coherence.
