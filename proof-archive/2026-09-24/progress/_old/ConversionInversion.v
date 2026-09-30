Require Import TypeRulesCore Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRulesCore _tmp_epstep _work_epstep_rtc
  _work_mixed_closure _work_cjoin _work_cstep_invariants
  SignatureLemmas SignatureConversion.

Theorem conv_fconv : forall t u, conv t u -> fconv t u.
Proof.
  intros t u H; induction H; eauto using fconv, fstep.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (apply fc_step, fs_eta).
  - eapply (fconv_map2 (fun x y => TCase x y bs)); eauto using fstep.
  - eapply (fconv_map2
      (fun x y => TCase M Q (bs1 ++ (x,y) :: bs2)));
      eauto using fstep.
Qed.

Lemma conv_cjoin : forall t u, conv t u -> cjoin t u.
Proof. intros; apply fconv_cjoin, conv_fconv; assumption. Qed.

Lemma conv_pi_components : forall A B A' B',
  conv (TPi A B) (TPi A' B') -> conv A A' /\ conv B B'.
Proof.
  intros. destruct (cjoin_pi_inv _ _ _ _ (conv_cjoin _ _ H));
    split; apply cjoin_conv_bridge; assumption.
Qed.

Lemma conv_sigma_components : forall A B A' B',
  conv (TSigma A B) (TSigma A' B') -> conv A A' /\ conv B B'.
Proof.
  intros. destruct (cjoin_sigma_inv_luna _ _ _ _ (conv_cjoin _ _ H));
    split; apply cjoin_conv_bridge; assumption.
Qed.

Lemma conv_enumt_component : forall E E',
  conv (TEnumT E) (TEnumT E') -> conv E E'.
Proof.
  intros. apply cjoin_conv_bridge, enum_cjoin_inv_luna, conv_cjoin; assumption.
Qed.

Lemma pstep_idesc_inv_ci : forall I u, pstep (TIDesc I) u ->
  exists I', u = TIDesc I' /\ pstep I I'.
Proof. intros; inversion H; subst; eauto. Qed.
Lemma epstep_idesc_inv_ci : forall I u, epstep (TIDesc I) u ->
  exists I', u = TIDesc I' /\ epstep I I'.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma rtc_pstep_idesc_inv_ci : forall I u, rtc pstep (TIDesc I) u ->
  exists I', u = TIDesc I' /\ rtc pstep I I'.
Proof.
  intros I u H; remember (TIDesc I) as t eqn:E; revert I E.
  induction H; intros; subst.
  - eexists; split; [reflexivity|apply rtc_refl].
  - destruct (pstep_idesc_inv_ci _ _ H) as [I1 [-> HI]].
    destruct (IHrtc I1 eq_refl) as [I2 [-> HI2]].
    exists I2; split; [reflexivity|eauto using rtc_step].
Qed.

Lemma rtc_epstep_idesc_inv_ci : forall I u, rtc epstep (TIDesc I) u ->
  exists I', u = TIDesc I' /\ rtc epstep I I'.
Proof.
  intros I u H; remember (TIDesc I) as t eqn:E; revert I E.
  induction H; intros; subst.
  - eexists; split; [reflexivity|apply rtc_refl].
  - destruct (epstep_idesc_inv_ci _ _ H) as [I1 [-> HI]].
    destruct (IHrtc I1 eq_refl) as [I2 [-> HI2]].
    exists I2; split; [reflexivity|eauto using rtc_step].
Qed.

Lemma rtc_cstep_idesc_inv_ci : forall I u, rtc cstep (TIDesc I) u ->
  exists I', u = TIDesc I' /\ rtc cstep I I'.
Proof.
  intros I u H; remember (TIDesc I) as t eqn:E; revert I E.
  induction H; intros; subst.
  - eexists; split; [reflexivity|apply rtc_refl].
  - inversion H; subst.
    + destruct (rtc_pstep_idesc_inv_ci _ _ H1) as [I1 [-> HI]].
      destruct (IHrtc I1 eq_refl) as [I2 [-> HI2]].
      exists I2; split; [reflexivity|]. eapply rtc_step; [apply cs_core; exact HI|exact HI2].
    + destruct (rtc_epstep_idesc_inv_ci _ _ H1) as [I1 [-> HI]].
      destruct (IHrtc I1 eq_refl) as [I2 [-> HI2]].
      exists I2; split; [reflexivity|]. eapply rtc_step; [apply cs_eta; exact HI|exact HI2].
Qed.

Lemma cjoin_idesc_inv_ci : forall I I',
  cjoin (TIDesc I) (TIDesc I') -> cjoin I I'.
Proof.
  intros I I' [w [H1 H2]].
  destruct (rtc_cstep_idesc_inv_ci _ _ H1) as [J1 [E1 HI]].
  destruct (rtc_cstep_idesc_inv_ci _ _ H2) as [J2 [E2 HJ]].
  subst w. inversion E2; subst. eexists; split; eassumption.
Qed.

Lemma conv_idesc_component : forall I I',
  conv (TIDesc I) (TIDesc I') -> conv I I'.
Proof. intros; apply cjoin_conv_bridge, cjoin_idesc_inv_ci, conv_cjoin; assumption. Qed.

Lemma conv_conse_components : forall c E c' E',
  conv (TConsE c E) (TConsE c' E') -> conv c c' /\ conv E E'.
Proof.
  intros. destruct (cjoin_conse_inv_parent _ _ _ _ (conv_cjoin _ _ H));
    split; apply cjoin_conv_bridge; assumption.
Qed.

Lemma sub_idesc_endpoints_conv : forall G I I',
  sub G (TIDesc I) (TIDesc I') -> conv (TIDesc I) (TIDesc I').
Proof.
  intros G I I' Hsub.
  destruct (sub_transport G _ _ Hsub (TIDesc I') HIDesc
    (cv_refl _) (whd_shape _ HIDesc (hs_idesc I')))
    as [H | [[K _] | [K _]]].
  - exact H.
  - destruct K as [K | [K | K]]; discriminate.
  - discriminate.
Qed.

Lemma sub_enumt_endpoints_conv : forall G E E',
  sub G (TEnumT E) (TEnumT E') -> conv (TEnumT E) (TEnumT E').
Proof.
  intros G E E' Hsub.
  destruct (sub_transport G _ _ Hsub (TEnumT E') HEnumT
    (cv_refl _) (whd_shape _ HEnumT (hs_enumt E')))
    as [H | [[K _] | [K _]]].
  - exact H.
  - destruct K as [K | [K | K]]; discriminate.
  - discriminate.
Qed.

Theorem sub_idesc_target_conv_pres : forall G I0 I D,
  check G D (TIDesc I) ->
  sub G (TIDesc I0) (TIDesc I) -> conv I0 I.
Proof.
  intros G I0 I D _ Hsub.
  apply conv_idesc_component, sub_idesc_endpoints_conv with G; exact Hsub.
Qed.

Theorem sub_enum_cons_tail_conv_pres : forall G tg0 E0 tg E n,
  check G (TESucc n) (TEnumT (TConsE tg E)) ->
  sub G (TEnumT (TConsE tg0 E0)) (TEnumT (TConsE tg E)) -> conv E0 E.
Proof.
  intros G tg0 E0 tg E n _ Hsub.
  pose proof (conv_enumt_component _ _
    (sub_enumt_endpoints_conv _ _ _ Hsub)) as HC.
  exact (proj2 (conv_conse_components _ _ _ _ HC)).
Qed.

Lemma pstep_pair_inv_ci : forall a b u, pstep (TPair a b) u ->
  exists a' b', u = TPair a' b' /\ pstep a a' /\ pstep b b'.
Proof. intros; inversion H; subst; eauto. Qed.
Lemma epstep_pair_inv_ci : forall a b u, epstep (TPair a b) u ->
  exists a' b', u = TPair a' b' /\ epstep a a' /\ epstep b b'.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma rtc_pstep_pair_inv_ci : forall a b u, rtc pstep (TPair a b) u ->
  exists a' b', u = TPair a' b' /\ rtc pstep a a' /\ rtc pstep b b'.
Proof.
  intros a b u H; remember (TPair a b) as t eqn:E; revert a b E.
  induction H; intros; subst.
  - exists a,b; repeat split; apply rtc_refl.
  - destruct (pstep_pair_inv_ci _ _ _ H) as [a1 [b1 [-> [Ha Hb]]]].
    destruct (IHrtc a1 b1 eq_refl) as [a2 [b2 [-> [Ha2 Hb2]]]].
    exists a2,b2; repeat split; eauto using rtc_step.
Qed.
Lemma rtc_epstep_pair_inv_ci : forall a b u, rtc epstep (TPair a b) u ->
  exists a' b', u = TPair a' b' /\ rtc epstep a a' /\ rtc epstep b b'.
Proof.
  intros a b u H; remember (TPair a b) as t eqn:E; revert a b E.
  induction H; intros; subst.
  - exists a,b; repeat split; apply rtc_refl.
  - destruct (epstep_pair_inv_ci _ _ _ H) as [a1 [b1 [-> [Ha Hb]]]].
    destruct (IHrtc a1 b1 eq_refl) as [a2 [b2 [-> [Ha2 Hb2]]]].
    exists a2,b2; repeat split; eauto using rtc_step.
Qed.
Lemma rtc_cstep_pair_inv_ci : forall a b u, rtc cstep (TPair a b) u ->
  exists a' b', u = TPair a' b' /\ rtc cstep a a' /\ rtc cstep b b'.
Proof.
  intros a b u H; remember (TPair a b) as t eqn:E; revert a b E.
  induction H; intros; subst.
  - exists a,b; repeat split; apply rtc_refl.
  - inversion H; subst.
    + destruct (rtc_pstep_pair_inv_ci _ _ _ H1) as [a1 [b1 [-> [Ha Hb]]]].
      destruct (IHrtc a1 b1 eq_refl) as [a2 [b2 [-> [Ha2 Hb2]]]].
      exists a2,b2; repeat split; eauto using rtc_step, cs_core.
    + destruct (rtc_epstep_pair_inv_ci _ _ _ H1) as [a1 [b1 [-> [Ha Hb]]]].
      destruct (IHrtc a1 b1 eq_refl) as [a2 [b2 [-> [Ha2 Hb2]]]].
      exists a2,b2; repeat split; eauto using rtc_step, cs_eta.
Qed.
Lemma cjoin_pair_inv_ci : forall a b a' b',
  cjoin (TPair a b) (TPair a' b') -> cjoin a a' /\ cjoin b b'.
Proof.
  intros a b a' b' [w [H1 H2]].
  destruct (rtc_cstep_pair_inv_ci _ _ _ H1) as [x [y [E1 [Ha Hb]]]].
  destruct (rtc_cstep_pair_inv_ci _ _ _ H2) as [x' [y' [E2 [Ha' Hb']]]].
  subst w. inversion E2; subst. split; unfold cjoin; eauto.
Qed.

Lemma pstep_mui_inv_ci : forall R u, pstep (TMuI R) u ->
  exists R', u = TMuI R' /\ pstep R R'.
Proof. intros; inversion H; subst; eauto. Qed.
Lemma epstep_mui_inv_ci : forall R u, epstep (TMuI R) u ->
  exists R', u = TMuI R' /\ epstep R R'.
Proof. intros; inversion H; subst; eauto. Qed.
Lemma pstep_muiapp_inv_ci : forall R i u, pstep (TApp (TMuI R) i) u ->
  exists R' i', u = TApp (TMuI R') i' /\ pstep R R' /\ pstep i i'.
Proof.
  intros R i u H; inversion H; subst.
  destruct (pstep_mui_inv_ci _ _ H2) as [R' [-> HR]].
  exists R',a'; repeat split; assumption.
Qed.
Lemma epstep_muiapp_inv_ci : forall R i u, epstep (TApp (TMuI R) i) u ->
  exists R' i', u = TApp (TMuI R') i' /\ epstep R R' /\ epstep i i'.
Proof.
  intros R i u H; inversion H; subst.
  destruct (epstep_mui_inv_ci _ _ H2) as [R' [-> HR]].
  exists R',a'; repeat split; assumption.
Qed.
Lemma rtc_pstep_muiapp_inv_ci : forall R i u, rtc pstep (TApp (TMuI R) i) u ->
  exists R' i', u = TApp (TMuI R') i' /\ rtc pstep R R' /\ rtc pstep i i'.
Proof.
  intros R i u H; remember (TApp (TMuI R) i) as t eqn:E; revert R i E.
  induction H; intros; subst.
  - exists R,i; repeat split; apply rtc_refl.
  - destruct (pstep_muiapp_inv_ci _ _ _ H) as [R1 [i1 [-> [HR Hi]]]].
    destruct (IHrtc R1 i1 eq_refl) as [R2 [i2 [-> [HR2 Hi2]]]].
    exists R2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma rtc_epstep_muiapp_inv_ci : forall R i u, rtc epstep (TApp (TMuI R) i) u ->
  exists R' i', u = TApp (TMuI R') i' /\ rtc epstep R R' /\ rtc epstep i i'.
Proof.
  intros R i u H; remember (TApp (TMuI R) i) as t eqn:E; revert R i E.
  induction H; intros; subst.
  - exists R,i; repeat split; apply rtc_refl.
  - destruct (epstep_muiapp_inv_ci _ _ _ H) as [R1 [i1 [-> [HR Hi]]]].
    destruct (IHrtc R1 i1 eq_refl) as [R2 [i2 [-> [HR2 Hi2]]]].
    exists R2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma rtc_cstep_muiapp_inv_ci : forall R i u, rtc cstep (TApp (TMuI R) i) u ->
  exists R' i', u = TApp (TMuI R') i' /\ rtc cstep R R' /\ rtc cstep i i'.
Proof.
  intros R i u H; remember (TApp (TMuI R) i) as t eqn:E; revert R i E.
  induction H; intros; subst.
  - exists R,i; repeat split; apply rtc_refl.
  - inversion H; subst.
    + destruct (rtc_pstep_muiapp_inv_ci _ _ _ H1) as [R1 [i1 [-> [HR Hi]]]].
      destruct (IHrtc R1 i1 eq_refl) as [R2 [i2 [-> [HR2 Hi2]]]].
      exists R2,i2; repeat split; eauto using rtc_step, cs_core.
    + destruct (rtc_epstep_muiapp_inv_ci _ _ _ H1) as [R1 [i1 [-> [HR Hi]]]].
      destruct (IHrtc R1 i1 eq_refl) as [R2 [i2 [-> [HR2 Hi2]]]].
      exists R2,i2; repeat split; eauto using rtc_step, cs_eta.
Qed.
Lemma cjoin_muiapp_inv_ci : forall R R' i i',
  cjoin (TApp (TMuI R) i) (TApp (TMuI R') i') ->
  cjoin R R' /\ cjoin i i'.
Proof.
  intros R R' i i' [w [H1 H2]].
  destruct (rtc_cstep_muiapp_inv_ci _ _ _ H1) as [X [j [E1 [HR Hi]]]].
  destruct (rtc_cstep_muiapp_inv_ci _ _ _ H2) as [X' [j' [E2 [HR' Hi']]]].
  subst w. inversion E2; subst. split; unfold cjoin; eauto.
Qed.

Lemma cjoin_sigmuapp_inv_ci : forall E S E' S' i i',
  cjoin (TApp (SigMu E S) i) (TApp (SigMu E' S') i') ->
  cjoin E E' /\ cjoin S S' /\ cjoin i i'.
Proof.
  intros E S E' S' i i' H.
  destruct (cjoin_musapp_inv_luna _ _ _ _ H) as [HES Hi].
  destruct (cjoin_pair_inv_ci _ _ _ _ HES) as [HE HS]. auto.
Qed.

Lemma conv_muiapp_components : forall R R' i i',
  conv (TApp (TMuI R) i) (TApp (TMuI R') i') ->
  conv R R' /\ conv i i'.
Proof.
  intros. destruct (cjoin_muiapp_inv_ci _ _ _ _ (conv_cjoin _ _ H));
    split; apply cjoin_conv_bridge; assumption.
Qed.

Lemma conv_sigmuapp_components : forall E S E' S' i i',
  conv (TApp (SigMu E S) i) (TApp (SigMu E' S') i') ->
  conv E E' /\ conv S S' /\ conv i i'.
Proof.
  intros. destruct (cjoin_sigmuapp_inv_ci _ _ _ _ _ _ (conv_cjoin _ _ H))
    as [HE [HS Hi]]. repeat split; apply cjoin_conv_bridge; assumption.
Qed.

Theorem checked_pair_fst_pres : forall G a b A B k,
  check G (TSigma A B) (TSort k) ->
  check G (TPair a b) (TSigma A B) -> check G a A.
Proof.
  intros G a b A B k _ Hpair.
  destruct (pair_origin _ _ _ _ Hpair) as [A0 [B0 [Ha [Hb Hsub]]]].
  destruct (conv_sigma_components _ _ _ _
    (sub_sigma_endpoints_conv _ _ _ _ _ Hsub)) as [HA _].
  eapply ch_expand; [apply cv_sym; exact HA | exact Ha].
Qed.
