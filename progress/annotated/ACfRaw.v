(* Raw facts for confluence modulo annotations: freshness of a variable is
   preserved by reduction, and a raw normal form that is convertible or
   universe-comparable to a term not mentioning a variable does not mention
   it either. Freshness is expressed in lifted form. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AStepFunction.
Require nameless.DBConfluence nameless.DBGeneration nameless.DBCommutation.
Import ListNotations.
Module RCf := nameless.DBConfluence.
Module RG := nameless.DBGeneration.

Definition raw_fresh x r := exists r0, r = Raw.lift 1 x r0.
Definition raw_normal r := forall s, ~ RCore.reduction r s.

Lemma raw_fresh_lift : forall x r, raw_fresh x (Raw.lift 1 x r).
Proof. intros; exists r; reflexivity. Qed.

Lemma raw_fresh_shift : forall x A, raw_fresh x A -> raw_fresh (S x) (Raw.lift 1 0 A).
Proof.
  intros x A [A0 ->]; exists (Raw.lift 1 0 A0).
  pose proof (RB.lift_lift_comm A0 1 1 0 x (Nat.le_0_l x)) as H; cbn in H.
  now rewrite H.
Qed.

Lemma raw_fresh_subst : forall x a B, raw_fresh x a -> raw_fresh (S x) B ->
  raw_fresh x (Raw.subst a 0 B).
Proof.
  intros x a B [a0 ->] [B0 ->]; exists (Raw.subst a0 0 B0).
  pose proof (RB.lift_subst_comm B0 a0 1 x 0) as H; cbn in H; now rewrite H.
Qed.

Lemma raw_fresh_old_lift : forall x y A, x <= y ->
  raw_fresh x (Raw.lift (S y) 0 A).
Proof.
  intros x y A Hxy; exists (Raw.lift y 0 A).
  pose proof (RB.lift_fuse A 1 y 0 x Hxy) as H; cbn in H; now rewrite H.
Qed.

Lemma raw_reduction_fresh : forall r s, RCore.reduction r s ->
  forall x, raw_fresh x r -> raw_fresh x s.
Proof.
  intros r s H x [r0 ->].
  destruct (RCf.reduction_parallel _ _ H) as [Hp|He].
  - destruct (nameless.DBCommutation.pstep_lift_inverse _ _ Hp r0 x eq_refl)
      as [u [-> _]]; exists u; reflexivity.
  - destruct (nameless.DBEta.epstep_lift_inverse _ _ He r0 x eq_refl)
      as [u [-> _]]; exists u; reflexivity.
Qed.

Lemma raw_reductions_fresh : forall r s, RB.rtc RCore.reduction r s ->
  forall x, raw_fresh x r -> raw_fresh x s.
Proof. intros r s H; induction H; eauto using raw_reduction_fresh. Qed.

Lemma raw_normal_reductions : forall r s, raw_normal r ->
  RB.rtc RCore.reduction r s -> s = r.
Proof.
  intros r s HN H; destruct H; [reflexivity|exfalso; eapply HN; eassumption].
Qed.

Lemma raw_normal_conv_fresh : forall x r s, raw_normal r -> RCore.conv r s ->
  raw_fresh x s -> raw_fresh x r.
Proof.
  intros x r s HN HC HF.
  destruct (RCf.conversion_joinable _ _ HC) as [w [Hr Hs]].
  apply raw_normal_reductions in Hr; [subst w|exact HN].
  eapply raw_reductions_fresh; eassumption.
Qed.

Lemma raw_conv_fresh_join : forall x r s, RCore.conv r s -> raw_fresh x s ->
  RCore.conv r s.
Proof. auto. Qed.

Lemma raw_normal_pi : forall A B, raw_normal (Raw.TPi A B) ->
  raw_normal A /\ raw_normal B.
Proof.
  intros A B H; split; intros s Hs; eapply H;
    [apply RCore.red_TPi_A|apply RCore.red_TPi_B]; exact Hs.
Qed.

Lemma raw_fresh_pi_inv : forall x A B, raw_fresh x (Raw.TPi A B) ->
  raw_fresh x A /\ raw_fresh (S x) B.
Proof.
  intros x A B [r0 H]; destruct r0; cbn [Raw.lift] in H; try discriminate.
  - destruct (n <? x); discriminate.
  - inversion H; subst; split; eexists; reflexivity.
Qed.

Lemma raw_fresh_pi : forall x A B, raw_fresh x A -> raw_fresh (S x) B ->
  raw_fresh x (Raw.TPi A B).
Proof.
  intros x A B [A0 ->] [B0 ->]; exists (Raw.TPi A0 B0); reflexivity.
Qed.

Lemma raw_pi_inj : forall A B A' B', Raw.TPi A B = Raw.TPi A' B' -> A = A' /\ B = B'.
Proof. intros ? ? ? ? E; inversion E; auto. Qed.

Lemma raw_pi_reductions : forall A B t, RB.rtc RCore.reduction (Raw.TPi A B) t ->
  exists A' B', t = Raw.TPi A' B' /\ RB.rtc RCore.reduction A A' /\ RB.rtc RCore.reduction B B'.
Proof. exact (RG.reduces_binary Raw.TPi RG.reduction_pi). Qed.

(* A convertible term free of x yields a Pi view whose components are also
   free of x (up to conversion). *)
Lemma fresh_pi_view : forall x s X Y, RCore.conv s (Raw.TPi X Y) ->
  (exists s0, RCore.conv s (Raw.lift 1 x s0)) ->
  (exists X0, RCore.conv X (Raw.lift 1 x X0)) /\
  (exists Y0, RCore.conv Y (Raw.lift 1 (S x) Y0)).
Proof.
  intros x s X Y HP [s0 Hs].
  assert (HC : RCore.conv (Raw.lift 1 x s0) (Raw.TPi X Y)) by
    (eapply RCore.cv_trans; [apply RCore.cv_sym; exact Hs|exact HP]).
  destruct (RCf.conversion_joinable _ _ HC) as [w [Hl Hp]].
  destruct (raw_pi_reductions _ _ _ Hp) as [X' [Y' [-> [HX HY]]]].
  destruct (raw_reductions_fresh _ _ Hl x (raw_fresh_lift _ _)) as [w0 Hw].
  destruct (raw_fresh_pi_inv x X' Y' (ex_intro _ w0 Hw)) as [[X0 HX0] [Y0 HY0]].
  split; [exists X0|exists Y0]; [rewrite <- HX0|rewrite <- HY0];
    apply nameless.DBWeakening.reductions_conversion; assumption.
Qed.

Lemma raw_normal_pi_view : forall r U V, raw_normal r -> RCore.conv r (Raw.TPi U V) ->
  exists U' V', r = Raw.TPi U' V' /\ RCore.conv U U' /\ RCore.conv V V'.
Proof.
  intros r U V HN HC.
  destruct (RCf.conversion_joinable _ _ HC) as [w [Hr Hp]].
  apply raw_normal_reductions in Hr; [subst w|exact HN].
  destruct (raw_pi_reductions _ _ _ Hp) as [U' [V' [-> [HU HV]]]].
  exists U', V'; split; [reflexivity|split];
    apply nameless.DBWeakening.reductions_conversion; assumption.
Qed.

Lemma raw_normal_sort_view : forall r k, raw_normal r -> RCore.conv r (Raw.TSort k) ->
  r = Raw.TSort k.
Proof.
  intros r k HN HC.
  destruct (RCf.conversion_joinable _ _ HC) as [w [Hr Hs]].
  apply raw_normal_reductions in Hr; [subst w|exact HN].
  exact (RC.sort_reductions_identity _ _ Hs).
Qed.

(* Both sides of a universe comparison transfer freshness to raw normal
   forms of the other side. *)
Theorem comparison_fresh : forall A B, RC.type_comparison A B -> forall x,
  (forall r, raw_normal r -> RCore.conv r A ->
     (exists s0, RCore.conv B (Raw.lift 1 x s0)) -> raw_fresh x r) /\
  (forall r, raw_normal r -> RCore.conv r B ->
     (exists s0, RCore.conv A (Raw.lift 1 x s0)) -> raw_fresh x r).
Proof.
  intros A B H; induction H as [A B HAB|A B j k HA HB Hjk|A B U V X Y HA HB HX IHX HY IHY];
    intros x; split; intros r HN Hr [s0 Hs].
  - apply (raw_normal_conv_fresh x r (Raw.lift 1 x s0) HN); [|apply raw_fresh_lift].
    eapply RCore.cv_trans; [exact Hr|eapply RCore.cv_trans; [exact HAB|exact Hs]].
  - apply (raw_normal_conv_fresh x r (Raw.lift 1 x s0) HN); [|apply raw_fresh_lift].
    eapply RCore.cv_trans; [exact Hr|eapply RCore.cv_trans; [apply RCore.cv_sym; exact HAB|exact Hs]].
  - rewrite (raw_normal_sort_view r j HN (RCore.cv_trans Hr HA)).
    exists (Raw.TSort j); reflexivity.
  - rewrite (raw_normal_sort_view r k HN (RCore.cv_trans Hr HB)).
    exists (Raw.TSort k); reflexivity.
  - destruct (raw_normal_pi_view r U V HN (RCore.cv_trans Hr HA))
      as [U' [V' [-> [HU HV]]]].
    destruct (raw_normal_pi _ _ HN) as [HNU HNV].
    destruct (fresh_pi_view x B X Y HB (ex_intro _ s0 Hs)) as [HX0 HY0].
    apply raw_fresh_pi.
    + exact (proj2 (IHX x) U' HNU (RCore.cv_sym HU) HX0).
    + exact (proj1 (IHY (S x)) V' HNV (RCore.cv_sym HV) HY0).
  - destruct (raw_normal_pi_view r X Y HN (RCore.cv_trans Hr HB))
      as [X' [Y' [-> [HX' HY']]]].
    destruct (raw_normal_pi _ _ HN) as [HNX HNY].
    destruct (fresh_pi_view x A U V HA (ex_intro _ s0 Hs)) as [HU0 HV0].
    apply raw_fresh_pi.
    + exact (proj1 (IHX x) X' HNX (RCore.cv_sym HX') HU0).
    + exact (proj2 (IHY (S x)) Y' HNY (RCore.cv_sym HY') HV0).
Qed.

Corollary comparison_fresh_left : forall x r T, RC.type_comparison r T ->
  raw_normal r -> raw_fresh x T -> raw_fresh x r.
Proof.
  intros x r T H HN [T0 ->].
  exact (proj1 (comparison_fresh _ _ H x) r HN (RCore.cv_refl _)
    (ex_intro _ T0 (RCore.cv_refl _))).
Qed.

Corollary comparison_fresh_right : forall x P r, RC.type_comparison P r ->
  raw_normal r -> raw_fresh x P -> raw_fresh x r.
Proof.
  intros x P r H HN [P0 ->].
  exact (proj2 (comparison_fresh _ _ H x) r HN (RCore.cv_refl _)
    (ex_intro _ P0 (RCore.cv_refl _))).
Qed.

Print Assumptions comparison_fresh.
