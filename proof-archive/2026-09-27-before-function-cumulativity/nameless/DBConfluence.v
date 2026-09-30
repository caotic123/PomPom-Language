Require Export nameless.DBReduction nameless.DBParallel.
(* Push one parallel core step across an arbitrary parallel eta path. *)
Lemma pstep_epsteps_commute : forall x y,
    pstep x y -> forall z, rtc epstep x z ->
    exists w, rtc epstep y w /\ rtc pstep z w.
Proof.
  intros x y Hxy z Hxz. revert y Hxy.
  induction Hxz as [x | x z1 z Hxz1 Hrest IH]; intros y Hxy.
  - exists y. split; [apply rtc_refl | apply rtc_one; exact Hxy].
  - destruct (pstep_epstep_commute _ _ _ Hxy Hxz1)
      as [q [Hyq Hz1q]].
    destruct (IH q Hz1q) as [w [Hqw Hzw]].
    exists w. split.
    + eapply rtc_trans; eassumption.
    + exact Hzw.
Qed.

(* Push an arbitrary core path across an arbitrary eta path. *)
Lemma psteps_epsteps_commute : forall x y,
    rtc pstep x y -> forall z, rtc epstep x z ->
    exists w, rtc epstep y w /\ rtc pstep z w.
Proof.
  intros x y Hxy z Hxz. revert z Hxz.
  induction Hxy as [x | x y1 y Hxy1 Hrest IH]; intros z Hxz.
  - exists z. split; [exact Hxz | apply rtc_refl].
  - destruct (pstep_epsteps_commute _ _ Hxy1 _ Hxz)
      as [q [Hy1q Hzq]].
    destruct (IH q Hy1q) as [w [Hyw Hqw]].
    exists w. split.
    + exact Hyw.
    + eapply rtc_trans; eassumption.
Qed.

(* One phase is an arbitrary block of either kind.  Treating whole blocks
   as single phases turns Hindley--Rosen commutation into an ordinary
   diamond argument. *)
Inductive cstep : term -> term -> Prop :=
| cs_core : forall t u, rtc pstep t u -> cstep t u
| cs_eta : forall t u, rtc epstep t u -> cstep t u.

Lemma cstep_refl : forall t, cstep t t.
Proof. intros t. apply cs_core, rtc_refl. Qed.

Lemma cstep_diamond : diamond cstep.
Proof.
  unfold diamond. intros x y z Hxy Hxz.
  destruct Hxy as [x y Hxy | x y Hxy];
    destruct Hxz as [x z Hxz | x z Hxz].
  - destruct (pstep_confluent x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w. split; apply cs_core; assumption.
  - destruct (psteps_epsteps_commute _ _ Hxy _ Hxz)
      as [w [Hyw Hzw]].
    exists w. split; [apply cs_eta | apply cs_core]; assumption.
  - destruct (psteps_epsteps_commute _ _ Hxz _ Hxy)
      as [w [Hzw Hyw]].
    exists w. split; [apply cs_core | apply cs_eta]; assumption.
  - pose proof (diamond_rtc_confluent _ epstep epstep_diamond) as Heta.
    destruct (Heta x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w. split; apply cs_eta; assumption.
Qed.

Lemma cstep_confluent : confluent cstep.
Proof. apply diamond_rtc_confluent, cstep_diamond. Qed.

Lemma pstep_cstep : forall t u, pstep t u -> cstep t u.
Proof. intros t u H. apply cs_core, rtc_one, H. Qed.

Lemma epstep_cstep : forall t u, epstep t u -> cstep t u.
Proof. intros t u H. apply cs_eta, rtc_one, H. Qed.


Lemma csteps_reductions : forall t u, rtc cstep t u -> rtc reduction t u.
Proof.
  intros t u H; induction H; [apply rtc_refl|].
  eapply rtc_trans; [|exact IHrtc]. destruct H; induction H;
    eauto using rtc_refl, rtc_trans, pstep_reductions, epstep_reductions.
Qed.

Lemma reduction_parallel : forall t u, reduction t u -> pstep t u \/ epstep t u.
Proof.
  intros t u H; induction H.
  { left. now apply root_pstep. }
  { right. apply eps_eta, epstep_refl. }
  all: destruct IHreduction;
    [left; constructor; auto using pstep_refl|right; constructor; auto using epstep_refl].
Qed.
Lemma red_star_cstep : forall t u, rtc reduction t u -> rtc cstep t u.
Proof.
  intros t u H; induction H; [apply rtc_refl|].
  eapply rtc_step; [|exact IHrtc].
  destruct (reduction_parallel _ _ H); auto using pstep_cstep, epstep_cstep.
Qed.
Theorem reduction_confluent : confluent reduction.
Proof.
  intros t u v Hu Hv.
  destruct (cstep_confluent t u v (red_star_cstep _ _ Hu) (red_star_cstep _ _ Hv))
    as [w [Huw Hvw]].
  exists w; split; now apply csteps_reductions.
Qed.
Lemma reduction_compatible : forall t u,
  compatible (rtc reduction) t u -> rtc reduction t u.
Proof. intros t u H; destruct H; red_star_congr. Qed.
Theorem conversion_joinable : forall t u, conv t u ->
  exists w, rtc reduction t w /\ rtc reduction u w.
Proof.
  fix IH 3. intros t u H; destruct H.
  - exists u; split; [apply pstep_reductions, step_pstep;assumption|apply rtc_refl].
  - exists t; split; apply rtc_refl.
  - destruct (IH _ _ H) as [w [Htw Huw]]; exists w; auto.
  - destruct (IH _ _ H) as [w [Htw Huw]].
    destruct (IH _ _ H0) as [w' [Huw' Hvw']].
    destruct (reduction_confluent _ _ _ Huw Huw') as [z [Hwz Hw'z]].
    exists z; split; eapply rtc_trans; eassumption.
  - exists f; split; [apply rtc_one, red_eta|apply rtc_refl].
  - assert (Hw : exists w, compatible (rtc reduction) t w /\ compatible (rtc reduction) u w).
    { match goal with H : compatible _ _ _ |- _ => destruct H end;
      repeat match goal with H : conv ?a ?b |- _ =>
        let w := fresh "w" in let Ha := fresh "Ha" in let Hb := fresh "Hb" in
        destruct (IH a b H) as [w [Ha Hb]]; clear H end;
      eexists; split; constructor; eassumption. }
    destruct Hw as [w [Htw Huw]]. exists w; split; now apply reduction_compatible.
Qed.
