Require Import Progress.

Lemma rtc_R_single_S_commute : forall (A : Type) (R S : A -> A -> Prop),
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  forall x y z, rtc R x y -> S x z ->
    exists w, S y w /\ rtc R z w.
Proof.
  intros A R S H x y z Hxy. revert z. induction Hxy as [x|x y' y Hxy Hyy' IH]; intros z Hz.
  - exists z. split; [exact Hz|apply rtc_refl].
  - destruct (H _ _ _ Hxy Hz) as [w [Hyw Hzw]].
    destruct (IH w Hyw) as [q [Hyq Hzq]].
    exists q. split; [exact Hyq|eapply rtc_trans; eassumption].
Qed.

Lemma rtc_R_S_commute : forall (A : Type) (R S : A -> A -> Prop),
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  forall x y z, rtc R x y -> rtc S x z ->
    exists w, rtc S y w /\ rtc R z w.
Proof.
  intros A R S H x y z Hxy Hxz. revert Hxy. revert y.
  induction Hxz as [x|x z' z Hxz Hzz' IH]; intros y Hxy.
  - exists y. split; [apply rtc_refl|exact Hxy].
  - destruct (rtc_R_single_S_commute A R S H _ _ _ Hxy Hxz)
      as [q [Hyq Hzq]].
    destruct (IH q Hzq) as [w [Hqw Hzw]].
    exists w. split; [eapply rtc_trans; [apply rtc_one; exact Hyq|exact Hqw]|exact Hzw].
Qed.

Inductive block_union (A : Type) (R S : A -> A -> Prop) : A -> A -> Prop :=
| bu_left : forall x y, rtc R x y -> block_union A R S x y
| bu_right : forall x y, rtc S x y -> block_union A R S x y.

Lemma block_union_diamond : forall (A : Type) (R S : A -> A -> Prop),
  confluent R -> confluent S ->
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  diamond (block_union A R S).
Proof.
  intros A R S HR HS Hcomm x y z Hxy Hxz.
  destruct Hxy as [x y Hxy|x y Hxy]; destruct Hxz as [x z Hxz|x z Hxz].
  - destruct (HR x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w; split; [apply bu_left|apply bu_left]; assumption.
  - destruct (rtc_R_S_commute A R S Hcomm _ _ _ Hxy Hxz)
      as [w [Hyw Hzw]].
    exists w; split; [apply bu_right|apply bu_left]; assumption.
  - destruct (rtc_R_S_commute A R S Hcomm _ _ _ Hxz Hxy)
      as [w [Hzw Hyw]].
    exists w; split; [apply bu_left|apply bu_right]; assumption.
  - destruct (HS x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w; split; [apply bu_right|apply bu_right]; assumption.
Qed.

Lemma block_union_confluent : forall (A : Type) (R S : A -> A -> Prop),
  confluent R -> confluent S ->
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  confluent (block_union A R S).
Proof.
  intros; apply diamond_rtc_confluent, block_union_diamond; assumption.
Qed.

Print Assumptions rtc_R_single_S_commute.
Print Assumptions rtc_R_S_commute.
Print Assumptions block_union_diamond.
Print Assumptions block_union_confluent.
