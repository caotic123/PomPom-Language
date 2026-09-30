(* Function variance is proved by a bound on comparison depth. Substitution
   may enlarge terms, but it preserves this bound. *)
From Stdlib Require Import Arith Lia.
Require Export nameless.DBSemanticJudgments.
Import Full.

Inductive bounded_universe_le : nat -> term -> term -> Prop :=
| bu_refl : forall n A, bounded_universe_le n A A
| bu_sort : forall n j k, j <= k -> bounded_universe_le n (TSort j) (TSort k)
| bu_pi : forall n A B C D,
    bounded_universe_le n C A -> bounded_universe_le n B D ->
    bounded_universe_le (S n) (TPi A B) (TPi C D).
Lemma bounded_universe_mono : forall n A B, bounded_universe_le n A B ->
  forall m, n <= m -> bounded_universe_le m A B.
Proof.
  intros n A B H; induction H; intros m Hnm; [constructor|now constructor|].
  destruct m; [lia|constructor; [apply IHbounded_universe_le1|apply IHbounded_universe_le2]; lia].
Qed.
Lemma universe_le_bounded : forall A B, universe_le A B -> exists n, bounded_universe_le n A B.
Proof.
  intros A B H; induction H.
  - exists 0; constructor.
  - exists 0; now constructor.
  - destruct IHuniverse_le1 as [n Hn], IHuniverse_le2 as [m Hm].
    exists (S (Nat.max n m)); constructor; eapply bounded_universe_mono;
      [exact Hn|apply Nat.le_max_l|exact Hm|apply Nat.le_max_r].
Qed.
Lemma bounded_universe_subst : forall n A B, bounded_universe_le n A B -> forall a c,
  bounded_universe_le n (subst a c A) (subst a c B).
Proof. intros n A B H; induction H; intros a c; cbn [subst]; constructor; auto. Qed.
Lemma bounded_universe_step_match : forall n A B, bounded_universe_le n A B ->
  (forall A', reduction A A' -> exists B', reduction B B' /\ bounded_universe_le n A' B') /\
  (forall B', reduction B B' -> exists A', reduction A A' /\ bounded_universe_le n A' B').
Proof.
  intros n A B H; induction H.
  - split; intros t HR; exists t; split; [exact HR|constructor|exact HR|constructor].
  - split; intros t HR; inversion HR; discriminate.
  - destruct IHbounded_universe_le1 as [HCA HAC], IHbounded_universe_le2 as [HBD HDB].
    split; intros t HR; inversion HR; subst; try discriminate.
    + match goal with H : reduction A ?A' |- _ => destruct (HAC A' H) as [C' [HC HL]] end.
      exists (TPi C' D); split; [now apply red_TPi_A|now constructor].
    + match goal with H : reduction B ?B' |- _ => destruct (HBD B' H) as [D' [HD HL]] end.
      exists (TPi C D'); split; [now apply red_TPi_B|now constructor].
    + match goal with H : reduction C ?C' |- _ => destruct (HCA C' H) as [AA [HA HL]] end.
      exists (TPi AA B); split; [now apply red_TPi_A|now constructor].
    + match goal with H : reduction D ?D' |- _ => destruct (HDB D' H) as [BB [HB HL]] end.
      exists (TPi A BB); split; [now apply red_TPi_B|now constructor].
Qed.
Lemma bounded_universe_reductions_match : forall A A', rtc reduction A A' -> forall n B,
  bounded_universe_le n A B -> exists B', rtc reduction B B' /\ bounded_universe_le n A' B'.
Proof.
  intros A A' HR; induction HR; intros n B HB; [exists B; split; [constructor|exact HB]|].
  destruct (proj1 (bounded_universe_step_match _ _ _ HB) _ H) as [B1 [H1 HB1]].
  destruct (IHHR n B1 HB1) as [B2 [H2 HB2]]; exists B2; split; [eapply rtc_step; eassumption|exact HB2].
Qed.
Lemma bounded_universe_normal : forall n A B,
  bounded_universe_le n A B -> normal_form A -> normal_form B.
Proof.
  intros n A B HB HN t HR; destruct (proj2 (bounded_universe_step_match _ _ _ HB) _ HR) as [u [HU _]].
  exact (HN u HU).
Qed.
Lemma calculus_normal_pi_components : forall n A B R,
  calculus_interp n (TPi A B) R -> normal_form (TPi A B) ->
  exists RA RB, calculus_interp n A RA /\ predicate_equiv R (dependent_function RA RB) /\
  (forall a, RA a -> calculus_interp n (subst a 0 B) (RB a)).
Proof.
  intros n A B R HT HN.
  destruct (type_interp_pi_normal_view _ ltac:(apply level_atom_not_pi; exact primitive_not_pi)
    _ _ HT A B eq_refl) as (RA & RB & V & HA & HE & HV & HB).
  assert (HNsub : normal_form B) by (intros t HR; apply (HN (TPi A t)); now apply red_TPi_B).
  pose proof (normal_reductions_identity _ _ HNsub HV); subst V.
  exists RA,RB; auto.
Qed.

Theorem bounded_universe_semantics : forall h A B,
  bounded_universe_le h A B -> forall n m R S,
  calculus_interp n A R -> calculus_interp m B S -> forall t, R t -> S t.
Proof.
  intros h; induction h using lt_wf_ind; intros A B HAB n m R S HA HB t Ht.
  destruct (normalize_full A (type_interp_normalizing _ _ _ HA)) as [AN [RA HNA]].
  destruct (bounded_universe_reductions_match _ _ RA _ _ HAB) as [BN [RB HNAB]].
  pose proof (bounded_universe_normal _ _ _ HNAB HNA) as HNB.
  pose proof (type_interp_reductions _ _ _ HA _ RA) as HAN.
  pose proof (type_interp_reductions _ _ _ HB _ RB) as HBN.
  clear HA HB HAB RA RB A B.
  inversion HNAB; subst.
  - apply (calculus_interp_unique _ _ _ _ _ _ HAN HBN (cv_refl _)); exact Ht.
  - pose proof (proj2 (calculus_sort_view _ _ _ _ HAN (cv_refl _))) as HEA.
    pose proof (proj2 (calculus_sort_view _ _ _ _ HBN (cv_refl _))) as HEB.
    apply HEB; eapply calculus_type_cumulative; [eassumption|apply HEA; exact Ht].
  - destruct (calculus_normal_pi_components _ _ _ _ HAN HNA) as (RA & RBB & HRA & HERA & HRBB).
    destruct (calculus_normal_pi_components _ _ _ _ HBN HNB) as (RC & RDD & HRC & HERC & HRDD).
    apply HERC; eapply dependent_function_variance; [| |apply HERA; exact Ht].
    + intros a Ha; eapply (H n0 ltac:(lia)); [exact H0|exact HRC|exact HRA|exact Ha].
    + intros a v Ha HaB.
      assert (HaA : RA a) by (eapply (H n0 ltac:(lia)); [exact H0|exact HRC|exact HRA|exact Ha]).
      eapply (H n0 ltac:(lia)); [apply bounded_universe_subst; exact H1|exact (HRBB a HaA)|exact (HRDD a Ha)|exact HaB].
Qed.
Theorem universe_le_semantics : forall A B, universe_le A B -> forall n m R S,
  calculus_interp n A R -> calculus_interp m B S -> forall t, R t -> S t.
Proof.
  intros A B H; destruct (universe_le_bounded _ _ H) as [h Hh].
  exact (bounded_universe_semantics h A B Hh).
Qed.
Theorem semantic_function_cumulative : forall f A B,
  semantic_value f A -> semantic_type B -> universe_le A B -> semantic_value f B.
Proof.
  intros f A B [n [R [HA Hf]]] [m [S HB]] HC; exists m,S; split; [exact HB|].
  eapply universe_le_semantics; eassumption.
Qed.

Print Assumptions universe_le_semantics.
Print Assumptions semantic_function_cumulative.
