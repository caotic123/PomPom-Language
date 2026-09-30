(* GLM worker 3 — pstep/mueq commuting diagram, conditional on the beta      *)
(* substitution fact.  Part 1: unconditional infrastructure.                 *)
(*                                                                           *)
(*   1. mueq shape inversions for the rigid heads that the root pstep        *)
(*      contractions pin down (TLam, TPair, TConsE, TIn, TIVar, TESucc,      *)
(*      TIPi/TIProd/TISig/TIChoice, and the constants TNilE/TEZero/TI1/      *)
(*      TUnit); mueq is shape-directed, so each inversion is by direct       *)
(*      structural case analysis with no premises.                           *)
(*   2. mueq_enum_pos_glm : mueq preserves enum_pos (TEZero=0, TESucc=S n),  *)
(*      needed to transport the ps_case_red side conditions to the mueq      *)
(*      partner unconditionally.                                             *)
(*   3. rtc_pbranches_case_glm / rtc_pstep_case_cong_glm : lifting rtc       *)
(*      pbranches through TCase and a combined TCase congruence used by the  *)
(*      ps_case simulation case.                                             *)
(*                                                                           *)
(* No Axiom / Conjecture / Admitted; everything here is closed.              *)

Require Import Progress.
Require Import _luna_mueq _glm_mueq_sim_lift _luna_pstep_rtc.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. mueq shape inversions (all unconditional)                              *)
(* ========================================================================== *)

Lemma mueq_lam_inv_glm : forall b u,
    mueq (TLam b) u -> exists b', u = TLam b' /\ mueq b b'.
Proof. intros b u H. inversion H; subst. eexists. split; [reflexivity | eassumption]. Qed.

Lemma mueq_pair_inv_glm : forall a b u,
    mueq (TPair a b) u ->
    exists a' b', u = TPair a' b' /\ mueq a a' /\ mueq b b'.
Proof.
  intros a b u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_conse_inv_glm : forall t E u,
    mueq (TConsE t E) u ->
    exists t' E', u = TConsE t' E' /\ mueq t t' /\ mueq E E'.
Proof.
  intros t E u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_in_inv_glm : forall x u,
    mueq (TIn x) u -> exists x', u = TIn x' /\ mueq x x'.
Proof. intros x u H. inversion H; subst. eexists. split; [reflexivity | eassumption]. Qed.

Lemma mueq_ivar_inv_glm : forall i u,
    mueq (TIVar i) u -> exists i', u = TIVar i' /\ mueq i i'.
Proof. intros i u H. inversion H; subst. eexists. split; [reflexivity | eassumption]. Qed.

Lemma mueq_esucc_inv_glm : forall n u,
    mueq (TESucc n) u -> exists n', u = TESucc n' /\ mueq n n'.
Proof. intros n u H. inversion H; subst. eexists. split; [reflexivity | eassumption]. Qed.

Lemma mueq_iprod_inv_glm : forall A B u,
    mueq (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ mueq A A' /\ mueq B B'.
Proof.
  intros A B u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_ipi_inv_glm : forall S T u,
    mueq (TIPi S T) u ->
    exists S' T', u = TIPi S' T' /\ mueq S S' /\ mueq T T'.
Proof.
  intros S T u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_isig_inv_glm : forall S T u,
    mueq (TISig S T) u ->
    exists S' T', u = TISig S' T' /\ mueq S S' /\ mueq T T'.
Proof.
  intros S T u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_ichoice_inv_glm : forall E T u,
    mueq (TIChoice E T) u ->
    exists E' T', u = TIChoice E' T' /\ mueq E E' /\ mueq T T'.
Proof.
  intros E T u H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; eassumption].
Qed.

Lemma mueq_nile_inv_glm : forall u, mueq TNilE u -> u = TNilE.
Proof. intros u H. inversion H; subst. reflexivity. Qed.

Lemma mueq_ezero_inv_glm : forall u, mueq TEZero u -> u = TEZero.
Proof. intros u H. inversion H; subst. reflexivity. Qed.

Lemma mueq_i1_inv_glm : forall u, mueq TI1 u -> u = TI1.
Proof. intros u H. inversion H; subst. reflexivity. Qed.

Lemma mueq_unit_inv_glm : forall u, mueq TUnit u -> u = TUnit.
Proof. intros u H. inversion H; subst. reflexivity. Qed.

(* ========================================================================== *)
(*  2. mueq preserves enum_pos                                                *)
(* ========================================================================== *)

Lemma mueq_enum_pos_glm : forall c u n, mueq c u -> enum_pos c n -> enum_pos u n.
Proof.
  intros c u n Hm He. revert u Hm.
  induction He as [c n | c n He IH]; intros u Hm.
  - (* pos_zero: c = TEZero *)
    inversion Hm; subst. constructor.
  - (* pos_succ: c = TESucc c0 *)
    inversion Hm; subst. constructor. eapply IH; eassumption.
Qed.

(* ========================================================================== *)
(*  3. rtc lifting through TCase                                              *)
(* ========================================================================== *)

(* A rtc pbranches sequence lifts pointwise through TCase with fixed M, Q
   (each pbranches step is a ps_case with reflexive pstep M, Q). *)
Lemma rtc_pbranches_case_glm : forall bs bs' M Q,
    rtc pbranches bs bs' -> rtc pstep (TCase M Q bs) (TCase M Q bs').
Proof.
  intros bs bs' M Q H.
  eapply (rtc_map_rel_pstep (list (term * term)) term pbranches pstep
            (fun xs => TCase M Q xs)); [| exact H].
  intros x y Hxy. eapply ps_case;
    [apply pstep_refl | apply pstep_refl | exact Hxy].
Qed.

(* Combined TCase congruence: M, Q by rtc pstep and the branch list by
   rtc pbranches simultaneously (used by the ps_case simulation case). *)
Lemma rtc_pstep_case_cong_glm : forall M M' Q Q' bs bs',
    rtc pstep M M' -> rtc pstep Q Q' -> rtc pbranches bs bs' ->
    rtc pstep (TCase M Q bs) (TCase M' Q' bs').
Proof.
  intros M M' Q Q' bs bs' HM HQ Hbs.
  eapply rtc_trans.
  - eapply (rtc_map_rel_pstep term term pstep pstep (fun m => TCase m Q bs));
      [| exact HM].
    intros x y Hxy. eapply ps_case;
      [exact Hxy | apply pstep_refl | apply pbranches_refl].
  - eapply rtc_trans.
    + eapply (rtc_map_rel_pstep term term pstep pstep (fun q => TCase M' q bs));
        [| exact HQ].
      intros x y Hxy. eapply ps_case;
        [apply pstep_refl | exact Hxy | apply pbranches_refl].
    + eapply (rtc_map_rel_pstep (list (term * term)) term pbranches pstep
                (fun xs => TCase M' Q' xs)); [| exact Hbs].
      intros x y Hxy. eapply ps_case;
        [apply pstep_refl | apply pstep_refl | exact Hxy].
Qed.

(* ========================================================================== *)
(*  4. Closedness certificates                                                *)
(* ========================================================================== *)

Print Assumptions mueq_lam_inv_glm.
Print Assumptions mueq_pair_inv_glm.
Print Assumptions mueq_conse_inv_glm.
Print Assumptions mueq_in_inv_glm.
Print Assumptions mueq_ivar_inv_glm.
Print Assumptions mueq_esucc_inv_glm.
Print Assumptions mueq_iprod_inv_glm.
Print Assumptions mueq_ipi_inv_glm.
Print Assumptions mueq_isig_inv_glm.
Print Assumptions mueq_ichoice_inv_glm.
Print Assumptions mueq_nile_inv_glm.
Print Assumptions mueq_ezero_inv_glm.
Print Assumptions mueq_i1_inv_glm.
Print Assumptions mueq_unit_inv_glm.
Print Assumptions mueq_enum_pos_glm.
Print Assumptions rtc_pbranches_case_glm.
Print Assumptions rtc_pstep_case_cong_glm.
