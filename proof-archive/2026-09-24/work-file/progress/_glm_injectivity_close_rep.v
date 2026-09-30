(* GLM worker 3 — conditional closing layer for exact EnumT / Pi conversion  *)
(* injectivity, part 1: representations, bridges, simulation, transport.     *)
(*                                                                           *)
(* Arbitrary qconv intermediates need not retain a stable syntactic head     *)
(* (top-level beta expansions exist), so the endpoints are represented       *)
(* honestly by                                                               *)
(*                                                                           *)
(*   enumt_rep t E := cjoin t (TEnumT E)                                     *)
(*   pi_rep    t A B := cjoin t (TPi A B)                                    *)
(*                                                                           *)
(* and carried along the qconv chain.  cjoin is an equivalence (cjoin_refl,  *)
(* _sym, _trans via cstep confluence), so transport across a cjoin link is   *)
(* free; transport across a mueq link is the genuinely missing               *)
(* modulo-simulation interface.  IMPORTANT: structural mueq may change the   *)
(* EnumT/Pi components, so the honest interface lets the component move,     *)
(* accumulating a qconv on the component itself:                             *)
(*                                                                           *)
(*   mueq_enumt_sim_components : forall t u E, mueq t u -> enumt_rep t E ->  *)
(*       exists E', enumt_rep u E' /\ qconv E E'.                            *)
(*   mueq_pi_sim_components : forall t u A B, mueq t u -> pi_rep t A B ->    *)
(*       exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.           *)
(*                                                                           *)
(* The transport lemmas below accumulate these component qconvs with         *)
(* qconv_trans along the whole chain.  The earlier fixed-component premises  *)
(* mueq_enumt_sim / mueq_pi_sim are retained as strict special cases         *)
(* (mueq_enumt_sim_subset / mueq_pi_sim_subset).                             *)
(* (only the mueq half of qlink is assumed; the cjoin half is derived).      *)
(* This part also supplies the conv bridges: epstep_conv, cstep_conv,        *)
(* cjoin_conv, qlink_conv, qconv_conv, and the stable-endpoint EnumT         *)
(* cancellation (the Pi cancellation is cjoin_pi_inv of                      *)
(* _work_cstep_invariants).                                                  *)

Require Import Progress.
Require Import _tmp_epstep _work_mixed_closure _work_cjoin
               _work_cstep_invariants
               _luna_mueq
               _glm_qconv_def _glm_qconv_main.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. conv bridges: cjoin (hence qlink, qconv) re-enters conv                *)
(* ========================================================================== *)

(* Mutual embedding of parallel eta reduction into conv.  The epbranches      *)
(* statement is generalized over a branch prefix so cv_case_br can act on     *)
(* the first differing cell (same shape as the mueq_conv_mut argument of      *)
(* _luna_mueq); the mutuality supplies conv c c' / conv b b' to cv_case_br.   *)
Lemma epstep_conv_mut :
    (forall t u, epstep t u -> conv t u) /\
    (forall bs bs', epbranches bs bs' -> forall pre M Q,
        conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply epstep_epbranches_ind; intros;
    try solve [eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma,
      cv_pair, cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi,
      cv_switch, cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
      cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
      cv_list, cv_lnil, cv_lcons].
  - (* eps_case : branches first (empty prefix), then head/motive *)
    eapply cv_trans.
    + apply (H1 [] M Q).
    + apply cv_case; [exact H | exact H0].
  - (* eps_eta : compose cv_eta with the induction hypothesis *)
    eapply cv_trans; [apply cv_eta | assumption].
  - (* epbs_cons : replace the first cell with cv_case_br, then the tail *)
    eapply cv_trans.
    + apply cv_case_br; [exact H | exact H0].
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma epstep_conv : forall t u, epstep t u -> conv t u.
Proof. exact (proj1 epstep_conv_mut). Qed.

Lemma epbranches_case_conv : forall bs bs',
    epbranches bs bs' -> forall M Q,
      conv (TCase M Q bs) (TCase M Q bs').
Proof.
  intros bs bs' H M Q.
  exact (proj2 epstep_conv_mut bs bs' H [] M Q).
Qed.

Lemma rtc_pstep_conv : forall t u, rtc pstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply pstep_conv, H | exact IHrtc].
Qed.

Lemma rtc_epstep_conv : forall t u, rtc epstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply epstep_conv, H | exact IHrtc].
Qed.

Lemma cstep_conv : forall t u, cstep t u -> conv t u.
Proof.
  intros t u H. destruct H.
  - apply rtc_pstep_conv, H.
  - apply rtc_epstep_conv, H.
Qed.

Lemma rtc_cstep_conv : forall t u, rtc cstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply cstep_conv, H | exact IHrtc].
Qed.

Lemma cjoin_conv : forall t u, cjoin t u -> conv t u.
Proof.
  intros t u [w [Htw Huw]].
  eapply cv_trans;
    [apply rtc_cstep_conv, Htw | apply cv_sym, rtc_cstep_conv, Huw].
Qed.

Lemma qlink_conv : forall t u, qlink t u -> conv t u.
Proof.
  intros t u [H | H].
  - apply cjoin_conv, H.
  - apply mueq_conv, H.
Qed.

Lemma qconv_conv : forall t u, qconv t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply qlink_conv, H | exact IHrtc].
Qed.

(* ========================================================================== *)
(*  2. Honest representation predicates and the simulation interface          *)
(* ========================================================================== *)

Definition enumt_rep (t E : term) : Prop := cjoin t (TEnumT E).

Definition pi_rep (t A B : term) : Prop := cjoin t (TPi A B).

(* The minimal simulation compatibility: one mueq link transports a          *)
(* representation.  This is exactly the modulo-simulation interface that the  *)
(* mueq simulation work would discharge; everything below is conditional on   *)
(* it (quantified premise, so the theorems stay axiom-free).                  *)
Definition mueq_enumt_sim : Prop :=
  forall t u E, mueq t u -> enumt_rep t E -> enumt_rep u E.

Definition mueq_pi_sim : Prop :=
  forall t u A B, mueq t u -> pi_rep t A B -> pi_rep u A B.

(* --- the honest component-changing interface ------------------------------ *)

(* Structural mueq may change EnumT/Pi components; the simulation only has   *)
(* to preserve representability and relate the old component to the new one  *)
(* by qconv.  This is the premise the new consumers use.                     *)
Definition mueq_enumt_sim_components : Prop :=
  forall t u E, mueq t u -> enumt_rep t E ->
    exists E', enumt_rep u E' /\ qconv E E'.

Definition mueq_pi_sim_components : Prop :=
  forall t u A B, mueq t u -> pi_rep t A B ->
    exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.

(* The fixed-component premises are strict special cases of the honest ones. *)
Lemma mueq_enumt_sim_subset : mueq_enumt_sim -> mueq_enumt_sim_components.
Proof.
  intros SIM t u E H Hrep.
  exists E. split; [exact (SIM t u E H Hrep) | apply qconv_refl].
Qed.

Lemma mueq_pi_sim_subset : mueq_pi_sim -> mueq_pi_sim_components.
Proof.
  intros SIM t u A B H Hrep.
  exists A, B. split; [exact (SIM t u A B H Hrep) | split; apply qconv_refl].
Qed.

(* --- step 1: transport across ONE qlink, accumulating component qconv ----- *)

(* the cjoin half is pure cjoin algebra (component unchanged, qconv_refl);   *)
(* the mueq half is the honest component-changing premise.                   *)
Lemma enumt_rep_qlink_components : mueq_enumt_sim_components ->
    forall t u E, qlink t u -> enumt_rep t E ->
      exists E', enumt_rep u E' /\ qconv E E'.
Proof.
  intros SIM t u E [H | H] Hrep.
  - (* cjoin : cjoin u t and cjoin t (TEnumT E) compose; component stable *)
    exists E. split.
    + apply cjoin_trans with (u := t);
        [apply cjoin_sym, H | exact Hrep].
    + apply qconv_refl.
  - (* mueq : the component-changing simulation compatibility *)
    exact (SIM t u E H Hrep).
Qed.

Lemma pi_rep_qlink_components : mueq_pi_sim_components ->
    forall t u A B, qlink t u -> pi_rep t A B ->
      exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.
Proof.
  intros SIM t u A B [H | H] Hrep.
  - exists A, B. split.
    + apply cjoin_trans with (u := t);
        [apply cjoin_sym, H | exact Hrep].
    + split; apply qconv_refl.
  - exact (SIM t u A B H Hrep).
Qed.

(* --- step 2: transport across rtc qconv, accumulating component qconv ----- *)

(* The component is existentially chosen at every link; the accumulated      *)
(* qconv is composed with qconv_trans.                                       *)
Lemma enumt_rep_qconv_components : mueq_enumt_sim_components ->
    forall t u, qconv t u -> forall E, enumt_rep t E ->
      exists E', enumt_rep u E' /\ qconv E E'.
Proof.
  intros SIM t u H.
  induction H as [x | x y z Hxy Hyz IH]; intros E Hrep.
  - exists E. split; [exact Hrep | apply qconv_refl].
  - destruct (enumt_rep_qlink_components SIM x y E Hxy Hrep)
      as [Emid [Hrepmid HqE]].
    destruct (IH Emid Hrepmid) as [E' [Hrep' HqE']].
    exists E'. split; [exact Hrep' | eapply qconv_trans; eassumption].
Qed.

Lemma pi_rep_qconv_components : mueq_pi_sim_components ->
    forall t u, qconv t u -> forall A B, pi_rep t A B ->
      exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.
Proof.
  intros SIM t u H.
  induction H as [x | x y z Hxy Hyz IH]; intros A B Hrep.
  - exists A, B. split; [exact Hrep | split; apply qconv_refl].
  - destruct (pi_rep_qlink_components SIM x y A B Hxy Hrep)
      as [Amid [Bmid [Hrepmid [HqA HqB]]]].
    destruct (IH Amid Bmid Hrepmid) as [A' [B' [Hrep' [HqA' HqB']]]].
    exists A', B'. split; [exact Hrep' | split].
    + eapply qconv_trans; eassumption.
    + eapply qconv_trans; eassumption.
Qed.

(* --- step 1 (SPECIAL CASE: fixed component, generally unprovable) --------- *)

(* These lemmas assume the component survives every mueq link unchanged;     *)
(* structural mueq may change EnumT/Pi components, so they only hold for     *)
(* the restricted premise above.  The component-changing versions are the    *)
(* enumt_rep_qlink_components / pi_rep_qlink_components of section 2.        *)
(* the cjoin half is pure cjoin algebra; the mueq half is the premise *)
Lemma enumt_rep_qlink : mueq_enumt_sim -> forall t u E,
    qlink t u -> enumt_rep t E -> enumt_rep u E.
Proof.
  intros SIM t u E [H | H] Hrep.
  - (* cjoin : cjoin u t and cjoin t (TEnumT E) compose *)
    apply cjoin_trans with (u := t);
      [apply cjoin_sym, H | exact Hrep].
  - (* mueq : the simulation compatibility *)
    exact (SIM t u E H Hrep).
Qed.

Lemma pi_rep_qlink : mueq_pi_sim -> forall t u A B,
    qlink t u -> pi_rep t A B -> pi_rep u A B.
Proof.
  intros SIM t u A B [H | H] Hrep.
  - apply cjoin_trans with (u := t);
      [apply cjoin_sym, H | exact Hrep].
  - exact (SIM t u A B H Hrep).
Qed.

(* --- step 2 (SPECIAL CASE: fixed component, generally unprovable) --------- *)

Lemma enumt_rep_qconv : mueq_enumt_sim -> forall t u E,
    qconv t u -> enumt_rep t E -> enumt_rep u E.
Proof.
  intros SIM t u E H.
  induction H as [x | x y z Hxy Hyz IH]; intros Hrep.
  - exact Hrep.
  - apply IH. exact (enumt_rep_qlink SIM x y E Hxy Hrep).
Qed.

Lemma pi_rep_qconv : mueq_pi_sim -> forall t u A B,
    qconv t u -> pi_rep t A B -> pi_rep u A B.
Proof.
  intros SIM t u A B H.
  induction H as [x | x y z Hxy Hyz IH]; intros Hrep.
  - exact Hrep.
  - apply IH. exact (pi_rep_qlink SIM x y A B Hxy Hrep).
Qed.

(* ========================================================================== *)
(*  3. Stable-endpoint cancellation                                           *)
(* ========================================================================== *)

(* cstep cannot leave the TEnumT head, so a join of two syntactic TEnumT      *)
(* endpoints joins at a common TEnumT witness and the components join.        *)
Lemma cjoin_enumt_inv_glm : forall E1 E2,
    cjoin (TEnumT E1) (TEnumT E2) -> cjoin E1 E2.
Proof.
  intros E1 E2 [w [H1 H2]].
  destruct (rtc_cstep_enumt_inv _ _ H1) as [E1' [Hw1 HE1]].
  destruct (rtc_cstep_enumt_inv _ _ H2) as [E2' [Hw2 HE2]].
  rewrite Hw1 in Hw2. inversion Hw2. subst E2'.
  exists E1'. split; [exact HE1 | exact HE2].
Qed.

(* The Pi counterpart is cjoin_pi_inv of _work_cstep_invariants.              *)
