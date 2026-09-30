(* _parent_phi_erase_eta_congr_sort.v — non-eta congruence backward with sort endpoint.
   SLOW SAFE strategy: Show after EVERY tactic, case-by-case, until Qed.
   Covers RIGID congruence heads via vacuity (closed conv_whd / mus-unit-pair-epi
   nonsort / preservation helpers) and excludes non-rigid App/Lam/Fst/Snd/Switch/
   Interp/Ind/IAll/Hyps/Case + eta-top via disequality premises (need endpoint
   reflection, future). No admits, closed. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep _work_conv_whd_pos
  _parent_mus_cstep_inv _parent_inert_cstep_inv _parent_epi_nonsort
  _parent_phi_erase_sort_hshape _glm_phi_erase_pstep_reflect_shapes
  _parent_phi_erase_epstep_forward _parent_phi_erase_sort_algebra
  _parent_phi_erase_idem _tmp_pstep_var_rigid.
From Stdlib Require Import List Lia PeanoNat String.
Import ListNotations TypeRules.

(* --- preservation helpers: nullary (equality) --- *)

Lemma rtc_pstep_tag_id_glm : forall s u, pstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_epstep_tag_id_glm : forall s u, epstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_pstep_tag_rtc_glm : forall s u, rtc pstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  remember (TTag s) as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_pstep_tag_id_glm s y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_epstep_tag_rtc_glm : forall s u, rtc epstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  remember (TTag s) as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_epstep_tag_id_glm s y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma cstep_tag_id_glm : forall s u, cstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    eapply rtc_pstep_tag_rtc_glm. Show.
    exact Hpu. Show.
  - Show.
    eapply rtc_epstep_tag_rtc_glm. Show.
    exact Heu. Show.
Qed.

Lemma rtc_cstep_tag_id_glm : forall s u, rtc cstep (TTag s) u -> u = TTag s.
Proof.
  intros s u H. Show.
  remember (TTag s) as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (cstep_tag_id_glm s y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_tag_not_sort_glm : forall s j, ~ rtc cstep (TTag s) (TSort j).
Proof.
  intros s j H. Show.
  pose proof (rtc_cstep_tag_id_glm s (TSort j) H) as Heq. Show.
  discriminate Heq. Show.
Qed.

Lemma rtc_pstep_ezero_id_glm : forall u, pstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_epstep_ezero_id_glm : forall u, epstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_pstep_ezero_rtc_glm : forall u, rtc pstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  remember TEZero as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_pstep_ezero_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_epstep_ezero_rtc_glm : forall u, rtc epstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  remember TEZero as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_epstep_ezero_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma cstep_ezero_id_glm : forall u, cstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    eapply rtc_pstep_ezero_rtc_glm. Show.
    exact Hpu. Show.
  - Show.
    eapply rtc_epstep_ezero_rtc_glm. Show.
    exact Heu. Show.
Qed.

Lemma rtc_cstep_ezero_id_glm : forall u, rtc cstep TEZero u -> u = TEZero.
Proof.
  intros u H. Show.
  remember TEZero as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (cstep_ezero_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_ezero_not_sort_glm : forall j, ~ rtc cstep TEZero (TSort j).
Proof.
  intros j H. Show.
  pose proof (rtc_cstep_ezero_id_glm (TSort j) H) as Heq. Show.
  discriminate Heq. Show.
Qed.

Lemma rtc_pstep_i1_id_glm : forall u, pstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_epstep_i1_id_glm : forall u, epstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  inversion H; subst. Show.
  reflexivity. Show.
Qed.

Lemma rtc_pstep_i1_rtc_glm : forall u, rtc pstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  remember TI1 as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_pstep_i1_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_epstep_i1_rtc_glm : forall u, rtc epstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  remember TI1 as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (rtc_epstep_i1_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma cstep_i1_id_glm : forall u, cstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    eapply rtc_pstep_i1_rtc_glm. Show.
    exact Hpu. Show.
  - Show.
    eapply rtc_epstep_i1_rtc_glm. Show.
    exact Heu. Show.
Qed.

Lemma rtc_cstep_i1_id_glm : forall u, rtc cstep TI1 u -> u = TI1.
Proof.
  intros u H. Show.
  remember TI1 as t eqn:Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]. Show.
  - Show.
    inversion Ht; subst. Show.
    reflexivity. Show.
  - Show.
    subst x. Show.
    pose proof (cstep_i1_id_glm y Hxy) as Hy. Show.
    subst y. Show.
    eapply IH. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_i1_not_sort_glm : forall j, ~ rtc cstep TI1 (TSort j).
Proof.
  intros j H. Show.
  pose proof (rtc_cstep_i1_id_glm (TSort j) H) as Heq. Show.
  discriminate Heq. Show.
Qed.

(* --- unary preservation (existence, same head) --- *)

Lemma pstep_esucc_inv_glm : forall n u, pstep (TESucc n) u ->
  exists n', u = TESucc n' /\ pstep n n'.
Proof.
  intros n u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_pstep_esucc_inv_glm : forall n u, rtc pstep (TESucc n) u ->
  exists n', u = TESucc n' /\ rtc pstep n n'.
Proof.
  intros n u H. Show.
  remember (TESucc n) as t eqn:Ht. Show.
  revert n Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros n0 Heq; subst. Show.
  - Show.
    exists n0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_esucc_inv_glm _ _ Hxy) as [n1 [-> Hn1]]. Show.
    destruct (IH n1 eq_refl) as [n2 [-> Hn2]]. Show.
    exists n2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hn1. Show.
      * exact Hn2. Show.
Qed.

Lemma epstep_esucc_inv_glm : forall n u, epstep (TESucc n) u ->
  exists n', u = TESucc n' /\ epstep n n'.
Proof.
  intros n u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_epstep_esucc_inv_glm : forall n u, rtc epstep (TESucc n) u ->
  exists n', u = TESucc n' /\ rtc epstep n n'.
Proof.
  intros n u H. Show.
  remember (TESucc n) as t eqn:Ht. Show.
  revert n Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros n0 Heq; subst. Show.
  - Show.
    exists n0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_esucc_inv_glm _ _ Hxy) as [n1 [-> Hn1]]. Show.
    destruct (IH n1 eq_refl) as [n2 [-> Hn2]]. Show.
    exists n2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hn1. Show.
      * exact Hn2. Show.
Qed.

Lemma cstep_esucc_inv_glm : forall n u, cstep (TESucc n) u ->
  exists n', u = TESucc n'.
Proof.
  intros n u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_esucc_inv_glm _ _ Hpu) as [n' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_esucc_inv_glm _ _ Heu) as [n' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_esucc_inv_glm : forall n u, rtc cstep (TESucc n) u ->
  exists n', u = TESucc n'.
Proof.
  intros n u H. Show.
  remember (TESucc n) as t eqn:Ht. Show.
  revert n Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros n0 Heq; subst. Show.
  - Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_esucc_inv_glm _ _ Hxy) as [n1 ->]. Show.
    exact (IH n1 eq_refl). Show.
Qed.

Corollary rtc_cstep_esucc_not_sort_glm : forall n j,
  ~ rtc cstep (TESucc n) (TSort j).
Proof.
  intros n j H. Show.
  destruct (rtc_cstep_esucc_inv_glm _ _ H) as [n' Heq]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_ivar_inv_glm : forall i u, pstep (TIVar i) u ->
  exists i', u = TIVar i' /\ pstep i i'.
Proof.
  intros i u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_pstep_ivar_inv_glm : forall i u, rtc pstep (TIVar i) u ->
  exists i', u = TIVar i' /\ rtc pstep i i'.
Proof.
  intros i u H. Show.
  remember (TIVar i) as t eqn:Ht. Show.
  revert i Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros i0 Heq; subst. Show.
  - Show.
    exists i0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_ivar_inv_glm _ _ Hxy) as [i1 [-> Hi1]]. Show.
    destruct (IH i1 eq_refl) as [i2 [-> Hi2]]. Show.
    exists i2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hi1. Show.
      * exact Hi2. Show.
Qed.

Lemma epstep_ivar_inv_glm : forall i u, epstep (TIVar i) u ->
  exists i', u = TIVar i' /\ epstep i i'.
Proof.
  intros i u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_epstep_ivar_inv_glm : forall i u, rtc epstep (TIVar i) u ->
  exists i', u = TIVar i' /\ rtc epstep i i'.
Proof.
  intros i u H. Show.
  remember (TIVar i) as t eqn:Ht. Show.
  revert i Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros i0 Heq; subst. Show.
  - Show.
    exists i0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_ivar_inv_glm _ _ Hxy) as [i1 [-> Hi1]]. Show.
    destruct (IH i1 eq_refl) as [i2 [-> Hi2]]. Show.
    exists i2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hi1. Show.
      * exact Hi2. Show.
Qed.

Lemma cstep_ivar_inv_glm : forall i u, cstep (TIVar i) u ->
  exists i', u = TIVar i'.
Proof.
  intros i u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_ivar_inv_glm _ _ Hpu) as [i' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_ivar_inv_glm _ _ Heu) as [i' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_ivar_inv_glm : forall i u, rtc cstep (TIVar i) u ->
  exists i', u = TIVar i'.
Proof.
  intros i u H. Show.
  remember (TIVar i) as t eqn:Ht. Show.
  revert i Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros i0 Heq; subst. Show.
  - Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_ivar_inv_glm _ _ Hxy) as [i1 ->]. Show.
    exact (IH i1 eq_refl). Show.
Qed.

Corollary rtc_cstep_ivar_not_sort_glm : forall i j,
  ~ rtc cstep (TIVar i) (TSort j).
Proof.
  intros i j H. Show.
  destruct (rtc_cstep_ivar_inv_glm _ _ H) as [i' Heq]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_mui_inv_glm : forall R u, pstep (TMuI R) u ->
  exists R', u = TMuI R' /\ pstep R R'.
Proof.
  intros R u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_pstep_mui_inv_glm : forall R u, rtc pstep (TMuI R) u ->
  exists R', u = TMuI R' /\ rtc pstep R R'.
Proof.
  intros R u H. Show.
  remember (TMuI R) as t eqn:Ht. Show.
  revert R Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros R0 Heq; subst. Show.
  - Show.
    exists R0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_mui_inv_glm _ _ Hxy) as [R1 [-> HR1]]. Show.
    destruct (IH R1 eq_refl) as [R2 [-> HR2]]. Show.
    exists R2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HR1. Show.
      * exact HR2. Show.
Qed.

Lemma epstep_mui_inv_glm : forall R u, epstep (TMuI R) u ->
  exists R', u = TMuI R' /\ epstep R R'.
Proof.
  intros R u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_epstep_mui_inv_glm : forall R u, rtc epstep (TMuI R) u ->
  exists R', u = TMuI R' /\ rtc epstep R R'.
Proof.
  intros R u H. Show.
  remember (TMuI R) as t eqn:Ht. Show.
  revert R Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros R0 Heq; subst. Show.
  - Show.
    exists R0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_mui_inv_glm _ _ Hxy) as [R1 [-> HR1]]. Show.
    destruct (IH R1 eq_refl) as [R2 [-> HR2]]. Show.
    exists R2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HR1. Show.
      * exact HR2. Show.
Qed.

Lemma cstep_mui_inv_glm : forall R u, cstep (TMuI R) u ->
  exists R', u = TMuI R'.
Proof.
  intros R u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_mui_inv_glm _ _ Hpu) as [R' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_mui_inv_glm _ _ Heu) as [R' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_mui_inv_glm : forall R u, rtc cstep (TMuI R) u ->
  exists R', u = TMuI R'.
Proof.
  intros R u H. Show.
  remember (TMuI R) as t eqn:Ht. Show.
  revert R Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros R0 Heq; subst. Show.
  - Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_mui_inv_glm _ _ Hxy) as [R1 ->]. Show.
    exact (IH R1 eq_refl). Show.
Qed.

Corollary rtc_cstep_mui_not_sort_glm : forall R j,
  ~ rtc cstep (TMuI R) (TSort j).
Proof.
  intros R j H. Show.
  destruct (rtc_cstep_mui_inv_glm _ _ H) as [R' Heq]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_tin_inv_glm : forall x u, pstep (TIn x) u ->
  exists x', u = TIn x' /\ pstep x x'.
Proof.
  intros x u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_pstep_tin_inv_glm : forall x u, rtc pstep (TIn x) u ->
  exists x', u = TIn x' /\ rtc pstep x x'.
Proof.
  intros x u H. Show.
  remember (TIn x) as t eqn:Ht. Show.
  revert x Ht. Show.
  induction H as [a | a b c Hab Hbc IHa]; intros x0 Heq; subst. Show.
  - Show.
    exists x0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_tin_inv_glm _ _ Hab) as [x1 [-> Hx1]]. Show.
    destruct (IHa x1 eq_refl) as [x2 [-> Hx2]]. Show.
    exists x2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hx1. Show.
      * exact Hx2. Show.
Qed.

Lemma epstep_tin_inv_glm : forall x u, epstep (TIn x) u ->
  exists x', u = TIn x' /\ epstep x x'.
Proof.
  intros x u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_epstep_tin_inv_glm : forall x u, rtc epstep (TIn x) u ->
  exists x', u = TIn x' /\ rtc epstep x x'.
Proof.
  intros x u H. Show.
  remember (TIn x) as t eqn:Ht. Show.
  revert x Ht. Show.
  induction H as [a | a b c Hab Hbc IHa]; intros x0 Heq; subst. Show.
  - Show.
    exists x0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_tin_inv_glm _ _ Hab) as [x1 [-> Hx1]]. Show.
    destruct (IHa x1 eq_refl) as [x2 [-> Hx2]]. Show.
    exists x2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact Hx1. Show.
      * exact Hx2. Show.
Qed.

Lemma cstep_tin_inv_glm : forall x u, cstep (TIn x) u ->
  exists x', u = TIn x'.
Proof.
  intros x u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_tin_inv_glm _ _ Hpu) as [x' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_tin_inv_glm _ _ Heu) as [x' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_tin_inv_glm : forall x u, rtc cstep (TIn x) u ->
  exists x', u = TIn x'.
Proof.
  intros x u H. Show.
  remember (TIn x) as t eqn:Ht. Show.
  revert x Ht. Show.
  induction H as [a | a b c Hab Hbc IHa]; intros x0 Heq; subst. Show.
  - Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_tin_inv_glm _ _ Hab) as [x1 ->]. Show.
    exact (IHa x1 eq_refl). Show.
Qed.

Corollary rtc_cstep_tin_not_sort_glm : forall x j,
  ~ rtc cstep (TIn x) (TSort j).
Proof.
  intros x j H. Show.
  destruct (rtc_cstep_tin_inv_glm _ _ H) as [x' Heq]. Show.
  discriminate Heq. Show.
Qed.

(* --- binary preservation (existence, same head) --- *)

Lemma pstep_iprod_inv_glm : forall A B u, pstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B' /\ pstep A A' /\ pstep B B'.
Proof.
  intros A B u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_pstep_iprod_inv_glm : forall A B u, rtc pstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B' /\ rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. Show.
  remember (TIProd A B) as t eqn:Ht. Show.
  revert A B Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 B0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    exists B0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_iprod_inv_glm _ _ _ Hxy) as [A1 [B1 [-> [HA1 HB1]]]]. Show.
    destruct (IH A1 B1 eq_refl) as [A2 [B2 [-> [HA2 HB2]]]]. Show.
    exists A2. Show.
    exists B2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
    + eapply rtc_step. Show.
      * exact HB1. Show.
      * exact HB2. Show.
Qed.

Lemma epstep_iprod_inv_glm : forall A B u, epstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B' /\ epstep A A' /\ epstep B B'.
Proof.
  intros A B u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_epstep_iprod_inv_glm : forall A B u, rtc epstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B' /\ rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. Show.
  remember (TIProd A B) as t eqn:Ht. Show.
  revert A B Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 B0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    exists B0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_iprod_inv_glm _ _ _ Hxy) as [A1 [B1 [-> [HA1 HB1]]]]. Show.
    destruct (IH A1 B1 eq_refl) as [A2 [B2 [-> [HA2 HB2]]]]. Show.
    exists A2. Show.
    exists B2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
    + eapply rtc_step. Show.
      * exact HB1. Show.
      * exact HB2. Show.
Qed.

Lemma cstep_iprod_inv_glm : forall A B u, cstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B'.
Proof.
  intros A B u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_iprod_inv_glm _ _ _ Hpu) as [A' [B' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_iprod_inv_glm _ _ _ Heu) as [A' [B' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_iprod_inv_glm : forall A B u, rtc cstep (TIProd A B) u ->
  exists A' B', u = TIProd A' B'.
Proof.
  intros A B u H. Show.
  remember (TIProd A B) as t eqn:Ht. Show.
  revert A B Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 B0 Heq; subst. Show.
  - Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_iprod_inv_glm _ _ _ Hxy) as [A1 [B1 ->]]. Show.
    exact (IH A1 B1 eq_refl). Show.
Qed.

Corollary rtc_cstep_iprod_not_sort_glm : forall A B j,
  ~ rtc cstep (TIProd A B) (TSort j).
Proof.
  intros A B j H. Show.
  destruct (rtc_cstep_iprod_inv_glm _ _ _ H) as [A' [B' Heq]]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_ipi_inv_glm : forall S T u, pstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T' /\ pstep S S' /\ pstep T T'.
Proof.
  intros S T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_pstep_ipi_inv_glm : forall S T u, rtc pstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T' /\ rtc pstep S S' /\ rtc pstep T T'.
Proof.
  intros S T u H. Show.
  remember (TIPi S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    exists S0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_ipi_inv_glm _ _ _ Hxy) as [S1 [T1 [-> [HS1 HT1]]]]. Show.
    destruct (IH S1 T1 eq_refl) as [S2 [T2 [-> [HS2 HT2]]]]. Show.
    exists S2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HS1. Show.
      * exact HS2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma epstep_ipi_inv_glm : forall S T u, epstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T' /\ epstep S S' /\ epstep T T'.
Proof.
  intros S T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_epstep_ipi_inv_glm : forall S T u, rtc epstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T' /\ rtc epstep S S' /\ rtc epstep T T'.
Proof.
  intros S T u H. Show.
  remember (TIPi S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    exists S0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_ipi_inv_glm _ _ _ Hxy) as [S1 [T1 [-> [HS1 HT1]]]]. Show.
    destruct (IH S1 T1 eq_refl) as [S2 [T2 [-> [HS2 HT2]]]]. Show.
    exists S2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HS1. Show.
      * exact HS2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma cstep_ipi_inv_glm : forall S T u, cstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T'.
Proof.
  intros S T u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_ipi_inv_glm _ _ _ Hpu) as [S' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_ipi_inv_glm _ _ _ Heu) as [S' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_ipi_inv_glm : forall S T u, rtc cstep (TIPi S T) u ->
  exists S' T', u = TIPi S' T'.
Proof.
  intros S T u H. Show.
  remember (TIPi S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_ipi_inv_glm _ _ _ Hxy) as [S1 [T1 ->]]. Show.
    exact (IH S1 T1 eq_refl). Show.
Qed.

Corollary rtc_cstep_ipi_not_sort_glm : forall S T j,
  ~ rtc cstep (TIPi S T) (TSort j).
Proof.
  intros S T j H. Show.
  destruct (rtc_cstep_ipi_inv_glm _ _ _ H) as [S' [T' Heq]]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_isig_inv_glm : forall S T u, pstep (TISig S T) u ->
  exists S' T', u = TISig S' T' /\ pstep S S' /\ pstep T T'.
Proof.
  intros S T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_pstep_isig_inv_glm : forall S T u, rtc pstep (TISig S T) u ->
  exists S' T', u = TISig S' T' /\ rtc pstep S S' /\ rtc pstep T T'.
Proof.
  intros S T u H. Show.
  remember (TISig S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    exists S0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_isig_inv_glm _ _ _ Hxy) as [S1 [T1 [-> [HS1 HT1]]]]. Show.
    destruct (IH S1 T1 eq_refl) as [S2 [T2 [-> [HS2 HT2]]]]. Show.
    exists S2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HS1. Show.
      * exact HS2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma epstep_isig_inv_glm : forall S T u, epstep (TISig S T) u ->
  exists S' T', u = TISig S' T' /\ epstep S S' /\ epstep T T'.
Proof.
  intros S T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_epstep_isig_inv_glm : forall S T u, rtc epstep (TISig S T) u ->
  exists S' T', u = TISig S' T' /\ rtc epstep S S' /\ rtc epstep T T'.
Proof.
  intros S T u H. Show.
  remember (TISig S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    exists S0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_isig_inv_glm _ _ _ Hxy) as [S1 [T1 [-> [HS1 HT1]]]]. Show.
    destruct (IH S1 T1 eq_refl) as [S2 [T2 [-> [HS2 HT2]]]]. Show.
    exists S2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HS1. Show.
      * exact HS2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma cstep_isig_inv_glm : forall S T u, cstep (TISig S T) u ->
  exists S' T', u = TISig S' T'.
Proof.
  intros S T u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_isig_inv_glm _ _ _ Hpu) as [S' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_isig_inv_glm _ _ _ Heu) as [S' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_isig_inv_glm : forall S T u, rtc cstep (TISig S T) u ->
  exists S' T', u = TISig S' T'.
Proof.
  intros S T u H. Show.
  remember (TISig S T) as t eqn:Ht. Show.
  revert S T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros S0 T0 Heq; subst. Show.
  - Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_isig_inv_glm _ _ _ Hxy) as [S1 [T1 ->]]. Show.
    exact (IH S1 T1 eq_refl). Show.
Qed.

Corollary rtc_cstep_isig_not_sort_glm : forall S T j,
  ~ rtc cstep (TISig S T) (TSort j).
Proof.
  intros S T j H. Show.
  destruct (rtc_cstep_isig_inv_glm _ _ _ H) as [S' [T' Heq]]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_ichoice_inv_glm : forall E T u, pstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T' /\ pstep E E' /\ pstep T T'.
Proof.
  intros E T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_pstep_ichoice_inv_glm : forall E T u, rtc pstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T' /\ rtc pstep E E' /\ rtc pstep T T'.
Proof.
  intros E T u H. Show.
  remember (TIChoice E T) as t eqn:Ht. Show.
  revert E T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros E0 T0 Heq; subst. Show.
  - Show.
    exists E0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_ichoice_inv_glm _ _ _ Hxy) as [E1 [T1 [-> [HE1 HT1]]]]. Show.
    destruct (IH E1 T1 eq_refl) as [E2 [T2 [-> [HE2 HT2]]]]. Show.
    exists E2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HE1. Show.
      * exact HE2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma epstep_ichoice_inv_glm : forall E T u, epstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T' /\ epstep E E' /\ epstep T T'.
Proof.
  intros E T u H. Show.
  inversion H; subst. Show.
  do 2 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_epstep_ichoice_inv_glm : forall E T u, rtc epstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T' /\ rtc epstep E E' /\ rtc epstep T T'.
Proof.
  intros E T u H. Show.
  remember (TIChoice E T) as t eqn:Ht. Show.
  revert E T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros E0 T0 Heq; subst. Show.
  - Show.
    exists E0. Show.
    exists T0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_ichoice_inv_glm _ _ _ Hxy) as [E1 [T1 [-> [HE1 HT1]]]]. Show.
    destruct (IH E1 T1 eq_refl) as [E2 [T2 [-> [HE2 HT2]]]]. Show.
    exists E2. Show.
    exists T2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HE1. Show.
      * exact HE2. Show.
    + eapply rtc_step. Show.
      * exact HT1. Show.
      * exact HT2. Show.
Qed.

Lemma cstep_ichoice_inv_glm : forall E T u, cstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T'.
Proof.
  intros E T u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_ichoice_inv_glm _ _ _ Hpu) as [E' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_ichoice_inv_glm _ _ _ Heu) as [E' [T' [-> _]]]. Show.
    do 2 eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_ichoice_inv_glm : forall E T u, rtc cstep (TIChoice E T) u ->
  exists E' T', u = TIChoice E' T'.
Proof.
  intros E T u H. Show.
  remember (TIChoice E T) as t eqn:Ht. Show.
  revert E T Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros E0 T0 Heq; subst. Show.
  - Show.
    do 2 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_ichoice_inv_glm _ _ _ Hxy) as [E1 [T1 ->]]. Show.
    exact (IH E1 T1 eq_refl). Show.
Qed.

Corollary rtc_cstep_ichoice_not_sort_glm : forall E T j,
  ~ rtc cstep (TIChoice E T) (TSort j).
Proof.
  intros E T j H. Show.
  destruct (rtc_cstep_ichoice_inv_glm _ _ _ H) as [E' [T' Heq]]. Show.
  discriminate Heq. Show.
Qed.

(* --- LNil / LCons --- *)

Lemma pstep_lnil_inv_glm : forall A u, pstep (TLNil A) u ->
  exists A', u = TLNil A' /\ pstep A A'.
Proof.
  intros A u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_pstep_lnil_inv_glm : forall A u, rtc pstep (TLNil A) u ->
  exists A', u = TLNil A' /\ rtc pstep A A'.
Proof.
  intros A u H. Show.
  remember (TLNil A) as t eqn:Ht. Show.
  revert A Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_lnil_inv_glm _ _ Hxy) as [A1 [-> HA1]]. Show.
    destruct (IH A1 eq_refl) as [A2 [-> HA2]]. Show.
    exists A2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
Qed.

Lemma epstep_lnil_inv_glm : forall A u, epstep (TLNil A) u ->
  exists A', u = TLNil A' /\ epstep A A'.
Proof.
  intros A u H. Show.
  inversion H; subst. Show.
  eexists. Show.
  split. Show.
  + reflexivity. Show.
  + eassumption. Show.
Qed.

Lemma rtc_epstep_lnil_inv_glm : forall A u, rtc epstep (TLNil A) u ->
  exists A', u = TLNil A' /\ rtc epstep A A'.
Proof.
  intros A u H. Show.
  remember (TLNil A) as t eqn:Ht. Show.
  revert A Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_lnil_inv_glm _ _ Hxy) as [A1 [-> HA1]]. Show.
    destruct (IH A1 eq_refl) as [A2 [-> HA2]]. Show.
    exists A2. Show.
    split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
Qed.

Lemma cstep_lnil_inv_glm : forall A u, cstep (TLNil A) u ->
  exists A', u = TLNil A'.
Proof.
  intros A u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_lnil_inv_glm _ _ Hpu) as [A' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_lnil_inv_glm _ _ Heu) as [A' [-> _]]. Show.
    eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_lnil_inv_glm : forall A u, rtc cstep (TLNil A) u ->
  exists A', u = TLNil A'.
Proof.
  intros A u H. Show.
  remember (TLNil A) as t eqn:Ht. Show.
  revert A Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 Heq; subst. Show.
  - Show.
    eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_lnil_inv_glm _ _ Hxy) as [A1 ->]. Show.
    exact (IH A1 eq_refl). Show.
Qed.

Corollary rtc_cstep_lnil_not_sort_glm : forall A j,
  ~ rtc cstep (TLNil A) (TSort j).
Proof.
  intros A j H. Show.
  destruct (rtc_cstep_lnil_inv_glm _ _ H) as [A' Heq]. Show.
  discriminate Heq. Show.
Qed.

Lemma pstep_lcons_inv_glm : forall A a l u, pstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l' /\ pstep A A' /\ pstep a a' /\ pstep l l'.
Proof.
  intros A a l u H. Show.
  inversion H; subst. Show.
  do 3 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_pstep_lcons_inv_glm : forall A a l u, rtc pstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l' /\ rtc pstep A A' /\ rtc pstep a a' /\ rtc pstep l l'.
Proof.
  intros A a l u H. Show.
  remember (TLCons A a l) as t eqn:Ht. Show.
  revert A a l Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 a0 l0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    exists a0. Show.
    exists l0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (pstep_lcons_inv_glm _ _ _ _ Hxy) as [A1 [a1 [l1 [-> [HA1 [Ha1 Hl1]]]]]]. Show.
    destruct (IH A1 a1 l1 eq_refl) as [A2 [a2 [l2 [-> [HA2 [Ha2 Hl2]]]]]]. Show.
    exists A2. Show.
    exists a2. Show.
    exists l2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
    + eapply rtc_step. Show.
      * exact Ha1. Show.
      * exact Ha2. Show.
    + eapply rtc_step. Show.
      * exact Hl1. Show.
      * exact Hl2. Show.
Qed.

Lemma epstep_lcons_inv_glm : forall A a l u, epstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l' /\ epstep A A' /\ epstep a a' /\ epstep l l'.
Proof.
  intros A a l u H. Show.
  inversion H; subst. Show.
  do 3 eexists. Show.
  repeat split; try reflexivity; eassumption. Show.
Qed.

Lemma rtc_epstep_lcons_inv_glm : forall A a l u, rtc epstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l' /\ rtc epstep A A' /\ rtc epstep a a' /\ rtc epstep l l'.
Proof.
  intros A a l u H. Show.
  remember (TLCons A a l) as t eqn:Ht. Show.
  revert A a l Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 a0 l0 Heq; subst. Show.
  - Show.
    exists A0. Show.
    exists a0. Show.
    exists l0. Show.
    repeat split. Show.
    + reflexivity. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
    + apply rtc_refl. Show.
  - Show.
    destruct (epstep_lcons_inv_glm _ _ _ _ Hxy) as [A1 [a1 [l1 [-> [HA1 [Ha1 Hl1]]]]]]. Show.
    destruct (IH A1 a1 l1 eq_refl) as [A2 [a2 [l2 [-> [HA2 [Ha2 Hl2]]]]]]. Show.
    exists A2. Show.
    exists a2. Show.
    exists l2. Show.
    repeat split. Show.
    + reflexivity. Show.
    + eapply rtc_step. Show.
      * exact HA1. Show.
      * exact HA2. Show.
    + eapply rtc_step. Show.
      * exact Ha1. Show.
      * exact Ha2. Show.
    + eapply rtc_step. Show.
      * exact Hl1. Show.
      * exact Hl2. Show.
Qed.

Lemma cstep_lcons_inv_glm : forall A a l u, cstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l'.
Proof.
  intros A a l u H. Show.
  inversion H as [t u0 Hpu | t u0 Heu]; subst. Show.
  - Show.
    destruct (rtc_pstep_lcons_inv_glm _ _ _ _ Hpu) as [A' [a' [l' [-> _]]]]. Show.
    do 3 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (rtc_epstep_lcons_inv_glm _ _ _ _ Heu) as [A' [a' [l' [-> _]]]]. Show.
    do 3 eexists. Show.
    reflexivity. Show.
Qed.

Lemma rtc_cstep_lcons_inv_glm : forall A a l u, rtc cstep (TLCons A a l) u ->
  exists A' a' l', u = TLCons A' a' l'.
Proof.
  intros A a l u H. Show.
  remember (TLCons A a l) as t eqn:Ht. Show.
  revert A a l Ht. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros A0 a0 l0 Heq; subst. Show.
  - Show.
    do 3 eexists. Show.
    reflexivity. Show.
  - Show.
    destruct (cstep_lcons_inv_glm _ _ _ _ Hxy) as [A1 [a1 [l1 ->]]]. Show.
    exact (IH A1 a1 l1 eq_refl). Show.
Qed.

Corollary rtc_cstep_lcons_not_sort_glm : forall A a l j,
  ~ rtc cstep (TLCons A a l) (TSort j).
Proof.
  intros A a l j H. Show.
  destruct (rtc_cstep_lcons_inv_glm _ _ _ _ H) as [A' [a' [l' Heq]]]. Show.
  discriminate Heq. Show.
Qed.

(* --- general EPI nonsort (roots to UnitT/Sigma are non-sort) --- *)

Lemma rtc_cstep_epi_not_sort_glm : forall E P j,
  ~ rtc cstep (TEPi E P) (TSort j).
Proof.
  intros E P j H. Show.
  remember (TEPi E P) as x eqn:Hx. Show.
  revert E P Hx. Show.
  induction H as [x | x y z Hxy Hyz IH]; intros E0 P0 Hx. Show.
  - subst x. Show.
    discriminate. Show.
  - subst x. Show.
    inversion Hxy as [t u Hpu | t u Heu]; subst. Show.
    + Show.
      remember (TEPi E0 P0) as a eqn:Ha. Show.
      revert E0 P0 Ha. Show.
      induction Hpu as [a | a b c Hab Hbc IHa]; intros E1 P1 Ha. Show.
      * subst a. Show.
        eapply IH. Show.
        reflexivity. Show.
      * subst a. Show.
        inversion Hab; subst. Show.
        -- Show.
           eapply IHa. Show.
           + eapply rtc_step. Show.
             * eapply pstep_cstep. Show.
               exact Hbc. Show.
             * exact Hyz. Show.
           + reflexivity. Show.
        -- Show.
           exfalso. Show.
           eapply epi_nil_not_sort_parent. Show.
           eapply rtc_trans. Show.
           * eapply rtc_step. Show.
             -- eapply pstep_cstep. Show.
                eapply ps_epi_nil. Show.
                eassumption. Show.
             -- exact Hbc. Show.
           * exact Hyz. Show.
        -- Show.
           exfalso. Show.
           pose proof (cjoin_pi_inv) as _. Show.
           eapply cstep_root_to_nonsort_parent with (q := TSigma (TApp P2 TEZero) (lift 1 0 (TEPi E2 (TLam (TApp (lift 1 0 P2) (TESucc (TVar 0))))))) (h := HSigma) in Hyz. Show.
           { discriminate Hyz. Show. }
           { eapply rtc_trans. Show.
             - eapply rtc_step. Show.
               + eapply pstep_cstep. Show.
                 eapply ps_epi_cons. Show.
                 * eassumption. Show.
                 * eassumption. Show.
                 * eassumption. Show.
               + exact Hbc. Show.
             - exact Hyz. Show. }
           { constructor. Show. }
           { discriminate. Show. }
    + Show.
      remember (TEPi E0 P0) as a eqn:Ha. Show.
      revert E0 P0 Ha. Show.
      induction Heu as [a | a b c Hab Hbc IHa]; intros E1 P1 Ha. Show.
      * subst a. Show.
        eapply IH. Show.
        reflexivity. Show.
      * subst a. Show.
        inversion Hab; subst. Show.
        eapply IHa. Show.
        + eapply rtc_step. Show.
          * eapply epstep_cstep. Show.
            exact Hbc. Show.
          * exact Hyz. Show.
        + reflexivity. Show.
Qed.

