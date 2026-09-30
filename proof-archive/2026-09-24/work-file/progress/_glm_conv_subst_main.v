(* GLM worker 1 — conv-subst main: the exact two-sided conversion            *)
(* substitution theorem, reduced to a SINGLE residual constructor case.      *)
(*                                                                          *)
(*   Definition conv_subst_compatible_glm : Prop :=                         *)
(*     forall t t' u u', conv t t' -> conv u u' -> forall k,                *)
(*       conv (subst u k t) (subst u' k t').                                *)
(*                                                                          *)
(* Structure of the proof (all 36 constructors of conv):                    *)
(*   - cv_step : step_subst_glm transports the reduction (same u), then     *)
(*     the substituent is swapped by conv_subst_rigid_glm + cv_trans.       *)
(*   - cv_eta  : substitution keeps the eta shape (subst_lift_one_zero),    *)
(*     cv_eta re-fires, then the rigid swap.                                *)
(*   - congruences: the two-sided IH applies directly at the same cutoffs.  *)
(*   - cv_phi  : the ONLY genuinely open case.  Its conclusion is an        *)
(*     instance of the main theorem, so the whole case collapses to the     *)
(*     cv_phi residual conv_subst_cv_phi_residual_glm stated below.  The    *)
(*     residual is closed whenever a substituent is convertible to some     *)
(*     neutral (cv_phi_residual_one_neutral_glm) — via the neutral-pivot    *)
(*     three-leg chain — and the neutral-pair / neutral-at-k pair theorems  *)
(*     below give the corresponding unconditional closed fragments of       *)
(*     conv_subst_compatible_glm.                                           *)
(*                                                                          *)
(* Why the residual is genuinely hard: transporting spine_phi through       *)
(* substitution needs, in its sph_neutral case, neutral (subst u k Phin).   *)
(* A neutral tail that mentions the substituted variable k becomes          *)
(* lift k 0 u — neutral iff lift k 0 u is neutral.  For u whose lifted      *)
(* form is not neutral and not nil/cons-shaped (e.g. u = TLam b), NO        *)
(* spine_phi derivation exists on the substituted Phi at all: the eval      *)
(* target is forced (the substituted tail is step-normal), so cv_phi       *)
(* cannot re-fire on the substituted mu-applications, and TMuS-headed      *)
(* terms are head-stuck, so no step/congruence route exists either.  The    *)
(* honest reduction is therefore: exact theorem ⟸ this one residual.        *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_subst_reduction_bundle_eval
               _glm_subst_reduction_bundle_spine
               _glm_conv_subst_algebra _glm_conv_subst_rigid
               _glm_conv_subst_same_neutral _glm_conv_subst_neutral_pair.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* The exact target statement (verbatim from the task). *)
Definition conv_subst_compatible_glm : Prop :=
  forall t t' u u', conv t t' -> conv u u' -> forall k,
    conv (subst u k t) (subst u' k t').

(* The single residual constructor case: everything the cv_phi case of the  *)
(* induction needs, stated in isolation.                                    *)
Definition conv_subst_cv_phi_residual_glm : Prop :=
  forall S1 S2 i Phi1 Phi2 Psi1 Psi2 u u' : term, forall k : nat,
    conv u u' ->
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 ->
    eval (labels (TApp S2 i)) Phi2 ->
    spine_phi S1 i Phi1 Psi1 ->
    spine_phi S2 i Phi2 Psi2 ->
    conv Psi1 Psi2 ->
    conv (TApp (TMuS (subst u k S1)) (subst u k i))
         (TApp (TMuS (subst u' k S2)) (subst u' k i)).

(* cv_case_br with both sides substituted: the head clause changes (c,b) to *)
(* (c',b') while the WHOLE branch map changes substituent — so the prefix    *)
(* map, head clause and tail map are transported together, clause by clause, *)
(* with cv_case_br; the pointwise clause premises are conv_subst_rigid_glm. *)
Lemma conv_case_branches_full_glm :
  forall (bs1 bs2 : list (term * term)) (M Q c c' b b' u u' : term) (k : nat),
    conv u u' ->
    conv (subst u k c) (subst u' k c') ->
    conv (subst u (S k) b) (subst u' (S k) b') ->
    forall L : list (term * term),
    conv (TCase M Q (L ++ map (fun '(c0, b0) => (subst u k c0, subst u (S k) b0))
                              (bs1 ++ (c, b) :: bs2)))
         (TCase M Q (L ++ map (fun '(c0, b0) => (subst u' k c0, subst u' (S k) b0))
                              (bs1 ++ (c', b') :: bs2))).
Proof.
  intros bs1 bs2 M Q c c' b b' u u' k Hu Hc Hb.
  assert (Hpt : forall c0 b0, In (c0, b0) (bs1 ++ bs2) ->
      conv (subst u k c0) (subst u' k c0) /\
      conv (subst u (S k) b0) (subst u' (S k) b0)).
  { intros c0 b0 HIn. split.
    - exact (conv_subst_rigid_glm u u' Hu c0 k).
    - exact (conv_subst_rigid_glm u u' Hu b0 (S k)). }
  induction bs1 as [| [c0 b0] bs10 IH]; intros L; rewrite !map_app; cbn [map].
  - (* nil prefix *)
    eapply cv_trans.
    + apply (@cv_case_br M Q L (subst u k c) (subst u' k c')
              (subst u (S k) b) (subst u' (S k) b')
              (map (fun '(c1, b1) => (subst u k c1, subst u (S k) b1)) bs2)).
      * exact Hc.
      * exact Hb.
    + assert (Ht := conv_case_branch_map_prefix_glm bs2 M Q u u' k
                      (fun c1 b1 HIn => Hpt c1 b1 HIn)
                      (L ++ (subst u' k c', subst u' (S k) b') :: nil)).
      rewrite <- !app_assoc in Ht. cbn [app] in Ht. exact Ht.
  - (* cons prefix *)
    eapply cv_trans.
    + apply (@cv_case_br M Q L (subst u k c0) (subst u' k c0)
              (subst u (S k) b0) (subst u' (S k) b0)
              (map (fun '(c1, b1) => (subst u k c1, subst u (S k) b1)) bs10
               ++ (subst u k c, subst u (S k) b)
               :: map (fun '(c1, b1) => (subst u k c1, subst u (S k) b1)) bs2)).
      * exact (proj1 (Hpt c0 b0 (in_or_app ((c0, b0) :: bs10) bs2 (c0, b0)
                        (or_introl (in_eq (c0, b0) bs10))))).
      * exact (proj2 (Hpt c0 b0 (in_or_app ((c0, b0) :: bs10) bs2 (c0, b0)
                        (or_introl (in_eq (c0, b0) bs10))))).
    + specialize (IH (fun c1 b1 HIn =>
                        Hpt c1 b1 (in_cons (c0, b0) (c1, b1) (bs10 ++ bs2) HIn))
                     (L ++ (subst u' k c0, subst u' (S k) b0) :: nil)).
      rewrite !map_app in IH. cbn [map] in IH.
      rewrite <- !app_assoc in IH. cbn [app] in IH. exact IH.
Qed.

(* THE MAIN REDUCTION: the exact conv_subst_compatible_glm follows from the *)
(* cv_phi residual alone; every other constructor is closed here.  The     *)
(* induction statement has the substituents generalized INSIDE, so cv_sym   *)
(* can swap the pair; conv_subst_compatible_glm follows by reordering.      *)
Theorem conv_subst_ind_glm :
  conv_subst_cv_phi_residual_glm ->
  forall t t' : term, conv t t' ->
  forall u u' : term, conv u u' -> forall k : nat,
    conv (subst u k t) (subst u' k t').
Proof.
  intros Hres t t' H.
  induction H; intros uu uu' Hu kk; cbn.
  - (* cv_step *)
    eapply cv_trans.
    + apply cv_step. exact (step_subst_glm _ _ H uu kk).
    + exact (conv_subst_rigid_glm uu uu' Hu _ kk).
  - (* cv_refl *)
    eapply cv_trans.
    + apply cv_refl.
    + exact (conv_subst_rigid_glm uu uu' Hu t kk).
  - (* cv_sym *) apply cv_sym. exact (IHconv uu' uu (cv_sym Hu) kk).
  - (* cv_trans *)
    eapply cv_trans;
      [exact (IHconv1 uu uu' Hu kk)
      | exact (IHconv2 uu' uu' (cv_refl _) kk)].
  - (* cv_eta *)
    rewrite subst_lift_one_zero.
    eapply cv_trans.
    + apply cv_eta.
    + exact (conv_subst_rigid_glm uu uu' Hu _ kk).
  - (* cv_phi *)
    exact (Hres S1 S2 i Phi1 Phi2 Psi1 Psi2 uu uu' kk Hu
                H H0 H1 H2 H3 H4).
  - (* cv_pi *)  apply cv_pi; eauto.
  - (* cv_lam *) apply cv_lam. exact (IHconv uu uu' Hu (S kk)).
  - (* cv_app *) apply cv_app; eauto.
  - (* cv_sigma *) apply cv_sigma; eauto.
  - (* cv_pair *) apply cv_pair; eauto.
  - (* cv_fst *) apply cv_fst. exact (IHconv uu uu' Hu kk).
  - (* cv_snd *) apply cv_snd. exact (IHconv uu uu' Hu kk).
  - (* cv_conse *) apply cv_conse; eauto.
  - (* cv_enumt *) apply cv_enumt. exact (IHconv uu uu' Hu kk).
  - (* cv_esucc *) apply cv_esucc. exact (IHconv uu uu' Hu kk).
  - (* cv_epi *) apply cv_epi; eauto.
  - (* cv_switch *) apply cv_switch; eauto.
  - (* cv_idesc *) apply cv_idesc. exact (IHconv uu uu' Hu kk).
  - (* cv_ivar *) apply cv_ivar. exact (IHconv uu uu' Hu kk).
  - (* cv_iprod *) apply cv_iprod; eauto.
  - (* cv_ipi *) apply cv_ipi; eauto.
  - (* cv_isig *) apply cv_isig; eauto.
  - (* cv_ichoice *) apply cv_ichoice; eauto.
  - (* cv_interp *) apply cv_interp; eauto.
  - (* cv_mui *) apply cv_mui. exact (IHconv uu uu' Hu kk).
  - (* cv_mus *) apply cv_mus. exact (IHconv uu uu' Hu kk).
  - (* cv_in *) apply cv_in. exact (IHconv uu uu' Hu kk).
  - (* cv_ind *) apply cv_ind; eauto.
  - (* cv_iall *) apply cv_iall; eauto.
  - (* cv_hyps *) apply cv_hyps; eauto.
  - (* cv_list *) apply cv_list. exact (IHconv uu uu' Hu kk).
  - (* cv_lnil *) apply cv_lnil. exact (IHconv uu uu' Hu kk).
  - (* cv_lcons *) apply cv_lcons; eauto.
  - (* cv_case *)
    eapply cv_trans.
    + apply (@cv_case (subst uu kk M) (subst uu' kk M')
                      (subst uu kk Q) (subst uu' kk Q')
                      (map (fun '(c0, b0) => (subst uu kk c0, subst uu (S kk) b0)) bs)).
      * exact (IHconv1 uu uu' Hu kk).
      * exact (IHconv2 uu uu' Hu kk).
    + assert (Ht := conv_case_branch_map_prefix_glm bs (subst uu' kk M')
                       (subst uu' kk Q') uu uu' kk
                       (fun c b _ =>
                         conj (conv_subst_rigid_glm uu uu' Hu c kk)
                              (conv_subst_rigid_glm uu uu' Hu b (S kk))) []).
      cbn [app] in Ht. exact Ht.
  - (* cv_case_br *)
    eapply cv_trans.
    + apply (@cv_case (subst uu kk M) (subst uu' kk M)
                      (subst uu kk Q) (subst uu' kk Q)
                      (map (fun '(c0, b0) => (subst uu kk c0, subst uu (S kk) b0))
                           (bs1 ++ (c, b) :: bs2))).
      * exact (conv_subst_rigid_glm uu uu' Hu M kk).
      * exact (conv_subst_rigid_glm uu uu' Hu Q kk).
    + exact (conv_case_branches_full_glm bs1 bs2 (subst uu' kk M) (subst uu' kk Q)
                c c' b b' uu uu' kk Hu (IHconv1 uu uu' Hu kk)
                (IHconv2 uu uu' Hu (S kk)) []).
Qed.

(* Reordering wrapper: the exact task statement. *)
Theorem conv_subst_compatible_glm_of_residual :
  conv_subst_cv_phi_residual_glm -> conv_subst_compatible_glm.
Proof.
  intros Hres t t' u u' H Hu k.
  exact (conv_subst_ind_glm Hres t t' H u u' Hu k).
Qed.

(* Unconditional closed fragment 1: both substituents neutral. *)
Theorem conv_subst_compatible_neutral_pair_proved :
  forall t t' u u' : term, conv t t' -> conv u u' ->
    neutral u -> neutral u' ->
    forall k : nat, conv (subst u k t) (subst u' k t').
Proof. exact conv_subst_neutral_pair_glm. Qed.

(* Unconditional closed fragment 2: one substituent convertible to some     *)
(* neutral — by cv_sym/cv_trans this is a property of the PAIR.             *)
Theorem conv_subst_compatible_one_neutral_proved :
  forall t t' u u' : term, conv t t' -> conv u u' ->
    (exists n : term, neutral n /\ conv u n) ->
    forall k : nat, conv (subst u k t) (subst u' k t').
Proof. exact conv_subst_one_neutral_glm. Qed.

(* The residual is discharged under the one-neutral hypothesis: the cv_phi  *)
(* conclusion is itself an instance of the two-sided theorem.                *)
Lemma cv_phi_residual_one_neutral_glm :
  forall S1 S2 i Phi1 Phi2 Psi1 Psi2 u u' : term, forall k : nat,
    conv u u' ->
    (exists n : term, neutral n /\ conv u n) ->
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 ->
    eval (labels (TApp S2 i)) Phi2 ->
    spine_phi S1 i Phi1 Psi1 ->
    spine_phi S2 i Phi2 Psi2 ->
    conv Psi1 Psi2 ->
    conv (TApp (TMuS (subst u k S1)) (subst u k i))
         (TApp (TMuS (subst u' k S2)) (subst u' k i)).
Proof.
  intros S1 S2 i Phi1 Phi2 Psi1 Psi2 u u' k Hu Hneut Hbr He1 He2 Hs1 Hs2 Hpsis.
  assert (Hpsis_phi : conv (TApp (TMuS S1) i) (TApp (TMuS S2) i)).
  { exact (@cv_phi S1 S2 i Phi1 Phi2 Psi1 Psi2 Hbr He1 He2 Hs1 Hs2 Hpsis). }
  apply (conv_subst_one_neutral_glm (TApp (TMuS S1) i) (TApp (TMuS S2) i)
                                    u u' Hpsis_phi Hu Hneut k).
Qed.

(* Same under the stronger plain-neutrality of both substituents. *)
Lemma cv_phi_residual_neutral_pair_glm :
  forall S1 S2 i Phi1 Phi2 Psi1 Psi2 u u' : term, forall k : nat,
    conv u u' -> neutral u -> neutral u' ->
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 ->
    eval (labels (TApp S2 i)) Phi2 ->
    spine_phi S1 i Phi1 Psi1 ->
    spine_phi S2 i Phi2 Psi2 ->
    conv Psi1 Psi2 ->
    conv (TApp (TMuS (subst u k S1)) (subst u k i))
         (TApp (TMuS (subst u' k S2)) (subst u' k i)).
Proof.
  intros S1 S2 i Phi1 Phi2 Psi1 Psi2 u u' k Hu Hunat Hunat' Hbr He1 He2 Hs1 Hs2 Hpsis.
  assert (Hpsis_phi : conv (TApp (TMuS S1) i) (TApp (TMuS S2) i)).
  { exact (@cv_phi S1 S2 i Phi1 Phi2 Psi1 Psi2 Hbr He1 He2 Hs1 Hs2 Hpsis). }
  apply (conv_subst_neutral_pair_glm (TApp (TMuS S1) i) (TApp (TMuS S2) i)
                                     u u' Hpsis_phi Hu Hunat Hunat' k).
Qed.

Print Assumptions conv_subst_compatible_glm_of_residual.
Print Assumptions conv_subst_compatible_neutral_pair_proved.
Print Assumptions conv_subst_compatible_one_neutral_proved.
Print Assumptions cv_phi_residual_one_neutral_glm.

Check conv_subst_compatible_glm_of_residual :
  conv_subst_cv_phi_residual_glm -> conv_subst_compatible_glm.
