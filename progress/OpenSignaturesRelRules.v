(* Rule-level semantic lemmas for description interpretation, hypothesis
   types and builders, and function cumulativity. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelElim.
Import ListNotations.

(* The semantic family of a related term family. *)
Lemma term_family : forall IT1 IT2 RI X1 X2, S2 IT1 IT2 RI ->
  rel_at X1 X2 (Family IT1) (Family IT2) ->
  let Y := live_fam RI (fam_of 0 X1) in
  fam_resp RI Y /\
  (forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 -> interp 0 (TApp X1 i1) (TApp X2 i2) (Y i1)) /\
  (forall i1 i2 x1 x2, closed i1 -> closed i2 -> RI i1 i2 -> Y i1 x1 x2 -> rel_at x1 x2 (TApp X1 i1) (TApp X2 i2)).
Proof.
  intros IT1 IT2 RI X1 X2 HI HX Y.
  pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
  destruct (family_sem _ _ _ _ _ HI HX) as [HYr HYi].
  pose proof (live_fam_interp _ _ _ _ HP HYi) as HYi'.
  refine (conj (live_fam_resp _ _ HP HC HYr) (conj HYi' _)).
  intros i1 i2 x1 x2 H1 H2 Hi Hx; exists 0, (Y i1); split; [apply HYi'; assumption|exact Hx].
Qed.

Lemma sem_interp_rule : forall IT1 IT2 D1 D2' X1 X2,
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (TIDesc IT1) (TIDesc IT2) ->
  rel_at X1 X2 (Family IT1) (Family IT2) ->
  rel_at (TInterp IT1 D1 X1) (TInterp IT2 D2' X2) (TSort 0) (TSort 0).
Proof.
  intros IT1 IT2 D1 D2' X1 X2 HIT HD HX; destruct (small_of_rel _ _ HIT) as [RI HI].
  destruct (rel_at_desc _ _ _ _ _ HI HD) as [F HF].
  destruct (term_family _ _ _ _ _ HI HX) as [HYr [HYi _]].
  apply rel_at_sort; eexists.
  apply (interp_TInterp _ _ _ _ HF (S2_per _ _ _ HI) (S2_conv_closed _ _ _ HI) 0); [exact HYr|exact HYi].
Qed.

Lemma interp_payload_rel : forall IT1 IT2 RI D1 D2' X1 X2 xs1 xs2, S2 IT1 IT2 RI ->
  rel_at D1 D2' (TIDesc IT1) (TIDesc IT2) -> rel_at X1 X2 (Family IT1) (Family IT2) ->
  rel_at xs1 xs2 (TInterp IT1 D1 X1) (TInterp IT2 D2' X2) ->
  exists F, D2 RI D1 D2' F /\ F (live_fam RI (fam_of 0 X1)) xs1 xs2.
Proof.
  intros IT1 IT2 RI D1 D2' X1 X2 xs1 xs2 HI HD HX Hxs.
  destruct (rel_at_desc _ _ _ _ _ HI HD) as [F HF].
  destruct (term_family _ _ _ _ _ HI HX) as [HYr [HYi _]].
  exists F; split; [exact HF|].
  eapply rel_at_transfer; [exact Hxs|exact (interp_TInterp _ _ _ _ HF (S2_per _ _ _ HI) (S2_conv_closed _ _ _ HI) 0
    IT1 IT2 X1 X2 _ HYr HYi)|apply cv_refl].
Qed.

Lemma sem_iall_rule : forall IT1 IT2 D1 D2' X1 X2 xs1 xs2 P1 P2,
  closed xs1 -> closed xs2 ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (TIDesc IT1) (TIDesc IT2) ->
  rel_at X1 X2 (Family IT1) (Family IT2) ->
  rel_at xs1 xs2 (TInterp IT1 D1 X1) (TInterp IT2 D2' X2) ->
  rel_at P1 P2 (motive IT1 X1) (motive IT2 X2) ->
  rel_at (TIAll IT1 D1 X1 xs1 P1) (TIAll IT2 D2' X2 xs2 P2) (TSort 0) (TSort 0).
Proof.
  intros IT1 IT2 D1 D2' X1 X2 xs1 xs2 P1 P2 Hc1 Hc2 HIT HD HX Hxs HP.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  destruct (interp_payload_rel _ _ _ _ _ _ _ _ _ HI HD HX Hxs) as [F [HF HFxs]].
  destruct (term_family _ _ _ _ _ HI HX) as [HYr [HYi HYx]].
  apply rel_at_sort.
  eapply sem_iall_gen; [exact HF|eapply S2_per; exact HI|eapply S2_conv_closed; exact HI|exact HYr
    | |exact Hc1|exact Hc2|exact HFxs].
  eapply motive_mot_rel; [exact HI|exact HIT|exact HX| |exact HP].
  intros i1 i2 x1 x2 H1 H2 Hx1 Hx2 Hi Hx; apply HYx; assumption.
Qed.

Lemma recursive_method_hyp : forall IT1 IT2 RI X1 X2 P1 P2 h1 h2 (Y : fam), S2 IT1 IT2 RI ->
  closed IT1 -> closed IT2 -> closed X1 -> closed X2 -> closed P1 -> closed P2 ->
  (forall i1 i2 x1 x2, closed i1 -> closed i2 -> RI i1 i2 -> Y i1 x1 x2 -> rel_at x1 x2 (TApp X1 i1) (TApp X2 i2)) ->
  rel_at h1 h2 (recursive_method IT1 X1 P1) (recursive_method IT2 X2 P2) ->
  hyp_rel RI Y P1 P2 h1 h2.
Proof.
  intros IT1 IT2 RI X1 X2 P1 P2 h1 h2 Y HI HI1 HI2 HX1 HX2 HP1 HP2 HYx Hh i1 i2 x1 x2 Hi1 Hi2 Hx1 Hx2 Hi Hx.
  unfold recursive_method in Hh.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hh (small_rel_at _ _ _ _ _ HI Hi) Hi1 Hi2) as H1.
  rewrite !subst_pi_closed in H1 by (assumption || lia).
  rewrite !subst_app, !subst_pair, !subst_var_same in H1.
  rewrite !subst_var_other in H1 by lia.
  rewrite !(subst_not_free X1), !(subst_not_free X2), !(subst_not_free P1), !(subst_not_free P2)
    in H1 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H1 (HYx i1 i2 x1 x2 Hi1 Hi2 Hi Hx) Hx1 Hx2) as H2.
  rewrite !subst_app, !subst_pair, !subst_var_same in H2.
  rewrite !(subst_not_free P1), !(subst_not_free P2), !(subst_not_free i1), !(subst_not_free i2)
    in H2 by fresh_out2.
  exact H2.
Qed.

Lemma sem_hyps_rule : forall IT1 IT2 D1 D2' X1 X2 P1 P2 h1 h2 xs1 xs2,
  closed IT1 -> closed IT2 -> closed X1 -> closed X2 -> closed P1 -> closed P2 ->
  closed h1 -> closed h2 -> closed xs1 -> closed xs2 ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (TIDesc IT1) (TIDesc IT2) ->
  rel_at X1 X2 (Family IT1) (Family IT2) ->
  rel_at P1 P2 (motive IT1 X1) (motive IT2 X2) ->
  rel_at h1 h2 (recursive_method IT1 X1 P1) (recursive_method IT2 X2 P2) ->
  rel_at xs1 xs2 (TInterp IT1 D1 X1) (TInterp IT2 D2' X2) ->
  rel_at (THyps IT1 D1 X1 P1 h1 xs1) (THyps IT2 D2' X2 P2 h2 xs2)
    (TIAll IT1 D1 X1 xs1 P1) (TIAll IT2 D2' X2 xs2 P2).
Proof.
  intros IT1 IT2 D1 D2' X1 X2 P1 P2 h1 h2 xs1 xs2 HI1 HI2 HX1 HX2 HP1 HP2 Hh1 Hh2 Hc1 Hc2 HIT HD HX HP Hh Hxs.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  destruct (interp_payload_rel _ _ _ _ _ _ _ _ _ HI HD HX Hxs) as [F [HF HFxs]].
  destruct (term_family _ _ _ _ _ HI HX) as [HYr [HYi HYx]].
  assert (HM : mot_rel RI (live_fam RI (fam_of 0 X1)) P1 P2).
  { eapply motive_mot_rel; [exact HI|exact HIT|exact HX| |exact HP].
    intros i1 i2 x1 x2 H1 H2 Hx1 Hx2 Hi Hx; apply HYx; assumption. }
  assert (HH : hyp_rel RI (live_fam RI (fam_of 0 X1)) P1 P2 h1 h2).
  { eapply recursive_method_hyp; [exact HI|exact HI1|exact HI2|exact HX1|exact HX2|exact HP1|exact HP2| |exact Hh].
    intros i1 i2 x1 x2 H1 H2 Hi Hx; apply HYx; assumption. }
  exact (sem_hyps_gen _ _ _ _ HF (S2_per _ _ _ HI) (S2_conv_closed _ _ _ HI) IT1 IT2 X1 X2 P1 P2 h1 h2 _
    HYr HM HH HI1 HI2 HX1 HX2 HP1 HP2 Hh1 Hh2 xs1 xs2 Hc1 Hc2 HFxs).
Qed.

(* ------------------------------------------------------------------ *)
(* Function cumulativity *)

Lemma universe_le_subst : forall A B, universe_le A B -> forall u x, closed u ->
  universe_le (subst u x A) (subst u x B).
Proof.
  intros A B H; induction H; intros u y Hu.
  - apply ul_refl.
  - apply ul_sort; assumption.
  - destruct (Nat.eq_dec y x) as [->|Hne].
    + unfold subst; cbn [substitute].
      rewrite !(substitution_binder_identity _ x) by
        (intros v Hv; apply in_remove_iff in Hv as [_ Hv]; rewrite (proj2 (Nat.eqb_neq v x)) by auto; reflexivity).
      assert (Hbind : forall t, substitute (bind_substitution (fun v => if Nat.eqb v x then u else TVar v) x x) t = t).
      { intro t; apply substitute_identity_on; intros v _; unfold bind_substitution.
        destruct (Nat.eqb v x) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity|reflexivity]. }
      rewrite !Hbind. apply ul_pi; [apply IHuniverse_le1; exact Hu|exact H0].
    + rewrite !subst_pi_closed by assumption. apply ul_pi; auto.
Qed.

Inductive ule : nat -> term -> term -> Prop :=
| ule_refl : forall n A, ule n A A
| ule_sort : forall n j k, j <= k -> ule n (TSort j) (TSort k)
| ule_pi : forall n x A B C D, ule n C A -> ule n B D -> ule (S n) (TPi x A B) (TPi x C D).

Lemma ule_mono : forall n X Y, ule n X Y -> forall m, n <= m -> ule m X Y.
Proof.
  intros n X Y H; induction H; intros m Hm.
  - apply ule_refl.
  - apply ule_sort; assumption.
  - destruct m as [|m]; [lia|]. apply ule_pi; [apply IHule1|apply IHule2]; lia.
Qed.
Lemma universe_le_ule : forall X Y, universe_le X Y -> exists n, ule n X Y.
Proof.
  intros X Y H; induction H.
  - exists 0; apply ule_refl.
  - exists 0; apply ule_sort; assumption.
  - destruct IHuniverse_le1 as [n Hn], IHuniverse_le2 as [m Hm].
    exists (S (Nat.max n m)); apply ule_pi; eapply ule_mono; try eassumption; lia.
Qed.
Lemma ule_subst : forall n A B, ule n A B -> forall u x, closed u -> ule n (subst u x A) (subst u x B).
Proof.
  intros n A B H; induction H; intros u y Hu.
  - apply ule_refl.
  - apply ule_sort; assumption.
  - destruct (Nat.eq_dec y x) as [->|Hne].
    + unfold subst; cbn [substitute].
      rewrite !(substitution_binder_identity _ x) by
        (intros v Hv; apply in_remove_iff in Hv as [_ Hv]; rewrite (proj2 (Nat.eqb_neq v x)) by auto; reflexivity).
      assert (Hbind : forall t, substitute (bind_substitution (fun v => if Nat.eqb v x then u else TVar v) x x) t = t).
      { intro t; apply substitute_identity_on; intros v _; unfold bind_substitution.
        destruct (Nat.eqb v x) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity|reflexivity]. }
      rewrite !Hbind. apply ule_pi; [apply IHule1; exact Hu|exact H0].
    + rewrite !subst_pi_closed by assumption. apply ule_pi; auto.
Qed.

Lemma ule_incl : forall n X1 Y1, ule n X1 Y1 -> forall X2 Y2, universe_le X2 Y2 ->
  forall j k RX RY, interp j X1 X2 RX -> interp k Y1 Y2 RY -> rel_incl RX RY.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros X1 Y1 H X2 Y2 H2 j0 k0 RX RY HX HY.
  destruct H as [n0 Z|n0 j k Hjk|n0 x A B C D HCA HBD].
  - intros t u Ht; exact (rel_equiv_r _ _ _ _ (interp_unique_left _ _ _ _ _ _ _ _ HX HY (cv_refl _)) Ht).
  - destruct H2 as [Z|a b Hab|x2 A2 B2 C2 D2s HCA HBD].
    + intros t u Ht; exact (rel_equiv_r _ _ _ _ (interp_unique_right _ _ _ _ _ _ _ _ HX HY (cv_refl _)) Ht).
    + assert (HRX : rel_equiv RX (univ_rel j)).
      { eapply interp_unique_left; [exact HX|apply sort_interp|apply cv_refl]. }
      assert (HRY : rel_equiv RY (univ_rel k)).
      { eapply interp_unique_left; [exact HY|apply sort_interp|apply cv_refl]. }
      intros t u Ht; apply HRY. destruct (proj1 (HRX t u) Ht) as [R HR].
      exists R; eapply interp_cumulative; [exact Hjk|exact HR].
    + exfalso. destruct (interp_pi_view _ _ _ _ _ _ _ (interp_sym _ _ _ _ HX) (cv_refl _)) as
        (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & _).
      eapply head_clash; [exact HB|reflexivity|reflexivity|discriminate].
  - destruct H2 as [Z|a b Hab|x2 A2 B2 C2 D2s HCA2 HBD2].
    + intros t u Ht; exact (rel_equiv_r _ _ _ _ (interp_unique_right _ _ _ _ _ _ _ _ HX HY (cv_refl _)) Ht).
    + exfalso. destruct (interp_pi_view _ _ _ _ _ _ _ HX (cv_refl _)) as
        (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & _).
      eapply head_clash; [exact HB|reflexivity|reflexivity|discriminate].
    + destruct (interp_pi_view _ _ _ _ _ _ _ HX (cv_refl _)) as
        (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
      destruct (interp_pi_view _ _ _ _ _ _ _ HY (cv_refl _)) as
        (x1 & W0 & Z0 & y1 & W0' & Z0' & RW & RZ & HA' & HB' & HW & HZ & HE').
      destruct (conv_pi_inv _ _ _ _ _ _ HA) as [HAU HBV].
      destruct (conv_pi_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
      destruct (conv_pi_inv _ _ _ _ _ _ HA') as [HCW HDZ].
      destruct (conv_pi_inv _ _ _ _ _ _ HB') as [HCW' HDZ'].
      assert (HCAi : rel_incl RW RU).
      { eapply (IHn n0); [lia|exact HCA|exact HCA2| |].
        - eapply interp_conv; [exact HW|apply cv_sym; exact HCW|apply cv_sym; exact HCW'].
        - eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']. }
      intros f g Hfg. apply HE'. intros c1 c2 Hc1 Hc2 Hc.
      pose proof (HCAi _ _ Hc) as HcU.
      pose proof (proj1 (HE f g) Hfg c1 c2 Hc1 Hc2 HcU) as Happ.
      eapply (IHn n0); [lia|apply ule_subst; [exact HBD|exact Hc1]|apply universe_le_subst; [exact HBD2|exact Hc2]
        | | |exact Happ].
      * eapply interp_conv; [apply HV; assumption|apply cv_sym, HBV, Hc1|apply cv_sym, HBV', Hc2].
      * eapply interp_conv; [apply HZ; assumption|apply cv_sym, HDZ, Hc1|apply cv_sym, HDZ', Hc2].
Qed.

Lemma sem_cumul_fun : forall f1 f2 x A1 B1 A2 B2 C1 D1 C2 D2s k,
  rel_at f1 f2 (TPi x A1 B1) (TPi x A2 B2) ->
  ty_rel k (TPi x C1 D1) (TPi x C2 D2s) ->
  universe_le C1 A1 -> universe_le B1 D1 -> universe_le C2 A2 -> universe_le B2 D2s ->
  rel_at f1 f2 (TPi x C1 D1) (TPi x C2 D2s).
Proof.
  intros f1 f2 x A1 B1 A2 B2 C1 D1 C2 D2s k Hf HT HCA1 HBD1 HCA2 HBD2.
  destruct (universe_le_ule _ _ (ul_pi x HCA1 HBD1)) as [n Hn].
  destruct Hf as [j [R [HR Hf]]]; destruct HT as [S HS].
  exists k, S; split; [exact HS|].
  eapply (ule_incl n); [exact Hn|exact (ul_pi x HCA2 HBD2)|exact HR|exact HS|exact Hf].
Qed.
