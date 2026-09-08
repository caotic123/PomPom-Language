From Stdlib Require Import Program.Equality List Arith Lia PeanoNat.
Import ListNotations.
Require Import TypeRulesCore Progress ConversionInversion TypingSubstitution.
Import ListNotations TypeRulesCore.

Inductive mu_state (G : ctx) (c : term) : term -> term -> Prop :=
| ms_mui : forall R i z,
    check G z (TInterp (TApp R i) (TMuI R)) ->
    mu_state G c (TApp (TMuI R) i) z
| ms_mus : forall E Sf i ys,
    check G c (Label E) ->
    check G ys (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
    mu_state G c (TApp (SigMu E Sf) i) ys.

Lemma conv_mui_mus_absurd_tmp : forall R i E Sf j,
  conv (TApp (TMuI R) i) (TApp (SigMu E Sf) j) -> False.
Proof.
 intros R i E Sf j H. assert (Heq : HMuIApp = HMuSApp).
 { eapply conv_whd; [exact H|apply whd_shape;constructor|apply whd_shape;constructor]. }
 discriminate Heq.
Qed.
Lemma conv_mus_mui_absurd_tmp : forall E Sf j R i,
  conv (TApp (SigMu E Sf) j) (TApp (TMuI R) i) -> False.
Proof.
 intros E Sf j R i H. assert (Heq : HMuSApp = HMuIApp).
 { eapply conv_whd; [exact H|apply whd_shape;constructor|apply whd_shape;constructor]. }
 discriminate Heq.
Qed.

Inductive mu_rep : term -> Prop :=
| mr_mui : forall R i, mu_rep (TApp (TMuI R) i)
| mr_mus : forall E Sf i, mu_rep (TApp (SigMu E Sf) i)
| mr_carrier : forall E Sf i, mu_rep (TApp (Carrier E Sf) i).

Inductive mu_path (G : ctx) : term -> term -> Prop :=
| mp_conv : forall A B, mu_rep A -> mu_rep B -> conv A B -> mu_path G A B
| mp_forget : forall E Sf i IT,
    check G IT (TSort 0) -> check G E TEnumU ->
    check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check G i IT ->
    mu_path G (TApp (SigMu E Sf) i) (TApp (Carrier E Sf) i)
| mp_sig : forall S1 S2 i IT E Phi1 Phi2,
    check G IT (TSort 0) -> check G E TEnumU ->
    check G S1 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check G S2 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 -> eval (labels (TApp S2 i)) Phi2 ->
    spine_incl Phi1 Phi2 -> check G i IT ->
    mu_path G (TApp (SigMu E S1) i) (TApp (SigMu E S2) i)
| mp_trans : forall A B C, mu_path G A B -> mu_path G B C -> mu_path G A C.

Lemma mui_payload_transport_tmp : forall G R0 R1 i0 i1 xs,
  check G xs (TInterp (TApp R0 i0) (TMuI R0)) ->
  conv R0 R1 -> conv i0 i1 ->
  check G xs (TInterp (TApp R1 i1) (TMuI R1)).
Proof.
 intros G R0 R1 i0 i1 xs Hxs HR Hi. eapply ch_expand.
 - apply cv_sym, cv_interp.
   + apply cv_app; [exact HR|exact Hi].
   + apply cv_mui; exact HR.
 - exact Hxs.
Qed.

Lemma mu_factor_tmp : forall G A B, sub G A B -> forall U, mu_rep U -> conv B U ->
 exists V, mu_rep V /\ conv A V /\ mu_path G V U.
Proof.
 intros G A B Hsub. induction Hsub; intros U HU HBU.
 - exists U. split; [exact HU|]. split.
   + eapply cv_trans; eassumption.
   + apply mp_conv; [exact HU|exact HU|apply cv_refl].
 - destruct (IHHsub2 U HU HBU) as [U2 [HU2 [HBU2 HP2]]].
   destruct (IHHsub1 U2 HU2 HBU2) as [U1 [HU1 [HA1 HP1]]].
   exists U1. repeat split; try assumption. eapply mp_trans; eassumption.
 - exfalso. destruct HU as [R0 i0 | E0 Sf0 i0 | E0 Sf0 i0].
   + assert (Heq : HSort = HMuIApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|apply whd_shape; constructor]. }
     discriminate Heq.
   + assert (Heq : HSort = HMuSApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|apply whd_shape; constructor]. }
     discriminate Heq.
   + assert (Heq : HSort = HMuIApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|unfold Carrier; apply whd_shape; constructor]. }
     discriminate Heq.
 - exfalso. destruct HU as [R0 i0 | E0 Sf0 i0 | E0 Sf0 i0].
   + assert (Heq : HPi = HMuIApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|apply whd_shape; constructor]. }
     discriminate Heq.
   + assert (Heq : HPi = HMuSApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|apply whd_shape; constructor]. }
     discriminate Heq.
   + assert (Heq : HPi = HMuIApp).
     { eapply conv_whd; [exact HBU|apply whd_shape; constructor|unfold Carrier; apply whd_shape; constructor]. }
     discriminate Heq.
 - exists (TApp (SigMu E Sf) i). split; [apply mr_mus|]. split; [apply cv_refl|].
   eapply mp_trans.
   + apply mp_forget with (IT:=IT); assumption.
   + apply mp_conv; [apply mr_carrier|exact HU|exact HBU].
 - exists (TApp (SigMu E S1) i). split; [apply mr_mus|]. split; [apply cv_refl|].
   eapply mp_trans.
   + apply mp_sig with (IT:=IT) (Phi1:=Phi1) (Phi2:=Phi2).
     * exact H.
     * exact H0.
     * exact H1.
     * exact H2.
     * exact H3.
     * exact H4.
     * exact H5.
     * exact H6.
     * exact H7.
   + apply mp_conv; [apply mr_mus|exact HU|exact HBU].
Qed.

Lemma sig_to_carrier_pair_tmp : forall G E Sf i c xs IT,
  check G IT (TSort 0) -> check G E TEnumU ->
  check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  check G i IT -> check G c (Label E) ->
  check G xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
  check G (TPair c xs)
    (TInterp
      (TApp (TLam (Full (lift 1 0 E)
        (TApp (lift 1 0 Sf) (TVar 0)))) i)
      (TMuI (TLam (Full (lift 1 0 E)
        (TApp (lift 1 0 Sf) (TVar 0)))))).
Proof.
  intros G E Sf i c xs IT HIT HE HSf Hi Hc Hxs.
  set (R := TLam (Full (lift 1 0 E)
    (TApp (lift 1 0 Sf) (TVar 0)))).
  assert (Hred : conv
      (TInterp (TApp R i) (TMuI R))
      (TSigma (TEnumT E)
        (TInterp (TApp (lift 1 0 (branches (TApp Sf i))) (TVar 0))
          (lift 1 0 (Carrier E Sf))))).
  { unfold R.
    assert (HbetaD : conv
        (TApp (TLam (Full (lift 1 0 E)
          (TApp (lift 1 0 Sf) (TVar 0)))) i)
        (TIChoice E (branches (TApp Sf i)))).
    { eapply cv_trans; [apply cv_step, st_beta |].
      cbn [Full subst branches].
      rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl.
      rewrite _tmp_commute.lift_zero_id_local.
      repeat rewrite subst_lift_zero. apply cv_refl. }
    eapply cv_trans.
    - apply cv_interp; [exact HbetaD | apply cv_refl].
    - apply cv_step, st_interp_choice. }
  eapply ch_expand; [exact Hred |].
  apply ch_pair with (A := TEnumT E)
    (B := TInterp (TApp (lift 1 0 (branches (TApp Sf i))) (TVar 0))
             (lift 1 0 (Carrier E Sf))).
  - exact Hc.
  - cbn [subst branches].
    rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl.
    rewrite _tmp_commute.lift_zero_id_local.
    repeat rewrite subst_lift_zero. exact Hxs.
Qed.

Lemma sigmu_edge_payload_typed_tmp : forall G E S1 S2 i IT Phi1 Phi2 c xs,
  check G IT (TSort 0) -> check G E TEnumU ->
  check G S1 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  check G S2 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
       (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
  eval (labels (TApp S1 i)) Phi1 -> eval (labels (TApp S2 i)) Phi2 ->
  spine_incl Phi1 Phi2 -> check G i IT ->
  check G xs (TInterp (TApp (branches (TApp S1 i)) c) (Carrier E S1)) ->
  check G xs (TInterp (TApp (branches (TApp S2 i)) c) (Carrier E S2)).
Proof.
  intros G E S1 S2 i IT Phi1 Phi2 c xs HIT HE HS1 HS2 Hb
    He1 He2 Hincl Hi Hxs.
  assert (Hbranch : conv (branches (TApp S1 i)) (branches (TApp S2 i))).
  { assert (H1 : conv
        (TApp (TLam (branches (TApp (lift 1 0 S1) (TVar 0)))) i)
        (branches (TApp S1 i))).
    { eapply cv_trans; [apply cv_step, st_beta|].
      cbn [subst lift branches]. rewrite subst_lift_zero.
      rewrite _tmp_commute.lift_zero_id_local. apply cv_refl. }
    assert (H2 : conv
        (TApp (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) i)
        (branches (TApp S2 i))).
    { eapply cv_trans; [apply cv_step, st_beta|].
      cbn [subst lift branches]. rewrite subst_lift_zero.
      rewrite _tmp_commute.lift_zero_id_local. apply cv_refl. }
    eapply cv_trans; [apply cv_sym; exact H1|].
    eapply cv_trans; [apply cv_app; [exact Hb|apply cv_refl]|exact H2]. }
  assert (Hcarrier : conv (Carrier E S1) (Carrier E S2)).
  { unfold Carrier, Full. apply cv_mui, cv_lam, cv_ichoice.
    - apply cv_refl.
    - assert (Hblift : conv
          (lift 1 0 (TLam (branches (TApp (lift 1 0 S1) (TVar 0)))))
          (lift 1 0 (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))))).
      { apply conv_lift_typing; exact Hb. }
      assert (Hbody : conv
          (branches (TApp (lift 1 0 S1) (TVar 0)))
          (branches (TApp (lift 1 0 S2) (TVar 0)))).
      { eapply cv_trans.
        - apply cv_sym. eapply cv_trans; [apply cv_step, st_beta|].
          rewrite _tmp_eta_cancel.subst_eta_beta_cancel_gen; apply cv_refl.
        - eapply cv_trans; [apply cv_app; [exact Hblift|apply cv_refl]|].
          eapply cv_trans; [apply cv_step, st_beta|].
          rewrite _tmp_eta_cancel.subst_eta_beta_cancel_gen; apply cv_refl. }
      exact Hbody. }
  eapply ch_expand.
  - apply cv_sym, cv_interp; [apply cv_app; [exact Hbranch|apply cv_refl]|exact Hcarrier].
  - exact Hxs.
Qed.

Lemma in_origin_aux_tmp : forall G t T, check G t T -> forall x, t = TIn x ->
  (exists R i IT,
     check G IT (TSort 0) /\
     check G R (TPi IT (TIDesc (lift 1 0 IT))) /\
     check G i IT /\
     check G x (TInterp (TApp R i) (TMuI R)) /\
     sub G (TApp (TMuI R) i) T) \/
  (exists Sf i IT E Phi c xs,
     x = TPair c xs /\
     check G IT (TSort 0) /\ check G E TEnumU /\
     check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) /\
     check G i IT /\ check G c (Label E) /\
     eval (labels (TApp Sf i)) Phi /\ spine_mem c Phi /\
     check G xs (TInterp (TApp (branches (TApp Sf i)) c)
       (Carrier E Sf)) /\
     sub G (TApp (SigMu E Sf) i) T).
Proof.
  intros G t T HC. induction HC; intros x0 Eq; try discriminate; inversion Eq; subst.
  - inversion H.
  - destruct (IHHC x0 eq_refl) as [K|K]; [left; destruct K as [R [i [IT [HIT [HR [Hi [Hx Hsub]]]]]]];
      exists R,i,IT; repeat split; try assumption; eapply su_trans; eassumption |
    right; destruct K as [Sf [i [IT [E [Phi [c [xs [Hxs [HIT [HE [HSf [Hi [Hc [HL [Hm [Hx Hsub]]]]]]]]]]]]]]]];
      exists Sf,i,IT,E,Phi,c,xs; repeat split; try assumption; eapply su_trans; eassumption].
  - destruct (IHHC x0 eq_refl) as [K|K]; [left; destruct K as [R [i [IT [HIT [HR [Hi [Hx Hsub]]]]]]];
      exists R,i,IT; repeat split; try assumption; eapply su_trans; [exact Hsub|apply su_conv; exact (cv_sym H)] |
    right; destruct K as [Sf [i [IT [E [Phi [c [xs [Hxs [HIT [HE [HSf [Hi [Hc [HL [Hm [Hx Hsub]]]]]]]]]]]]]]]];
      exists Sf,i,IT,E,Phi,c,xs; repeat split; try assumption; eapply su_trans; [exact Hsub|apply su_conv; exact (cv_sym H)]].
  - left; exists R,i,IT; repeat split; eauto using su_conv, cv_refl.
  - right; exists Sf,i,IT,E,Phi,c,xs; repeat split; eauto using su_conv, cv_refl.
  all: eauto.
Qed.

Lemma tin_synth_absurd_nophi : forall G x A, synth G (TIn x) A -> False.
Proof.
  intros G x A H.
  inversion H; subst.
  all: try discriminate.
Qed.

Lemma mui_edge_nophi : forall G R0 R1 i0 i1 z,
  conv (TApp (TMuI R0) i0) (TApp (TMuI R1) i1) ->
  check G z (TInterp (TApp R0 i0) (TMuI R0)) ->
  check G z (TInterp (TApp R1 i1) (TMuI R1)).
Proof.
  intros G R0 R1 i0 i1 z H Hx.
  destruct (conv_muiapp_components _ _ _ _ H) as [HR Hi].
  eapply mui_payload_transport_tmp; eassumption.
Qed.

Lemma lift_branch_conv_nophi : forall S0 S1 i0 i1,
  conv S0 S1 -> conv i0 i1 ->
  conv (branches (TApp S0 i0)) (branches (TApp S1 i1)).
Proof.
  intros. unfold branches. apply cv_fst, cv_app; assumption.
Qed.

Lemma lifted_branch_family_conv_nophi : forall S0 S1,
  conv S0 S1 ->
  conv (TLam (branches (TApp (lift 1 0 S0) (TVar 0))))
       (TLam (branches (TApp (lift 1 0 S1) (TVar 0)))).
Proof.
  intros S0 S1 HS.
  apply cv_lam, cv_fst, cv_app.
  - apply fconv_conv, ErasureCounterexample.fconv_lift_parent, conv_fconv; exact HS.
  - apply cv_refl.
Qed.

Lemma carrier_conv_nophi : forall E0 E1 S0 S1,
  conv E0 E1 -> conv S0 S1 -> conv (Carrier E0 S0) (Carrier E1 S1).
Proof.
  intros E0 E1 S0 S1 HE HS.
  unfold Carrier, Full.
  apply cv_mui, cv_lam, cv_ichoice.
  - apply fconv_conv, ErasureCounterexample.fconv_lift_parent, conv_fconv; exact HE.
  - apply cv_fst, cv_app.
    + apply fconv_conv, ErasureCounterexample.fconv_lift_parent, conv_fconv; exact HS.
    + apply cv_refl.
Qed.

Lemma sig_payload_conv_nophi : forall E0 E1 S0 S1 i0 i1 c,
  conv E0 E1 -> conv S0 S1 -> conv i0 i1 ->
  conv (TInterp (TApp (branches (TApp S0 i0)) c) (Carrier E0 S0))
       (TInterp (TApp (branches (TApp S1 i1)) c) (Carrier E1 S1)).
Proof.
  intros E0 E1 S0 S1 i0 i1 c HE HS Hi.
  apply cv_interp.
  - apply cv_app.
    + apply lift_branch_conv_nophi; assumption.
    + apply cv_refl.
  - apply carrier_conv_nophi; assumption.
Qed.

Lemma mus_edge_nophi : forall G E0 S0 i0 E1 S1 i1 c z,
  conv (TApp (SigMu E0 S0) i0) (TApp (SigMu E1 S1) i1) ->
  check G c (Label E0) ->
  check G z (TInterp (TApp (branches (TApp S0 i0)) c) (Carrier E0 S0)) ->
  check G c (Label E1) /\
  check G z (TInterp (TApp (branches (TApp S1 i1)) c) (Carrier E1 S1)).
Proof.
  intros G E0 S0 i0 E1 S1 i1 c z H Hc Hz.
  destruct (conv_sigmuapp_components _ _ _ _ _ _ H) as [HE [HS Hi]].
  split.
  - unfold Label in *. eapply ch_expand; [apply cv_sym, cv_enumt; exact HE|exact Hc].
  - eapply ch_expand; [apply cv_sym, sig_payload_conv_nophi; eassumption|exact Hz].
Qed.

Inductive rigid_mu : term -> Prop :=
| rk_mui : forall R i, rigid_mu (TApp (TMuI R) i)
| rk_carrier : forall E Sf i, rigid_mu (TApp (Carrier E Sf) i).
Lemma conv_carrier_mus_absurd_nophi : forall E Sf i E' S' j,
 conv (TApp (Carrier E Sf) i) (TApp (SigMu E' S') j) -> False.
Proof. intros; unfold Carrier in H; eapply conv_mui_mus_absurd_tmp; eassumption. Qed.
Lemma conv_mus_carrier_absurd_nophi : forall E Sf i E' S' j,
 conv (TApp (SigMu E Sf) i) (TApp (Carrier E' S') j) -> False.
Proof. intros; unfold Carrier in H; eapply conv_mus_mui_absurd_tmp; eassumption. Qed.
Lemma rigid_path_nophi : forall G A B, rigid_mu A -> mu_path G A B -> rigid_mu B.
Proof.
 intros G A B HA Hp. dependent induction Hp.
 - destruct HA as [R0 i0 | E0 S0 i0].
   + destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
     * apply rk_mui.
     * exfalso. eapply conv_mui_mus_absurd_tmp; eassumption.
     * apply rk_carrier.
   + unfold Carrier in *. destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
     * apply rk_mui.
     * exfalso. eapply conv_carrier_mus_absurd_nophi; eassumption.
     * apply rk_carrier.
 - inversion HA.
 - inversion HA.
 - apply IHHp2. apply IHHp1. exact HA.
Qed.

Lemma test_rigid : forall G c A B z,
 rigid_mu A -> mu_state G c A z -> mu_path G A B -> rigid_mu B -> mu_state G c B z.
Proof.
 intros G c A B z HA Hst Hp HB. dependent induction Hp.
 - destruct HA as [R0 i0 | E0 S0 i0].
   + inversion Hst; subst. destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
     * apply ms_mui. eapply mui_edge_nophi; [eassumption|eassumption].
     * exfalso. eapply conv_mui_mus_absurd_tmp; eassumption.
     * unfold Carrier in *. apply ms_mui. eapply mui_edge_nophi; [eassumption|eassumption].
   + unfold Carrier in *. inversion Hst; subst.
     * destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
       -- apply ms_mui. eapply mui_edge_nophi; [eassumption|eassumption].
       -- exfalso. eapply conv_carrier_mus_absurd_nophi; eassumption.
       -- apply ms_mui. eapply mui_edge_nophi; [eassumption|eassumption].
 - inversion HA.
 - inversion HA.
 - assert (HBmid : rigid_mu B) by (apply (rigid_path_nophi G A B); assumption).
   assert (Hmid : mu_state G c B z).
   { eapply IHHp1; eassumption. }
   eapply IHHp2; eassumption.
Qed.

Inductive sig_state2 (G : ctx) (c ys : term) : term -> Prop :=
| ss2_mus : forall E Sf i,
    check G c (Label E) ->
    check G ys (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
    sig_state2 G c ys (TApp (SigMu E Sf) i)
| ss2_mui : forall R i,
    check G (TPair c ys) (TInterp (TApp R i) (TMuI R)) ->
    sig_state2 G c ys (TApp (TMuI R) i)
| ss2_carrier : forall E Sf i,
    check G (TPair c ys) (TInterp (TApp (TLam (Full (lift 1 0 E) (TApp (lift 1 0 Sf) (TVar 0)))) i)
      (TMuI (TLam (Full (lift 1 0 E) (TApp (lift 1 0 Sf) (TVar 0)))))) ->
    sig_state2 G c ys (TApp (Carrier E Sf) i).

Lemma sig_state2_path : forall G c ys A B,
  sig_state2 G c ys A -> mu_path G A B -> sig_state2 G c ys B.
Proof.
  intros G c ys A B Hst Hp. dependent induction Hp.
  - destruct Hst as [E0 Sf0 i0 Hc Hx | R0 i0 Hx | E0 Sf0 i0 Hx].
    + destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
      * exfalso. eapply conv_mus_mui_absurd_tmp; eassumption.
      * pose proof (mus_edge_nophi _ _ _ _ _ _ _ _ _ H1 Hc Hx) as [Hc' Hx']. apply ss2_mus; assumption.
      * exfalso. eapply conv_mus_carrier_absurd_nophi; eassumption.
    + destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
      * apply ss2_mui. eapply mui_edge_nophi; eassumption.
      * exfalso. eapply conv_mui_mus_absurd_tmp; eassumption.
      * apply ss2_carrier. unfold Carrier in H1. eapply mui_edge_nophi; eassumption.
    + destruct H0 as [R1 i1 | E1 S1 i1 | E1 S1 i1].
      * apply ss2_mui. unfold Carrier in H1. eapply mui_edge_nophi; eassumption.
      * exfalso. eapply conv_carrier_mus_absurd_nophi; eassumption.
      * apply ss2_carrier. unfold Carrier in H1. eapply mui_edge_nophi; eassumption.
  - inversion Hst as [E0 Sf0 i0 Hc Hx | R0 i0 Hx | E0 Sf0 i0 Hx].
    apply ss2_carrier. unfold Carrier. apply sig_to_carrier_pair_tmp with (G:=G) (E:=E) (Sf:=Sf) (i:=i) (c:=c) (xs:=ys) (IT:=IT); assumption.
  - inversion Hst as [E0 Sf0 i0 Hc Hx | R0 i0 Hx | E0 Sf0 i0 Hx].
    apply ss2_mus.
    * exact Hc.
    * apply (sigmu_edge_payload_typed_tmp G E S1 S2 i IT Phi1 Phi2 c ys).
      -- exact H.
      -- exact H0.
      -- exact H1.
      -- exact H2.
      -- exact H3.
      -- exact H4.
      -- exact H5.
      -- exact H6.
      -- exact H7.
      -- exact Hx.
  - apply IHHp2. apply IHHp1. exact Hst.
Qed.

Lemma mui_in_payload_same_pres : forall G R i xs IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G i IT ->
  check G (TIn xs) (TApp (TMuI R) i) ->
  check G xs (TInterp (TApp R i) (TMuI R)).
Proof.
  intros G R i xs IT HIT HR Hi HIn.
  destruct (in_origin_aux_tmp G (TIn xs) (TApp (TMuI R) i) HIn xs eq_refl)
    as [K|K].
  - destruct K as (R0 & i0 & IT0 & HIT0 & HR0 & Hi0 & Hx & Hsub).
    destruct (mu_factor_tmp G (TApp (TMuI R0) i0) (TApp (TMuI R) i)
      Hsub (TApp (TMuI R) i) (mr_mui _ _) (cv_refl _))
      as [V [HV [HAV Hpath]]].
    assert (HP : mu_path G (TApp (TMuI R0) i0) V).
    { apply mp_conv; [apply mr_mui|exact HV|exact HAV]. }
    assert (Hfull : mu_path G (TApp (TMuI R0) i0) (TApp (TMuI R) i)).
    { eapply mp_trans; eassumption. }
    assert (Hz : mu_state G (TVar 0) (TApp (TMuI R) i) xs).
    { eapply (test_rigid G (TVar 0) (TApp (TMuI R0) i0)
          (TApp (TMuI R) i) xs).
      - apply rk_mui.
      - apply ms_mui; exact Hx.
      - exact Hfull.
      - apply rk_mui.
    }
    inversion Hz; subst; assumption.
  - destruct K as (Sf & i0 & IT0 & E & Phi & c & xs0 & Heq & HIT0 & HE & HSf & Hi0 & Hc & HL & Hm & Hxs & Hsub).
    subst xs.
    destruct (mu_factor_tmp G (TApp (SigMu E Sf) i0) (TApp (TMuI R) i)
      Hsub (TApp (TMuI R) i) (mr_mui _ _) (cv_refl _))
      as [V [HV [HAV Hpath]]].
    assert (HP : mu_path G (TApp (SigMu E Sf) i0) V).
    { apply mp_conv; [apply mr_mus|exact HV|exact HAV]. }
    assert (Hfull : mu_path G (TApp (SigMu E Sf) i0) (TApp (TMuI R) i)).
    { eapply mp_trans; eassumption. }
    assert (Hstart : sig_state2 G c xs0 (TApp (SigMu E Sf) i0)).
    { apply ss2_mus; assumption. }
    assert (Hz : sig_state2 G c xs0 (TApp (TMuI R) i)).
    { eapply sig_state2_path; eassumption. }
    inversion Hz; subst; assumption.
Qed.

Lemma mus_in_pair_payload_same_pres : forall G Sf i a xs IT E,
  check G IT (TSort 0) -> check G E TEnumU ->
  check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  check G i IT ->
  check G (TIn (TPair a xs)) (TApp (SigMu E Sf) i) ->
  check G xs
    (TInterp (TApp (branches (TApp Sf i)) a) (Carrier E Sf)).
Proof.
  intros G Sf i a xs IT E HIT HE HSf Hi HIn.
  destruct (SignatureLemmas.in_pair_origin_aux G (TIn (TPair a xs)) (TApp (SigMu E Sf) i)
      HIn a xs eq_refl) as [KM|KS].
  - destruct KM as [R0 [i0 [IT0 [HIT0 [HR0 [Hi0 [Hpair Hsub]]]]]]].
    exfalso.
    destruct (sub_transport G (TApp (TMuI R0) i0) (TApp (SigMu E Sf) i)
      Hsub (TApp (SigMu E Sf) i) HMuSApp (cv_refl _)
      (whd_shape _ _ (hs_musapp (TPair E Sf) i))) as
      [Hconv | [[Htag [U [Hconv1 HU]]] | [Htag [U [Hconv2 HU]]]]].
    + eapply conv_mui_mus_absurd_tmp; eassumption.
    + destruct Htag as [Htag | [Htag | Htag]].
      * discriminate Htag.
      * discriminate Htag.
      * assert (Heq : HMuIApp = HMuSApp).
        { eapply conv_whd; [exact Hconv1 | apply whd_shape; constructor | exact HU]. }
        discriminate Heq.
    + discriminate Htag.
  - destruct KS as [S0 [i0 [IT0 [E0 [Phi0
      [HIT0 [HE0 [HS0 [Hi0 [Hc [HL [Hm [Hxs Hsub]]]]]]]]]]]]].
    destruct (mu_factor_tmp G (TApp (SigMu E0 S0) i0) (TApp (SigMu E Sf) i)
      Hsub (TApp (SigMu E Sf) i) (mr_mus _ _ _) (cv_refl _))
      as [V [HV [HAV Hpath]]].
    assert (HP : mu_path G (TApp (SigMu E0 S0) i0) V).
    { apply mp_conv; [apply mr_mus|exact HV|exact HAV]. }
    assert (Hfull : mu_path G (TApp (SigMu E0 S0) i0) (TApp (SigMu E Sf) i)).
    { eapply mp_trans; eassumption. }
    assert (Hstart : sig_state2 G a xs (TApp (SigMu E0 S0) i0)).
    { apply ss2_mus; assumption. }
    assert (Hz : sig_state2 G a xs (TApp (SigMu E Sf) i)).
    { eapply sig_state2_path; eassumption. }
    inversion Hz; subst; assumption.
Qed.
