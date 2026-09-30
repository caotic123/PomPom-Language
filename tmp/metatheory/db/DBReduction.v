Require Export ProofDB.DBCommutation.

Lemma red_star_TPi : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TPi a0 a1) (TPi b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TPi z a1)); [|exact H0].
    intros z w Hzw. now apply red_TPi_A. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TPi b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TPi_B.
Qed.

Lemma red_star_TLam : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TLam a0) (TLam b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TLam z)); [|exact H0].
    intros z w Hzw. now apply red_TLam_b.
Qed.

Lemma red_star_TApp : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TApp a0 a1) (TApp b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TApp z a1)); [|exact H0].
    intros z w Hzw. now apply red_TApp_f. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TApp b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TApp_a.
Qed.

Lemma red_star_TSigma : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TSigma a0 a1) (TSigma b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TSigma z a1)); [|exact H0].
    intros z w Hzw. now apply red_TSigma_A. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TSigma b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TSigma_B.
Qed.

Lemma red_star_TPair : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TPair a0 a1) (TPair b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TPair z a1)); [|exact H0].
    intros z w Hzw. now apply red_TPair_a. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TPair b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TPair_b.
Qed.

Lemma red_star_TFst : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TFst a0) (TFst b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TFst z)); [|exact H0].
    intros z w Hzw. now apply red_TFst_p.
Qed.

Lemma red_star_TSnd : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TSnd a0) (TSnd b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TSnd z)); [|exact H0].
    intros z w Hzw. now apply red_TSnd_p.
Qed.

Lemma red_star_TConsE : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TConsE a0 a1) (TConsE b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TConsE z a1)); [|exact H0].
    intros z w Hzw. now apply red_TConsE_tag. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TConsE b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TConsE_E.
Qed.

Lemma red_star_TEnumT : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TEnumT a0) (TEnumT b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TEnumT z)); [|exact H0].
    intros z w Hzw. now apply red_TEnumT_E.
Qed.

Lemma red_star_TESucc : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TESucc a0) (TESucc b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TESucc z)); [|exact H0].
    intros z w Hzw. now apply red_TESucc_n.
Qed.

Lemma red_star_TEPi : forall k a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TEPi k a0 a1) (TEPi k b0 b1).
Proof.
  intros k a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TEPi k z a1)); [|exact H0].
    intros z w Hzw. now apply red_TEPi_E. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TEPi k b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TEPi_P.
Qed.

Lemma red_star_TSwitch : forall k a0 b0 a1 b1 a2 b2 a3 b3, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction (TSwitch k a0 a1 a2 a3) (TSwitch k b0 b1 b2 b3).
Proof.
  intros k a0 b0 a1 b1 a2 b2 a3 b3 H0 H1 H2 H3.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TSwitch k z a1 a2 a3)); [|exact H0].
    intros z w Hzw. now apply red_TSwitch_E. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TSwitch k b0 z a2 a3)); [|exact H1].
    intros z w Hzw. now apply red_TSwitch_P. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TSwitch k b0 b1 z a3)); [|exact H2].
    intros z w Hzw. now apply red_TSwitch_p. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TSwitch k b0 b1 b2 z)); [|exact H3].
    intros z w Hzw. now apply red_TSwitch_e.
Qed.

Lemma red_star_TIDesc : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TIDesc a0) (TIDesc b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIDesc z)); [|exact H0].
    intros z w Hzw. now apply red_TIDesc_IT.
Qed.

Lemma red_star_TIVar : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TIVar a0) (TIVar b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIVar z)); [|exact H0].
    intros z w Hzw. now apply red_TIVar_i.
Qed.

Lemma red_star_TIProd : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TIProd a0 a1) (TIProd b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIProd z a1)); [|exact H0].
    intros z w Hzw. now apply red_TIProd_A. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIProd b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TIProd_B.
Qed.

Lemma red_star_TIPi : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TIPi a0 a1) (TIPi b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIPi z a1)); [|exact H0].
    intros z w Hzw. now apply red_TIPi_A. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIPi b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TIPi_D.
Qed.

Lemma red_star_TISig : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TISig a0 a1) (TISig b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TISig z a1)); [|exact H0].
    intros z w Hzw. now apply red_TISig_A. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TISig b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TISig_D.
Qed.

Lemma red_star_TIChoice : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TIChoice a0 a1) (TIChoice b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIChoice z a1)); [|exact H0].
    intros z w Hzw. now apply red_TIChoice_E. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIChoice b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TIChoice_D.
Qed.

Lemma red_star_TInterp : forall a0 b0 a1 b1 a2 b2, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction (TInterp a0 a1 a2) (TInterp b0 b1 b2).
Proof.
  intros a0 b0 a1 b1 a2 b2 H0 H1 H2.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInterp z a1 a2)); [|exact H0].
    intros z w Hzw. now apply red_TInterp_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInterp b0 z a2)); [|exact H1].
    intros z w Hzw. now apply red_TInterp_D. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TInterp b0 b1 z)); [|exact H2].
    intros z w Hzw. now apply red_TInterp_X.
Qed.

Lemma red_star_TMuI : forall a0 b0 a1 b1, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction (TMuI a0 a1) (TMuI b0 b1).
Proof.
  intros a0 b0 a1 b1 H0 H1.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TMuI z a1)); [|exact H0].
    intros z w Hzw. now apply red_TMuI_IT. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TMuI b0 z)); [|exact H1].
    intros z w Hzw. now apply red_TMuI_D.
Qed.

Lemma red_star_TIn : forall a0 b0, rtc reduction a0 b0 -> rtc reduction (TIn a0) (TIn b0).
Proof.
  intros a0 b0 H0.
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIn z)); [|exact H0].
    intros z w Hzw. now apply red_TIn_x.
Qed.

Lemma red_star_TInd : forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction a4 b4 -> rtc reduction a5 b5 -> rtc reduction (TInd a0 a1 a2 a3 a4 a5) (TInd b0 b1 b2 b3 b4 b5).
Proof.
  intros a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 H0 H1 H2 H3 H4 H5.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd z a1 a2 a3 a4 a5)); [|exact H0].
    intros z w Hzw. now apply red_TInd_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd b0 z a2 a3 a4 a5)); [|exact H1].
    intros z w Hzw. now apply red_TInd_D. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd b0 b1 z a3 a4 a5)); [|exact H2].
    intros z w Hzw. now apply red_TInd_P. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd b0 b1 b2 z a4 a5)); [|exact H3].
    intros z w Hzw. now apply red_TInd_s. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd b0 b1 b2 b3 z a5)); [|exact H4].
    intros z w Hzw. now apply red_TInd_i. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TInd b0 b1 b2 b3 b4 z)); [|exact H5].
    intros z w Hzw. now apply red_TInd_x.
Qed.

Lemma red_star_TIAll : forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction a4 b4 -> rtc reduction (TIAll a0 a1 a2 a3 a4) (TIAll b0 b1 b2 b3 b4).
Proof.
  intros a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 H0 H1 H2 H3 H4.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIAll z a1 a2 a3 a4)); [|exact H0].
    intros z w Hzw. now apply red_TIAll_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIAll b0 z a2 a3 a4)); [|exact H1].
    intros z w Hzw. now apply red_TIAll_D. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIAll b0 b1 z a3 a4)); [|exact H2].
    intros z w Hzw. now apply red_TIAll_X. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TIAll b0 b1 b2 z a4)); [|exact H3].
    intros z w Hzw. now apply red_TIAll_x. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TIAll b0 b1 b2 b3 z)); [|exact H4].
    intros z w Hzw. now apply red_TIAll_P.
Qed.

Lemma red_star_THyps : forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction a4 b4 -> rtc reduction a5 b5 -> rtc reduction (THyps a0 a1 a2 a3 a4 a5) (THyps b0 b1 b2 b3 b4 b5).
Proof.
  intros a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 H0 H1 H2 H3 H4 H5.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps z a1 a2 a3 a4 a5)); [|exact H0].
    intros z w Hzw. now apply red_THyps_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps b0 z a2 a3 a4 a5)); [|exact H1].
    intros z w Hzw. now apply red_THyps_D. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps b0 b1 z a3 a4 a5)); [|exact H2].
    intros z w Hzw. now apply red_THyps_X. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps b0 b1 b2 z a4 a5)); [|exact H3].
    intros z w Hzw. now apply red_THyps_P. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps b0 b1 b2 b3 z a5)); [|exact H4].
    intros z w Hzw. now apply red_THyps_h. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => THyps b0 b1 b2 b3 b4 z)); [|exact H5].
    intros z w Hzw. now apply red_THyps_x.
Qed.

Lemma red_star_TClose : forall a0 b0 a1 b1 a2 b2, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction (TClose a0 a1 a2) (TClose b0 b1 b2).
Proof.
  intros a0 b0 a1 b1 a2 b2 H0 H1 H2.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TClose z a1 a2)); [|exact H0].
    intros z w Hzw. now apply red_TClose_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TClose b0 z a2)); [|exact H1].
    intros z w Hzw. now apply red_TClose_F. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TClose b0 b1 z)); [|exact H2].
    intros z w Hzw. now apply red_TClose_G.
Qed.

Lemma red_star_TCloseCase : forall k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction a4 b4 -> rtc reduction a5 b5 -> rtc reduction a6 b6 -> rtc reduction (TCloseCase k a0 a1 a2 a3 a4 a5 a6) (TCloseCase k b0 b1 b2 b3 b4 b5 b6).
Proof.
  intros k a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 H0 H1 H2 H3 H4 H5 H6.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k z a1 a2 a3 a4 a5 a6)); [|exact H0].
    intros z w Hzw. now apply red_TCloseCase_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 z a2 a3 a4 a5 a6)); [|exact H1].
    intros z w Hzw. now apply red_TCloseCase_F. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 b1 z a3 a4 a5 a6)); [|exact H2].
    intros z w Hzw. now apply red_TCloseCase_G. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 b1 b2 z a4 a5 a6)); [|exact H3].
    intros z w Hzw. now apply red_TCloseCase_i. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 b1 b2 b3 z a5 a6)); [|exact H4].
    intros z w Hzw. now apply red_TCloseCase_Q. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 b1 b2 b3 b4 z a6)); [|exact H5].
    intros z w Hzw. now apply red_TCloseCase_b. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseCase k b0 b1 b2 b3 b4 b5 z)); [|exact H6].
    intros z w Hzw. now apply red_TCloseCase_x.
Qed.

Lemma red_star_TCloseInd : forall a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6, rtc reduction a0 b0 -> rtc reduction a1 b1 -> rtc reduction a2 b2 -> rtc reduction a3 b3 -> rtc reduction a4 b4 -> rtc reduction a5 b5 -> rtc reduction a6 b6 -> rtc reduction (TCloseInd a0 a1 a2 a3 a4 a5 a6) (TCloseInd b0 b1 b2 b3 b4 b5 b6).
Proof.
  intros a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 H0 H1 H2 H3 H4 H5 H6.
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd z a1 a2 a3 a4 a5 a6)); [|exact H0].
    intros z w Hzw. now apply red_TCloseInd_IT. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 z a2 a3 a4 a5 a6)); [|exact H1].
    intros z w Hzw. now apply red_TCloseInd_G. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 b1 z a3 a4 a5 a6)); [|exact H2].
    intros z w Hzw. now apply red_TCloseInd_P. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 b1 b2 z a4 a5 a6)); [|exact H3].
    intros z w Hzw. now apply red_TCloseInd_s. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 b1 b2 b3 z a5 a6)); [|exact H4].
    intros z w Hzw. now apply red_TCloseInd_F. }
  eapply rtc_trans.
  { eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 b1 b2 b3 b4 z a6)); [|exact H5].
    intros z w Hzw. now apply red_TCloseInd_i. }
  eapply (rtc_map_rel _ _ reduction reduction (fun z => TCloseInd b0 b1 b2 b3 b4 b5 z)); [|exact H6].
    intros z w Hzw. now apply red_TCloseInd_x.
Qed.

Ltac red_star_congr := solve [eassumption | apply rtc_refl |
  match goal with
  | |- rtc reduction (TPi ?a0 ?a1) (TPi ?b0 ?b1) => apply red_star_TPi; red_star_congr
  | |- rtc reduction (TLam ?a0) (TLam ?b0) => apply red_star_TLam; red_star_congr
  | |- rtc reduction (TApp ?a0 ?a1) (TApp ?b0 ?b1) => apply red_star_TApp; red_star_congr
  | |- rtc reduction (TSigma ?a0 ?a1) (TSigma ?b0 ?b1) => apply red_star_TSigma; red_star_congr
  | |- rtc reduction (TPair ?a0 ?a1) (TPair ?b0 ?b1) => apply red_star_TPair; red_star_congr
  | |- rtc reduction (TFst ?a0) (TFst ?b0) => apply red_star_TFst; red_star_congr
  | |- rtc reduction (TSnd ?a0) (TSnd ?b0) => apply red_star_TSnd; red_star_congr
  | |- rtc reduction (TConsE ?a0 ?a1) (TConsE ?b0 ?b1) => apply red_star_TConsE; red_star_congr
  | |- rtc reduction (TEnumT ?a0) (TEnumT ?b0) => apply red_star_TEnumT; red_star_congr
  | |- rtc reduction (TESucc ?a0) (TESucc ?b0) => apply red_star_TESucc; red_star_congr
  | |- rtc reduction (TEPi ?k ?a0 ?a1) (TEPi ?k ?b0 ?b1) => apply red_star_TEPi; red_star_congr
  | |- rtc reduction (TSwitch ?k ?a0 ?a1 ?a2 ?a3) (TSwitch ?k ?b0 ?b1 ?b2 ?b3) => apply red_star_TSwitch; red_star_congr
  | |- rtc reduction (TIDesc ?a0) (TIDesc ?b0) => apply red_star_TIDesc; red_star_congr
  | |- rtc reduction (TIVar ?a0) (TIVar ?b0) => apply red_star_TIVar; red_star_congr
  | |- rtc reduction (TIProd ?a0 ?a1) (TIProd ?b0 ?b1) => apply red_star_TIProd; red_star_congr
  | |- rtc reduction (TIPi ?a0 ?a1) (TIPi ?b0 ?b1) => apply red_star_TIPi; red_star_congr
  | |- rtc reduction (TISig ?a0 ?a1) (TISig ?b0 ?b1) => apply red_star_TISig; red_star_congr
  | |- rtc reduction (TIChoice ?a0 ?a1) (TIChoice ?b0 ?b1) => apply red_star_TIChoice; red_star_congr
  | |- rtc reduction (TInterp ?a0 ?a1 ?a2) (TInterp ?b0 ?b1 ?b2) => apply red_star_TInterp; red_star_congr
  | |- rtc reduction (TMuI ?a0 ?a1) (TMuI ?b0 ?b1) => apply red_star_TMuI; red_star_congr
  | |- rtc reduction (TIn ?a0) (TIn ?b0) => apply red_star_TIn; red_star_congr
  | |- rtc reduction (TInd ?a0 ?a1 ?a2 ?a3 ?a4 ?a5) (TInd ?b0 ?b1 ?b2 ?b3 ?b4 ?b5) => apply red_star_TInd; red_star_congr
  | |- rtc reduction (TIAll ?a0 ?a1 ?a2 ?a3 ?a4) (TIAll ?b0 ?b1 ?b2 ?b3 ?b4) => apply red_star_TIAll; red_star_congr
  | |- rtc reduction (THyps ?a0 ?a1 ?a2 ?a3 ?a4 ?a5) (THyps ?b0 ?b1 ?b2 ?b3 ?b4 ?b5) => apply red_star_THyps; red_star_congr
  | |- rtc reduction (TClose ?a0 ?a1 ?a2) (TClose ?b0 ?b1 ?b2) => apply red_star_TClose; red_star_congr
  | |- rtc reduction (TCloseCase ?k ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6) (TCloseCase ?k ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6) => apply red_star_TCloseCase; red_star_congr
  | |- rtc reduction (TCloseInd ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6) (TCloseInd ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6) => apply red_star_TCloseInd; red_star_congr
  end].

Lemma pstep_reductions : forall t u, pstep t u -> rtc reduction t u.
Proof.
  intros t u H; induction H; try solve [red_star_congr].
  - eapply rtc_trans with (y:=(TApp (TLam b') a'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TFst (TPair a' b)));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSnd (TPair a b')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TEPi k TNilE P));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TEPi k (TConsE tag E') P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSwitch k (TConsE tag E) P (TPair p' ps) TEZero));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSwitch k (TConsE tag E') P' (TPair p ps') (TESucc n')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT (TIVar i') X'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT TI1 X));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT TIBot X));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIProd A' B') X'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIPi A' D') X'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TISig A' D') X'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIChoice E' D') X'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT (TIVar i') X x' P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT TI1 X TUnit P));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT TIBot X x P));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIProd A' B') X' (TPair a' b') P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIPi A' D') X' f' P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TISig A D') X' (TPair a' x') P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIChoice E D') X' (TPair e' x') P'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT (TIVar i') X P h' x'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT TI1 X P h TUnit));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT TIBot X P h x));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIProd A' B') X' P' h' (TPair a' b')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIPi A D') X' P' h' f'));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TISig A D') X' P' h' (TPair a' x')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIChoice E D') X' P' h' (TPair e' x')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInd IT' D' P' st' i' (TIn xs')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TCloseCase k IT F G i Q b' (TIn xs')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TCloseInd IT' G' P' st' F' i' (TIn xs')));
      [red_star_congr|apply rtc_one; apply red_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].

Qed.
Lemma epstep_reductions : forall t u, epstep t u -> rtc reduction t u.
Proof.
  intros t u H; induction H; try solve [red_star_congr].
  eapply rtc_step; [apply red_eta|assumption].
Qed.
