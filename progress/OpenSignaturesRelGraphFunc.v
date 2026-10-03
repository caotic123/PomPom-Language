(* Graphs between related types are contained in the relation; any two
   graphs between the same types agree; graphs are total. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelGraph.
Import ListNotations.

Lemma nodup_same_name : forall (L : list string) m m' s, NoDup L ->
  nth_error L m = Some s -> nth_error L m' = Some s -> m = m'.
Proof.
  intros L m m' s HN H1 H2. apply (proj1 (NoDup_nth_error L) HN); [eapply nth_error_lt; exact H1|congruence].
Qed.

Lemma payload_conv : forall IT F G i IT' F' G' i', conv IT IT' -> conv F F' -> conv G G' -> conv i i' ->
  conv (payload IT F G i) (payload IT' F' G' i').
Proof.
  intros; unfold payload, carrier. apply cv_compatible, cp_TInterp; [assumption|apply conv_app; assumption|].
  apply cv_compatible, cp_TClose; assumption.
Qed.

Lemma closeat_payload_conv : forall A IT F G i IT' F' G' i', conv A (CloseAt IT F G i) ->
  conv A (CloseAt IT' F' G' i') -> conv (payload IT F G i) (payload IT' F' G' i').
Proof.
  intros A IT F G i IT' F' G' i' H1 H2.
  destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym H1) H2)) as (H3 & H4 & H5 & H6).
  apply payload_conv; assumption.
Qed.

Lemma tyw_conv_rty : forall A A', tyw A -> conv A A' -> rty A' A.
Proof. intros; apply rty_sym, tyw_conv; assumption. Qed.

(* Absorption: a graph between related types is contained in relatedness. *)
Lemma Gr_absorb : forall A B G, Gr A B G -> rty A B -> forall a b, G a b -> rel_at a b A B.
Proof.
  intros A B G H; induction H; intros HAB a0 b0 Hab.
  - destruct Hab as [_ [_ Hr]]; exact Hr.
  - destruct Hab.
  - rename H7 into IHc. destruct Hab as [Hf [Hg [Hff [Hgg Hfg]]]].
    destruct (pi_rty _ _ _ _ _ _ _ _ HAB H1 H2) as [HU HV].
    eapply pi_intro_rel; [exact HAB|exact H1|exact H2|]. intros a a2 Ha Ha2 Haa2.
    assert (Hd2 : Gd a2 (TApp c a2)) by (apply H5; [exact Ha2|eapply rel_at_right_of; exact Haa2]).
    pose proof (IHGr (rty_sym _ _ HU) _ _ Hd2) as Hca.
    assert (Hd : Gd a2 a).
    { eapply Gr_closure; [exact H3|exact Hd2|exact Ha2|exact Ha|eapply rel_at_right_of; exact Haa2|].
      eapply rel_at_trans; [apply rel_at_sym, Hca|apply rel_at_sym, Haa2]. }
    apply (IHc a2 a Hd); [apply HV; assumption|apply Hfg, Hd].
  - destruct Hab as [Hp [Hq [Hpp [Hqq Hx]]]].
    destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ HAB H1 H2 H3) as [HE' [_ Hiff]].
    assert (HL : L' = L) by (apply conv_code_inv; eapply cv_trans; [apply cv_sym, H4|exact HE']). subst L'.
    destruct Hx as (m & m' & s & xs & ys & Hm & Hm' & Hxs & Hys & Hpc & Hqc & Hr).
    pose proof (nodup_same_name _ _ _ _ H5 Hm Hm') as <-.
    apply Hiff; exists m, xs, ys; repeat apply conj; try assumption. eapply nth_error_lt; exact Hm.
  - destruct Hab as [Ht [Hu [Htt [Huu Hx]]]].
    destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ HAB H1 H2) as [HP Hiff].
    destruct Hx as (xs & ys & Hxs & Hys & Htc & Huc & Hp).
    apply Hiff; exists xs, ys; repeat apply conj; try assumption. apply IHGr; assumption.
  - apply IHGr; [exact HAB|apply H0, Hab].
Qed.

Lemma func_eq_right : forall A B G1 a1 b1 a2 b2, Gr A B G1 -> rty A B -> G1 a1 b1 ->
  rel_at a2 b2 A B -> rel_at a1 a2 A A -> rel_at b1 b2 B B.
Proof.
  intros A B G1 a1 b1 a2 b2 H HAB H1 H2 Ha.
  pose proof (Gr_absorb _ _ _ H HAB _ _ H1) as Hr.
  eapply rel_at_trans; [apply rel_at_sym, Hr|]. eapply rel_at_trans; [exact Ha|exact H2].
Qed.

(* Functionality: graphs between the same types agree on related inputs. *)
Theorem Gr_func : forall A B G1, Gr A B G1 -> forall G2, Gr A B G2 ->
  forall a1 a2 b1 b2, G1 a1 b1 -> G2 a2 b2 -> rel_at a1 a2 A A -> rel_at b1 b2 B B.
Proof.
  intros A B G1 H; induction H; intros G2 H2' a1 a2 b1 b2 Hab1 Hab2 Ha.
  - destruct Hab1 as [_ [_ Hr]].
    pose proof (Gr_absorb _ _ _ H2' H _ _ Hab2) as Hr2.
    eapply rel_at_trans; [apply rel_at_sym, Hr|]. eapply rel_at_trans; [exact Ha|exact Hr2].
  - destruct Hab1.
  - rename H7 into IHc. destruct (Gr_view _ _ _ H2') as
      [HAB HE|_ _ Hem HE|x2 U2 V2 y2 U2' V2' Gd2 Gc2 c2 D2 _ _ HA2 HB2 Hd2 Hc2 Hr2 Hcod2 HD2 Hreal2 HE
      |? ? ? ? ? ? ? ? _ _ HA2 _ _ _ _ _ HE|? ? ? ? ? ? ? ? ? _ _ HA2 _ _ HE]; apply HE in Hab2.
    + assert (HG1 : Gr A B (pi_graph A B Gd Gc)) by (eapply gr_pi with (c := c) (D := D); eassumption).
      destruct Hab2 as [_ [_ Hr]]. eapply func_eq_right; [exact HG1|exact HAB|exact Hab1|exact Hr|exact Ha].
    + destruct Hab2.
    + destruct Hab1 as [Hf1 [Hg1 [Hff1 [Hgg1 Hfg1]]]]. destruct Hab2 as [Hf2 [Hg2 [Hff2 [Hgg2 Hfg2]]]].
      destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym H1) HA2)) as [HUU2 HVV2].
      destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym H2) HB2)) as [HUU2' HVV2'].
      destruct (Gr_tyw _ _ _ H3) as [HU'w HUw].
      assert (HU' : rty U' U2') by (apply tyw_conv; assumption).
      assert (HU : rty U U2) by (apply tyw_conv; assumption).
      assert (Hd2' : Gr U' U Gd2) by (eapply Gr_transport; [exact Hd2|apply rty_sym, HU'|apply rty_sym, HU]).
      destruct (pi_rty _ _ _ _ _ _ _ _ (tyw_rty _ H) H1 H1) as [_ HVA].
      destruct (pi_rty _ _ _ _ _ _ _ _ (tyw_rty _ H0) H2 H2) as [_ HVB].
      eapply pi_intro_rel; [exact (tyw_rty _ H0)|exact H2|exact H2|]. intros e1 e2 He1 He2 He.
      assert (Hd1e : Gd e1 (TApp c e1)) by (apply H5; [exact He1|eapply rel_at_left_of; exact He]).
      assert (Hd2e : Gd2 e2 (TApp c2 e2)).
      { apply Hr2; [exact He2|]. eapply rel_at_retype; [eapply rel_at_right_of; exact He|exact HU'|exact HU']. }
      pose proof (IHGr _ Hd2' _ _ _ _ Hd1e Hd2e He) as Hcc.
      assert (Hcl1 : closed (TApp c e1)) by (apply closed_app; assumption).
      assert (Hcl2 : closed (TApp c2 e2)) by (apply closed_app; assumption).
      pose proof (pi_app_rel _ _ _ _ _ _ _ _ _ _ _ _ Ha H1 H1 Hcl1 Hcl2 Hcc) as Hff.
      pose proof (Hfg1 _ _ Hd1e) as HG1. pose proof (Hfg2 _ _ Hd2e) as HG2.
      assert (HC2 : Gr (subst (TApp c e1) x V) (subst e1 y V') (Gc2 e2 (TApp c2 e2))).
      { eapply Gr_transport; [apply Hcod2, Hd2e| |].
        - eapply rty_trans; [apply tyw_conv_rty; [|apply HVV2, Hcl2]|].
          + eapply rty_tyw_r, HVA; [exact Hcl1|exact Hcl2|exact Hcc].
          + apply rty_sym, HVA; assumption.
        - eapply rty_trans; [apply tyw_conv_rty; [|apply HVV2', He2]|].
          + eapply rty_tyw_r, HVB; [exact He1|exact He2|exact He].
          + apply rty_sym, HVB; assumption. }
      pose proof (IHc _ _ Hd1e _ HC2 _ _ _ _ HG1 HG2) as Hout.
      eapply rel_at_retype; [apply Hout|apply tyw_rty|apply HVB; assumption].
      * eapply rel_at_retype; [exact Hff|apply tyw_rty|apply rty_sym, HVA; assumption].
        eapply rty_tyw_l, HVA; [exact Hcl1|exact Hcl2|exact Hcc].
      * eapply rty_tyw_l, HVB; [exact He1|exact He2|exact He].
    + head_contra2.
    + head_contra2.
  - destruct (Gr_view _ _ _ H2') as
      [HAB HE|_ _ Hem HE|? ? ? ? ? ? ? ? ? ? _ _ HA2 _ _ _ _ _ _ _ HE
      |x2 E2 P2 y2 E3 P3 L2 L3 _ _ HA2 HE2 HB2 HE3 HN3 Hrows2 HE|? ? ? ? ? ? ? ? ? _ _ HA2 _ _ HE]; apply HE in Hab2.
    + assert (HG1 : Gr A B (sum_graph A B x P y P' L L')) by (eapply gr_sum; eassumption).
      destruct Hab2 as [_ [_ Hr]]. eapply func_eq_right; [exact HG1|exact HAB|exact Hab1|exact Hr|exact Ha].
    + destruct Hab2.
    + head_contra2.
    + destruct Hab1 as [Hp1 [Hq1 [Hpp1 [Hqq1 Hx1]]]]. destruct Hab2 as [Hp2 [Hq2 [Hpp2 [Hqq2 Hx2]]]].
      destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym H1) HA2)) as [HEE HPP].
      destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym H3) HB2)) as [HEE' HPP'].
      assert (HL2 : L2 = L) by (apply conv_code_inv; eapply cv_trans; [apply cv_sym, HE2|eapply cv_trans; [apply cv_sym, conv_enum, HEE|exact H2]]).
      assert (HL3 : L3 = L') by (apply conv_code_inv; eapply cv_trans; [apply cv_sym, HE3|eapply cv_trans; [apply cv_sym, conv_enum, HEE'|exact H4]]).
      subst L2 L3.
      destruct Hx1 as (m1 & m1' & s1 & xs1 & ys1 & Hm1 & Hm1' & Hxs1 & Hys1 & Hpc1 & Hqc1 & Hr1).
      destruct Hx2 as (m2 & m2' & s2 & xs2 & ys2 & Hm2 & Hm2' & Hxs2 & Hys2 & Hpc2 & Hqc2 & Hr2).
      destruct (sum_rel_step _ _ _ _ _ _ _ _ _ Ha H1 H2 Hpc1) as (xs2' & Hxs2' & Hpc2' & Hlt & Hxx).
      destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hpc2) Hpc2')) as [Hpos Hxs22].
      apply conv_position_inv in Hpos; subst m2.
      assert (s2 = s1) by congruence; subst s2.
      pose proof (nodup_same_name _ _ _ _ H5 Hm1' Hm2') as <-.
      destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ (tyw_rty _ H0) H3 H4 H3) as [_ [_ Hiff]].
      apply Hiff. exists m1', ys1, ys2; repeat apply conj; try assumption; [eapply nth_error_lt; exact Hm1'|].
      eapply rel_at_trans; [apply rel_at_sym, Hr1|]. eapply rel_at_trans.
      * eapply rel_at_trans; [exact Hxx|]. eapply rel_at_conv; [eapply rel_at_right_of; exact Hxx|apply cv_refl|apply cv_sym, Hxs22|apply cv_refl|apply cv_refl].
      * eapply rel_at_conv; [exact Hr2|apply cv_refl|apply cv_refl|apply cv_sym, HPP, closed_position|apply cv_sym, HPP', closed_position].
    + head_contra2.
  - destruct (Gr_view _ _ _ H2') as
      [HAB HE|_ _ Hem HE|? ? ? ? ? ? ? ? ? ? _ _ HA2 _ _ _ _ _ _ _ HE
      |? ? ? ? ? ? ? ? _ _ HA2 _ _ _ _ _ HE|IT2 F2 G02 i2 IT2' F2' G02' i2' Gp2 _ _ HA2 HB2 Hp2 HE]; apply HE in Hab2.
    + assert (HG1 : Gr A B (roll_graph A B Gp)) by (eapply gr_roll; eassumption).
      destruct Hab2 as [_ [_ Hr]]. eapply func_eq_right; [exact HG1|exact HAB|exact Hab1|exact Hr|exact Ha].
    + destruct Hab2.
    + head_contra2.
    + head_contra2.
    + destruct Hab1 as [Ht1 [Hu1 [Htt1 [Huu1 Hx1]]]]. destruct Hab2 as [Ht2 [Hu2 [Htt2 [Huu2 Hx2]]]].
      destruct (Gr_tyw _ _ _ H3) as [HPw HPw'].
      assert (Hp2' : Gr (payload IT F G i) (payload IT' F' G' i') Gp2).
      { eapply Gr_transport; [exact Hp2|apply tyw_conv_rty; [exact HPw|eapply closeat_payload_conv; eassumption]
          |apply tyw_conv_rty; [exact HPw'|eapply closeat_payload_conv; eassumption]]. }
      destruct Hx1 as (xs1 & ys1 & Hxs1 & Hys1 & Htc1 & Huc1 & Hg1).
      destruct Hx2 as (xs2 & ys2 & Hxs2 & Hys2 & Htc2 & Huc2 & Hg2).
      destruct (close_rel_step _ _ _ _ _ _ _ _ Ha H1 Htc1) as (xs2' & Hxs2' & Htc2' & Hxx).
      pose proof (conv_in_inv _ _ (cv_trans (cv_sym Htc2) Htc2')) as Hxs22.
      assert (Hx12 : rel_at xs1 xs2 (payload IT F G i) (payload IT F G i)).
      { eapply rel_at_conv; [exact Hxx|apply cv_refl|apply cv_sym, Hxs22|apply cv_refl|apply cv_refl]. }
      pose proof (IHGr _ Hp2' _ _ _ _ Hg1 Hg2 Hx12) as Hyy.
      destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ (tyw_rty _ H0) H2 H2) as [_ Hiff].
      apply Hiff; exists ys1, ys2; repeat apply conj; assumption.
  - eapply IHGr; [exact H2'|apply H0, Hab1|exact Hab2|exact Ha].
Qed.

Definition pi_realizer (D f c : term) :=
  TLam 0 (TApp (TApp D (TVar 0)) (TApp f (TApp c (TVar 0)))).

Lemma closed_not_in : forall t y, closed t -> ~ In y (free_vars t).
Proof. intros t y H; unfold closed in H; rewrite H; tauto. Qed.

Lemma pi_realizer_closed : forall D f c, closed D -> closed f -> closed c -> closed (pi_realizer D f c).
Proof.
  intros D f c HD Hf Hc; apply closed_lam_of; intros w Hw; cbn [free_vars] in Hw.
  repeat rewrite in_app_iff in Hw. cbn [In] in Hw.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
    first [exact (False_ind _ (closed_not_in _ _ HD Hw)) | exact (False_ind _ (closed_not_in _ _ Hf Hw))
      | exact (False_ind _ (closed_not_in _ _ Hc Hw)) | congruence | contradiction].
Qed.

Lemma pi_realizer_beta : forall D f c e, closed D -> closed f -> closed c ->
  conv (TApp (pi_realizer D f c) e) (TApp (TApp D e) (TApp f (TApp c e))).
Proof.
  intros D f c e HD Hf Hc; unfold pi_realizer. eapply cv_trans; [apply beta_conv|].
  rewrite !subst_app, subst_var_same, (subst_not_free D), (subst_not_free f), (subst_not_free c)
    by (apply closed_not_in; assumption).
  apply cv_refl.
Qed.

(* Totality. *)
Theorem Gr_total : forall A B G, Gr A B G -> forall a, closed a -> rel_at a a A A -> exists b, G a b.
Proof.
  intros A B G H; induction H; intros a0 Ha0 Haa0.
  - exists a0; repeat apply conj; try assumption. apply rel_at_rty_both; assumption.
  - exfalso; eapply H1; [exact Ha0|exact Haa0].
  - rename a0 into f. rename H7 into IHc.
    destruct (pi_rty _ _ _ _ _ _ _ _ (tyw_rty _ H) H1 H1) as [_ HVA].
    destruct (pi_rty _ _ _ _ _ _ _ _ (tyw_rty _ H0) H2 H2) as [_ HVB].
    exists (pi_realizer D f c).
    assert (Hgc : closed (pi_realizer D f c)) by (apply pi_realizer_closed; assumption).
    (* the realizer output at a domain point *)
    assert (Hout : forall a' a, Gd a' a -> Gc a' a (TApp f a) (TApp (pi_realizer D f c) a')).
    { intros a' a Hd. destruct (Gr_typed _ _ _ _ _ H3 Hd) as [Hca' [Hca [Ha'a' Haa]]].
      assert (Hdc : Gd a' (TApp c a')) by (apply H5; assumption).
      assert (Hcc : closed (TApp c a')) by (apply closed_app; assumption).
      pose proof (Gr_func _ _ _ H3 _ H3 _ _ _ _ Hd Hdc Ha'a') as Hac.
      assert (Hfa : rel_at (TApp f a) (TApp f (TApp c a')) (subst a x V) (subst a x V)).
      { eapply rel_at_retype; [eapply pi_app_rel; [exact Haa0|exact H1|exact H1|exact Hca|exact Hcc|exact Hac]
          |apply tyw_rty; eapply rty_tyw_l, HVA; [exact Hca|exact Hcc|exact Hac]|apply rty_sym, HVA; assumption]. }
      assert (Hcf1 : closed (TApp f a)) by (apply closed_app; assumption).
      assert (Hcf2 : closed (TApp f (TApp c a'))) by (apply closed_app; assumption).
      pose proof (H9 a' a _ Hd Hcf1 (rel_at_left_of _ _ _ _ Hfa)) as R1.
      pose proof (H9 a' a _ Hd Hcf2 (rel_at_right_of _ _ _ _ Hfa)) as R2.
      pose proof (Gr_func _ _ _ (H6 _ _ Hd) _ (H6 _ _ Hd) _ _ _ _ R1 R2 Hfa) as Hdd.
      eapply Gr_closure; [apply H6, Hd|exact R1|exact Hcf1|apply closed_app; [exact Hgc|exact Hca']|exact (rel_at_left_of _ _ _ _ Hfa)|].
      eapply rel_at_conv; [exact Hdd|apply cv_refl|apply cv_sym, pi_realizer_beta; assumption|apply cv_refl|apply cv_refl]. }
    refine (conj Ha0 (conj Hgc (conj Haa0 (conj _ Hout)))).
    eapply pi_intro_rel; [exact (tyw_rty _ H0)|exact H2|exact H2|]. intros e1 e2 He1 He2 He.
    assert (Hd1 : Gd e1 (TApp c e1)) by (apply H5; [exact He1|eapply rel_at_left_of; exact He]).
    assert (Hd2 : Gd e2 (TApp c e2)) by (apply H5; [exact He2|eapply rel_at_right_of; exact He]).
    pose proof (Gr_func _ _ _ H3 _ H3 _ _ _ _ Hd1 Hd2 He) as Hcc.
    pose proof (Hout _ _ Hd1) as O1. pose proof (Hout _ _ Hd2) as O2.
    assert (Hcl1 : closed (TApp c e1)) by (apply closed_app; assumption).
    assert (Hcl2 : closed (TApp c e2)) by (apply closed_app; assumption).
    assert (HC2 : Gr (subst (TApp c e1) x V) (subst e1 y V') (Gc e2 (TApp c e2))).
    { eapply Gr_transport; [apply H6, Hd2|apply rty_sym, HVA; assumption|apply rty_sym, HVB; assumption]. }
    pose proof (Gr_func _ _ _ (H6 _ _ Hd1) _ HC2 _ _ _ _ O1 O2) as Hres.
    eapply rel_at_retype; [apply Hres|apply tyw_rty|apply HVB; assumption].
    + eapply rel_at_retype; [eapply pi_app_rel; [exact Haa0|exact H1|exact H1|exact Hcl1|exact Hcl2|exact Hcc]
        |apply tyw_rty|apply rty_sym, HVA; assumption].
      eapply rty_tyw_l, HVA; [exact Hcl1|exact Hcl2|exact Hcc].
    + eapply rty_tyw_l, HVB; [exact He1|exact He2|exact He].
  - destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ (tyw_rty _ H) H1 H2 H1) as [_ [_ HiffA]].
    destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ (tyw_rty _ H0) H3 H4 H3) as [_ [_ HiffB]].
    destruct (proj1 (HiffA _ _) Haa0) as (m & xs & xs2 & Hm & Hxs & Hxs2 & Hp & Hp2 & Hr).
    destruct (H6 m Hm) as [(m' & s & Hs & Hs' & Hrt)|Hdead]; [|exfalso; eapply Hdead; [exact Hxs|exact Hr]].
    exists (TPair (enum_position m') xs).
    assert (Hxx : rel_at xs xs (subst (enum_position m) x P) (subst (enum_position m) x P)) by (eapply rel_at_left_of; exact Hr).
    refine (conj Ha0 (conj (closed_pair _ _ (closed_position _) Hxs) (conj Haa0 (conj _ _)))).
    + apply HiffB. exists m', xs, xs; repeat apply conj; try assumption; try apply cv_refl.
      * eapply nth_error_lt; exact Hs'.
      * eapply rel_at_retype; [exact Hxx|exact Hrt|exact Hrt].
    + exists m, m', s, xs, xs; repeat apply conj; try assumption; try apply cv_refl.
      eapply rel_at_retype; [exact Hxx|apply tyw_rty, (proj1 (rel_at_tyw _ _ _ _ Hxx))|exact Hrt].
  - destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ (tyw_rty _ H) H1 H1) as [_ HiffA].
    destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ (tyw_rty _ H0) H2 H2) as [_ HiffB].
    destruct (proj1 (HiffA _ _) Haa0) as (xs & xs2 & Hxs & Hxs2 & Ht & Ht2 & Hr).
    destruct (IHGr xs Hxs (rel_at_left_of _ _ _ _ Hr)) as [ys Hys].
    destruct (Gr_typed _ _ _ _ _ H3 Hys) as [_ [Hcys [_ Hyy]]].
    exists (TIn ys). refine (conj Ha0 (conj (closed_in _ Hcys) (conj Haa0 (conj _ _)))).
    + apply HiffB; exists ys, ys; repeat apply conj; try assumption; apply cv_refl.
    + exists xs, ys; repeat apply conj; try assumption; apply cv_refl.
  - destruct (IHGr a0 Ha0 Haa0) as [b Hb]; exists b; apply H0, Hb.
Qed.

(* Union of all graphs between two types; equal to each one of them. *)
Definition canonG (A B : term) : rel := fun a b => exists G, Gr A B G /\ G a b.

Lemma canonG_equiv : forall A B G, Gr A B G -> rel_equiv G (canonG A B).
Proof.
  intros A B G H a b; split; [intros Hab; exists G; split; assumption|].
  intros [G' [H' Hab]]. destruct (Gr_typed _ _ _ _ _ H' Hab) as [Ha [Hb [Haa Hbb]]].
  destruct (Gr_total _ _ _ H a Ha Haa) as [b0 Hb0].
  pose proof (Gr_func _ _ _ H _ H' _ _ _ _ Hb0 Hab Haa) as Hbb0.
  eapply Gr_closure; [exact H|exact Hb0|exact Ha|exact Hb|exact Haa|exact Hbb0].
Qed.
Lemma canonG_gr : forall A B G, Gr A B G -> Gr A B (canonG A B).
Proof. intros; eapply gr_equiv; [eassumption|apply canonG_equiv; assumption]. Qed.
