(* Composition of coercion graphs: the composite of two graphs is contained
   in a graph. This is the semantic counterpart of eliminating transitivity. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelGraphFunc.
Import ListNotations.

Definition comp_ok (A B : term) (G1 G2 : rel) :=
  exists G3, Gr A B G3 /\ forall a m b, G1 a m -> G2 m b -> G3 a b.

Lemma comp_ok_equiv : forall A B G1 G2 G1' G2', comp_ok A B G1 G2 ->
  rel_equiv G1 G1' -> rel_equiv G2 G2' -> comp_ok A B G1' G2'.
Proof.
  intros A B G1 G2 G1' G2' [G3 [H3 Hi]] E1 E2; exists G3; split; [exact H3|].
  intros a m b H1 H2; apply Hi with m; [apply E1, H1|apply E2, H2].
Qed.

Lemma comp_eq_left : forall A M B G1 G2, Gr A M G1 -> rty A M ->
  (forall a m, G1 a m -> rel_at a m A M) -> Gr M B G2 -> comp_ok A B G1 G2.
Proof.
  intros A M B G1 G2 H1 HAM E1 H2; exists G2; split; [eapply Gr_transport_l; [exact H2|apply rty_sym, HAM]|].
  intros a m b Ham Hmb. pose proof (E1 _ _ Ham) as Hr.
  destruct (Gr_typed _ _ _ _ _ H1 Ham) as [Ha _].
  destruct (Gr_typed _ _ _ _ _ H2 Hmb) as [Hm [Hb [Hmm Hbb]]].
  eapply Gr_closure; [exact H2|exact Hmb|exact Ha|exact Hb| |exact Hbb].
  eapply rel_at_retype; [apply rel_at_sym, Hr|apply tyw_rty, (rty_tyw_r _ _ HAM)|exact HAM].
Qed.

Lemma comp_eq_right : forall A M B G1 G2, Gr A M G1 -> Gr M B G2 -> rty M B ->
  (forall m b, G2 m b -> rel_at m b M B) -> comp_ok A B G1 G2.
Proof.
  intros A M B G1 G2 H1 H2 HMB E2; exists G1; split; [eapply Gr_transport_r; [exact H1|exact HMB]|].
  intros a m b Ham Hmb. pose proof (E2 _ _ Hmb) as Hr.
  destruct (Gr_typed _ _ _ _ _ H1 Ham) as [Ha [Hm [Haa Hmm]]].
  destruct (Gr_typed _ _ _ _ _ H2 Hmb) as [_ [Hb _]].
  eapply Gr_closure; [exact H1|exact Ham|exact Ha|exact Hb|exact Haa|].
  eapply rel_at_retype; [exact Hr|apply tyw_rty, (rty_tyw_l _ _ HMB)|apply rty_sym, HMB].
Qed.

Lemma comp_empty_left : forall A M B G1 G2, Gr A M G1 -> tyw B ->
  (forall t u, closed t -> ~ rel_at t u A A) -> comp_ok A B G1 G2.
Proof.
  intros A M B G1 G2 H1 HB He; exists empty_rel; split.
  - apply gr_empty; [exact (proj1 (Gr_tyw _ _ _ H1))|exact HB|exact He].
  - intros a m b Ham _; destruct (Gr_typed _ _ _ _ _ H1 Ham) as [Ha [_ [Haa _]]]; exact (He _ _ Ha Haa).
Qed.

Lemma comp_empty_right : forall A M B G1 G2, Gr A M G1 -> tyw B ->
  (forall t u, closed t -> ~ rel_at t u M M) -> comp_ok A B G1 G2.
Proof.
  intros A M B G1 G2 H1 HB He; exists empty_rel; split.
  - apply gr_empty; [exact (proj1 (Gr_tyw _ _ _ H1))|exact HB|].
    intros t u Ht Htu. destruct (Gr_total _ _ _ H1 t Ht (rel_at_left_of _ _ _ _ Htu)) as [m Hm].
    destruct (Gr_typed _ _ _ _ _ H1 Hm) as [_ [Hcm [_ Hmm]]]; exact (He _ _ Hcm Hmm).
  - intros a m b Ham _; destruct (Gr_typed _ _ _ _ _ H1 Ham) as [_ [Hm [_ Hmm]]]; exact (He _ _ Hm Hmm).
Qed.

Lemma comp_sum : forall A M B x E P y E' P' y2 E2 P2 z E3 P3 L L' L2 L3,
  tyw A -> tyw B -> conv A (TSigma x (TEnumT E) P) -> conv E (code L) ->
  conv M (TSigma y (TEnumT E') P') -> conv E' (code L') ->
  (forall m, m < List.length L -> row_live x P y P' L L' m \/ row_dead x P m) ->
  conv M (TSigma y2 (TEnumT E2) P2) -> conv E2 (code L2) ->
  conv B (TSigma z (TEnumT E3) P3) -> conv E3 (code L3) -> NoDup L3 ->
  (forall m, m < List.length L2 -> row_live y2 P2 z P3 L2 L3 m \/ row_dead y2 P2 m) ->
  comp_ok A B (sum_graph A M x P y P' L L') (sum_graph M B y2 P2 z P3 L2 L3).
Proof.
  intros A M B x E P y E' P' y2 E2 P2 z E3 P3 L L' L2 L3 HA HB HAc HE HMc HE' Hrows1 HM2c HE2 HBc HE3 HN3 Hrows2.
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HMc) HM2c)) as [HEE HPP].
  assert (HL : L2 = L') by (apply conv_code_inv; eapply cv_trans; [apply cv_sym, HE2|eapply cv_trans; [apply cv_sym, conv_enum, HEE|exact HE']]).
  subst L2.
  exists (sum_graph A B x P z P3 L L3); split.
  - eapply gr_sum; try eassumption. intros m Hm.
    destruct (Hrows1 m Hm) as [(m' & s & Hs & Hs' & Hr)|Hd]; [|right; exact Hd].
    pose proof (nth_error_lt _ _ _ Hs') as Hm'.
    assert (Hr' : rty (subst (enum_position m) x P) (subst (enum_position m') y2 P2)).
    { eapply rty_trans; [exact Hr|apply tyw_conv; [eapply rty_tyw_r; exact Hr|apply HPP, closed_position]]. }
    destruct (Hrows2 m' Hm') as [(m'' & s' & Hs2 & Hs3 & Hr2)|Hd2].
    + left. assert (s' = s) by congruence; subst s'.
      exists m'', s; repeat apply conj; try assumption. eapply rty_trans; eassumption.
    + right. intros t u Ht Htu; apply (Hd2 t u Ht). eapply rel_at_retype; [exact Htu|exact Hr'|exact Hr'].
  - intros p q r [Hp [Hq [Hpp [Hqq Hx1]]]] [_ [Hr [_ [Hrr Hx2]]]].
    refine (conj Hp (conj Hr (conj Hpp (conj Hrr _)))).
    destruct Hx1 as (m & m' & s & xs & ys & Hm & Hm' & Hxs & Hys & Hpc & Hqc & Hr1).
    destruct Hx2 as (m2 & m'' & s2 & ys2 & zs & Hm2 & Hm'' & Hys2 & Hzs & Hqc2 & Hrc & Hr2).
    destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hqc) Hqc2)) as [Hpos Hyy].
    apply conv_position_inv in Hpos; subst m2.
    assert (s2 = s) by congruence; subst s2.
    exists m, m'', s, xs, zs; repeat apply conj; try assumption.
    eapply rel_at_trans; [exact Hr1|]. eapply rel_at_conv; [exact Hr2|apply cv_sym, Hyy|apply cv_refl|apply cv_sym, HPP, closed_position|apply cv_refl].
Qed.

Lemma comp_roll : forall A M B IT F G i ITm Fm Gm im ITm' Fm' Gm' im' IT' F' G' i' Gp1 Gp2,
  tyw A -> tyw B -> conv A (CloseAt IT F G i) -> conv M (CloseAt ITm Fm Gm im) ->
  conv M (CloseAt ITm' Fm' Gm' im') -> conv B (CloseAt IT' F' G' i') ->
  Gr (payload ITm' Fm' Gm' im') (payload IT' F' G' i') Gp2 ->
  comp_ok (payload IT F G i) (payload IT' F' G' i') Gp1 Gp2 ->
  comp_ok A B (roll_graph A M Gp1) (roll_graph M B Gp2).
Proof.
  intros A M B IT F G i ITm Fm Gm im ITm' Fm' Gm' im' IT' F' G' i' Gp1 Gp2 HA HB HAc HMc HM2c HBc H2 [G3 [H3 Hi]].
  exists (roll_graph A B G3); split; [eapply gr_roll; eassumption|].
  intros t u v [Ht [Hu [Htt [Huu Hx1]]]] [_ [Hv [_ [Hvv Hx2]]]].
  refine (conj Ht (conj Hv (conj Htt (conj Hvv _)))).
  destruct Hx1 as (xs & ys & Hxs & Hys & Htc & Huc & Hg1).
  destruct Hx2 as (ys2 & zs & Hys2 & Hzs & Huc2 & Hvc & Hg2).
  pose proof (conv_in_inv _ _ (cv_trans (cv_sym Huc2) Huc)) as Hyy.
  exists xs, zs; repeat apply conj; try assumption. apply Hi with ys; [exact Hg1|].
  destruct (Gr_typed _ _ _ _ _ H2 Hg2) as [_ [_ [Hy2 Hzz]]].
  eapply Gr_closure; [exact H2|exact Hg2|exact Hys|exact Hzs| |exact Hzz].
  eapply rel_at_conv; [exact Hy2|apply cv_refl|exact Hyy|apply cv_refl|apply cv_refl].
Qed.

Definition comp_realizer (D1 D2 c2 : term) :=
  TLam 0 (TLam 1 (TApp (TApp D2 (TVar 0)) (TApp (TApp D1 (TApp c2 (TVar 0))) (TVar 1)))).

Lemma comp_realizer_closed : forall D1 D2 c2, closed D1 -> closed D2 -> closed c2 ->
  closed (comp_realizer D1 D2 c2).
Proof.
  intros D1 D2 c2 H1 H2 H3; apply closed_lam_of; intros w Hw; cbn [free_vars] in Hw.
  rewrite in_remove_iff in Hw; destruct Hw as [Hw Hne].
  repeat rewrite in_app_iff in Hw; cbn [In] in Hw.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
    first [exact (False_ind _ (closed_not_in _ _ H1 Hw)) | exact (False_ind _ (closed_not_in _ _ H2 Hw))
      | exact (False_ind _ (closed_not_in _ _ H3 Hw)) | congruence | contradiction].
Qed.

Lemma comp_realizer_beta : forall D1 D2 c2 e t, closed D1 -> closed D2 -> closed c2 -> closed e ->
  conv (TApp (TApp (comp_realizer D1 D2 c2) e) t) (TApp (TApp D2 e) (TApp (TApp D1 (TApp c2 e)) t)).
Proof.
  intros D1 D2 c2 e t H1 H2 H3 He; unfold comp_realizer.
  eapply cv_trans; [apply conv_app_f, beta_conv|].
  rewrite subst_lam_closed by (assumption || lia).
  rewrite !subst_app, subst_var_same, subst_var_other by lia.
  rewrite (subst_not_free D2), (subst_not_free D1), (subst_not_free c2) by (apply closed_not_in; assumption).
  eapply cv_trans; [apply beta_conv|].
  rewrite !subst_app, subst_var_same.
  rewrite (subst_not_free D2), (subst_not_free D1), (subst_not_free c2), (subst_not_free e)
    by (apply closed_not_in; assumption).
  apply cv_refl.
Qed.

Lemma closed_compose : forall c d, closed c -> closed d -> closed (compose_coercion c d).
Proof.
  intros c d Hc Hd; unfold compose_coercion; apply closed_lam_of; intros w Hw; cbn [free_vars] in Hw.
  repeat rewrite in_app_iff in Hw; cbn [In] in Hw.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
    first [exact (False_ind _ (closed_not_in _ _ Hc Hw)) | exact (False_ind _ (closed_not_in _ _ Hd Hw))
      | congruence | contradiction].
Qed.

Lemma comp_pi : forall A M B x U V y U' V' y2 U2 V2 w W X Gd1 Gc1 c1 D1 Gd2 Gc2 c2 D2,
  tyw A -> tyw B -> conv A (TPi x U V) -> conv M (TPi y U' V') ->
  conv M (TPi y2 U2 V2) -> conv B (TPi w W X) ->
  Gr U' U Gd1 -> closed c1 -> (forall a', closed a' -> rel_at a' a' U' U' -> Gd1 a' (TApp c1 a')) ->
  (forall a' a, Gd1 a' a -> Gr (subst a x V) (subst a' y V') (Gc1 a' a)) -> closed D1 ->
  (forall a' a t, Gd1 a' a -> closed t -> rel_at t t (subst a x V) (subst a x V) ->
     Gc1 a' a t (TApp (TApp D1 a') t)) ->
  Gr W U2 Gd2 -> closed c2 -> (forall a', closed a' -> rel_at a' a' W W -> Gd2 a' (TApp c2 a')) ->
  (forall a' a, Gd2 a' a -> Gr (subst a y2 V2) (subst a' w X) (Gc2 a' a)) -> closed D2 ->
  (forall a' a t, Gd2 a' a -> closed t -> rel_at t t (subst a y2 V2) (subst a y2 V2) ->
     Gc2 a' a t (TApp (TApp D2 a') t)) ->
  comp_ok W U Gd2 Gd1 ->
  (forall m a e, Gd1 m a -> Gd2 e m -> comp_ok (subst a x V) (subst e w X) (Gc1 m a) (Gc2 e m)) ->
  comp_ok A B (pi_graph A M Gd1 Gc1) (pi_graph M B Gd2 Gc2).
Proof.
  intros A M B x U V y U' V' y2 U2 V2 w W X Gd1 Gc1 c1 D1 Gd2 Gc2 c2 D2 HA HB HAc HMc HM2c HBc
    HGd1 Hc1 Hreal1 Hcod1 HD1 Hcd1 HGd2 Hc2 Hreal2 Hcod2 HD2 Hcd2 Hdom Hcod.
  destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HMc) HM2c)) as [HUU2 HVV2].
  destruct Hdom as [G3d [HG3d Hincl]].
  destruct (Gr_tyw _ _ _ HGd1) as [HU'w HUw].
  pose proof (tyw_conv_rty _ _ HU'w HUU2) as HU2U'.
  assert (Hstep : forall e, closed e -> rel_at e e W W ->
    Gd2 e (TApp c2 e) /\ Gd1 (TApp c2 e) (TApp c1 (TApp c2 e)) /\ G3d e (TApp c1 (TApp c2 e)) /\
    closed (TApp c2 e) /\ rel_at (TApp c2 e) (TApp c2 e) U' U').
  { intros e He Hee.
    assert (H2e : Gd2 e (TApp c2 e)) by (apply Hreal2; assumption).
    destruct (Gr_typed _ _ _ _ _ HGd2 H2e) as [_ [Hce [_ Hcc]]].
    assert (Hcc' : rel_at (TApp c2 e) (TApp c2 e) U' U') by (eapply rel_at_retype; [exact Hcc|exact HU2U'|exact HU2U']).
    assert (H1e : Gd1 (TApp c2 e) (TApp c1 (TApp c2 e))) by (apply Hreal1; assumption).
    repeat apply conj; try assumption. exact (Hincl _ _ _ H2e H1e). }
  assert (Hmid : forall e a, G3d e a -> Gd2 e (TApp c2 e) /\ Gd1 (TApp c2 e) a).
  { intros e a H. destruct (Gr_typed _ _ _ _ _ HG3d H) as [He [Ha [Hee Haa]]].
    destruct (Hstep e He Hee) as (H2e & H1e & H3e & Hce & Hcc').
    pose proof (Gr_func _ _ _ HG3d _ HG3d _ _ _ _ H H3e Hee) as Hac.
    split; [exact H2e|].
    eapply Gr_closure; [exact HGd1|exact H1e|exact Hce|exact Ha|exact Hcc'|apply rel_at_sym, Hac]. }
  exists (pi_graph A B G3d (fun e a => canonG (subst a x V) (subst e w X))). split.
  - eapply gr_pi with (c := compose_coercion c2 c1) (D := comp_realizer D1 D2 c2);
      [exact HA|exact HB|exact HAc|exact HBc|exact HG3d|apply closed_compose; assumption| | |apply comp_realizer_closed; assumption|].
    + intros e He Hee. destruct (Hstep e He Hee) as (H2e & H1e & H3e & Hce & Hcc').
      destruct (Gr_typed _ _ _ _ _ HG3d H3e) as [_ [Hc3 [_ H33]]].
      eapply Gr_closure; [exact HG3d|exact H3e|exact He|apply closed_app; [apply closed_compose; assumption|exact He]|exact Hee|].
      eapply rel_at_conv; [exact H33|apply cv_refl|apply cv_sym, compose_coercion_beta|apply cv_refl|apply cv_refl].
    + intros e a H. destruct (Hmid e a H) as [H2e H1e]. destruct (Hcod _ _ _ H1e H2e) as [G3 [HG3 _]].
      exact (canonG_gr _ _ _ HG3).
    + intros e a t H Ht Htt. destruct (Hmid e a H) as [H2e H1e].
      pose proof (Hcd1 _ _ _ H1e Ht Htt) as R1.
      destruct (Gr_typed _ _ _ _ _ (Hcod1 _ _ H1e) R1) as [_ [Hs [_ Hss]]].
      destruct (Gr_typed _ _ _ _ _ HGd2 H2e) as [He [Hce _]].
      assert (Hss2 : rel_at (TApp (TApp D1 (TApp c2 e)) t) (TApp (TApp D1 (TApp c2 e)) t)
        (subst (TApp c2 e) y2 V2) (subst (TApp c2 e) y2 V2)).
      { eapply rel_at_conv; [exact Hss|apply cv_refl|apply cv_refl|apply HVV2, Hce|apply HVV2, Hce]. }
      pose proof (Hcd2 _ _ _ H2e Hs Hss2) as R2.
      destruct (Hcod _ _ _ H1e H2e) as [G3 [HG3 Hi3]].
      pose proof (Hi3 _ _ _ R1 R2) as R3.
      destruct (Gr_typed _ _ _ _ _ HG3 R3) as [_ [Hout [_ Hoo]]].
      exists G3; split; [exact HG3|].
      eapply Gr_closure; [exact HG3|exact R3|exact Ht| |exact Htt|].
      * apply closed_app; [apply closed_app; [apply comp_realizer_closed; assumption|exact He]|exact Ht].
      * eapply rel_at_conv; [exact Hoo|apply cv_refl|apply cv_sym, comp_realizer_beta; assumption|apply cv_refl|apply cv_refl].
  - intros f g h [Hf [Hg [Hff [Hgg Hfg]]]] [_ [Hh [_ [Hhh Hgh]]]].
    refine (conj Hf (conj Hh (conj Hff (conj Hhh _)))). intros e a H.
    destruct (Hmid e a H) as [H2e H1e]. destruct (Hcod _ _ _ H1e H2e) as [G3 [HG3 Hi3]].
    exists G3; split; [exact HG3|]. apply Hi3 with (TApp g (TApp c2 e)); [apply Hfg, H1e|apply Hgh, H2e].
Qed.

Lemma eq_graph_rel : forall A B G a b, rel_equiv G (eq_graph A B) -> G a b -> rel_at a b A B.
Proof. intros A B G a b HE H; apply HE in H; destruct H as [_ [_ Hr]]; exact Hr. Qed.

Theorem Gr_comp_both : forall A M G, Gr A M G ->
  (forall B G2, Gr M B G2 -> comp_ok A B G G2) /\ (forall A0 G0, Gr A0 A G0 -> comp_ok A0 M G0 G).
Proof.
  intros A M G H; induction H as
    [A B HAB
    |A B HA HB He
    |A B x U V y U' V' Gd Gc c D HA HB HAc HBc HGd IHd Hc Hreal HGc IHc HD Hcd
    |A B x E P y E' P' L L' HA HB HAc HE HBc HE' HN Hrows
    |A B IT F G0 i IT' F' G0' i' Gp HA HB HAc HBc HGp IHp
    |A B G G' HG IH HE].
  - split.
    + intros C G2 H2. eapply comp_eq_left; [apply gr_eq, HAB|exact HAB|intros a m [_ [_ Hr]]; exact Hr|exact H2].
    + intros A0 G0 H0. eapply comp_eq_right; [exact H0|apply gr_eq, HAB|exact HAB|intros m b [_ [_ Hr]]; exact Hr].
  - split.
    + intros C G2 H2. eapply comp_empty_left; [apply gr_empty; eassumption|exact (proj2 (Gr_tyw _ _ _ H2))|exact He].
    + intros A0 G0 H0. eapply comp_empty_right; [exact H0|exact HB|exact He].
  - assert (HG1 : Gr A B (pi_graph A B Gd Gc)) by (eapply gr_pi with (c := c) (D := D); eassumption).
    split.
    + intros C G2 H2. destruct (Gr_view _ _ _ H2) as
        [HMC HE2|HMw HCw He2 HE2|y2 U2 V2 w W X Gd2 Gc2 c2 D2 HMw HCw HM2c HCc HGd2 Hc2 Hreal2 Hcod2 HD2 Hcd2 HE2
        |? ? ? ? ? ? ? ? _ _ HM2c _ _ _ _ _ HE2|? ? ? ? ? ? ? ? ? _ _ HM2c _ _ HE2]; [| | |head_contra2|head_contra2].
      * eapply comp_eq_right; [exact HG1|exact H2|exact HMC|intros m b Hmb; eapply eq_graph_rel; eassumption].
      * eapply comp_empty_right; [exact HG1|exact HCw|exact He2].
      * eapply comp_ok_equiv; [|apply rel_equiv_refl|apply rel_equiv_sym, HE2].
        destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HBc) HM2c)) as [HUU2 HVV2].
        destruct (Gr_tyw _ _ _ HGd) as [HU'w _].
        apply (comp_pi A B C x U V y U' V' y2 U2 V2 w W X Gd Gc c D Gd2 Gc2 c2 D2); try assumption.
        -- apply (proj2 IHd). eapply Gr_transport_r; [exact HGd2|exact (tyw_conv_rty _ _ HU'w HUU2)].
        -- intros m a e Hd1 Hd2. apply (proj1 (IHc m a Hd1)).
           destruct (Gr_typed _ _ _ _ _ HGd Hd1) as [Hm _].
           eapply Gr_transport_l; [apply Hcod2, Hd2|].
           apply tyw_conv; [exact (proj1 (Gr_tyw _ _ _ (Hcod2 _ _ Hd2)))|apply cv_sym, HVV2, Hm].
    + intros A0 G0 H0. destruct (Gr_view _ _ _ H0) as
        [HA0A HE0|HA0w _ He0 HE0|x0 U0 V0 x2 U2 V2 Gd0 Gc0 c0 D0 HA0w _ HA0c HA2c HGd0 Hc0 Hreal0 Hcod0 HD0 Hcd0 HE0
        |? ? ? ? ? ? ? ? _ _ _ _ HA2c _ _ _ HE0|? ? ? ? ? ? ? ? ? _ _ _ HA2c _ HE0]; [| | |head_contra2|head_contra2].
      * eapply comp_eq_left; [exact H0|exact HA0A|intros a m Ham; eapply eq_graph_rel; eassumption|exact HG1].
      * eapply comp_empty_left; [exact H0|exact HB|exact He0].
      * eapply comp_ok_equiv; [|apply rel_equiv_sym, HE0|apply rel_equiv_refl].
        destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HA2c) HAc)) as [HU2U HV2V].
        destruct (Gr_tyw _ _ _ HGd0) as [_ HU0w].
        apply (comp_pi A0 A B x0 U0 V0 x2 U2 V2 x U V y U' V' Gd0 Gc0 c0 D0 Gd Gc c D); try assumption.
        -- apply (proj1 IHd). eapply Gr_transport_l; [exact HGd0|].
           apply tyw_conv; [exact (proj1 (Gr_tyw _ _ _ HGd0))|exact HU2U].
        -- intros m a e Hd0 Hd1. apply (proj2 (IHc e m Hd1)).
           destruct (Gr_typed _ _ _ _ _ HGd0 Hd0) as [Hm _].
           eapply Gr_transport_r; [apply Hcod0, Hd0|].
           apply tyw_conv; [exact (proj2 (Gr_tyw _ _ _ (Hcod0 _ _ Hd0)))|apply HV2V, Hm].
  - assert (HG1 : Gr A B (sum_graph A B x P y P' L L')) by (eapply gr_sum; eassumption).
    split.
    + intros C G2 H2. destruct (Gr_view _ _ _ H2) as
        [HMC HE2|HMw HCw He2 HE2|? ? ? ? ? ? ? ? ? ? _ _ HM2c _ _ _ _ _ _ _ HE2
        |y2 E2 P2 z E3 P3 L2 L3 HMw HCw HM2c HEE2 HCc HE3 HN3 Hrows2 HE2|? ? ? ? ? ? ? ? ? _ _ HM2c _ _ HE2];
        [| |head_contra2| |head_contra2].
      * eapply comp_eq_right; [exact HG1|exact H2|exact HMC|intros m b Hmb; eapply eq_graph_rel; eassumption].
      * eapply comp_empty_right; [exact HG1|exact HCw|exact He2].
      * eapply comp_ok_equiv; [|apply rel_equiv_refl|apply rel_equiv_sym, HE2].
        eapply comp_sum; eassumption.
    + intros A0 G0 H0. destruct (Gr_view _ _ _ H0) as
        [HA0A HE0|HA0w _ He0 HE0|? ? ? ? ? ? ? ? ? ? _ _ _ HA2c _ _ _ _ _ _ HE0
        |x0 E0 P0 x2 E2 P2 L0 L2 HA0w _ HA0c HEE0 HA2c HEE2 HN2 Hrows0 HE0|? ? ? ? ? ? ? ? ? _ _ _ HA2c _ HE0];
        [| |head_contra2| |head_contra2].
      * eapply comp_eq_left; [exact H0|exact HA0A|intros a m Ham; eapply eq_graph_rel; eassumption|exact HG1].
      * eapply comp_empty_left; [exact H0|exact HB|exact He0].
      * eapply comp_ok_equiv; [|apply rel_equiv_sym, HE0|apply rel_equiv_refl].
        eapply comp_sum; eassumption.
  - assert (HG1 : Gr A B (roll_graph A B Gp)) by (eapply gr_roll; eassumption).
    split.
    + intros C G2 H2. destruct (Gr_view _ _ _ H2) as
        [HMC HE2|HMw HCw He2 HE2|? ? ? ? ? ? ? ? ? ? _ _ HM2c _ _ _ _ _ _ _ HE2
        |? ? ? ? ? ? ? ? _ _ HM2c _ _ _ _ _ HE2|ITm Fm Gm im IT3 F3 G3 i3 Gp2 HMw HCw HM2c HCc HGp2 HE2];
        [| |head_contra2|head_contra2|].
      * eapply comp_eq_right; [exact HG1|exact H2|exact HMC|intros m b Hmb; eapply eq_graph_rel; eassumption].
      * eapply comp_empty_right; [exact HG1|exact HCw|exact He2].
      * eapply comp_ok_equiv; [|apply rel_equiv_refl|apply rel_equiv_sym, HE2].
        eapply comp_roll; [exact HA|exact HCw|exact HAc|exact HBc|exact HM2c|exact HCc|exact HGp2|].
        apply (proj1 IHp). eapply Gr_transport_l; [exact HGp2|].
        apply tyw_conv; [exact (proj1 (Gr_tyw _ _ _ HGp2))|eapply closeat_payload_conv; [exact HM2c|exact HBc]].
    + intros A0 Gz H0. destruct (Gr_view _ _ _ H0) as
        [HA0A HE0|HA0w _ He0 HE0|? ? ? ? ? ? ? ? ? ? _ _ _ HA2c _ _ _ _ _ _ HE0
        |? ? ? ? ? ? ? ? _ _ _ _ HA2c _ _ _ HE0|IT0 F0 G00 i0 ITa Fa Ga ia Gp0 HA0w _ HA0c HA2c HGp0 HE0];
        [| |head_contra2|head_contra2|].
      * eapply comp_eq_left; [exact H0|exact HA0A|intros a m Ham; eapply eq_graph_rel; eassumption|exact HG1].
      * eapply comp_empty_left; [exact H0|exact HB|exact He0].
      * eapply comp_ok_equiv; [|apply rel_equiv_sym, HE0|apply rel_equiv_refl].
        eapply comp_roll; [exact HA0w|exact HB|exact HA0c|exact HA2c|exact HAc|exact HBc|exact HGp|].
        apply (proj2 IHp). eapply Gr_transport_r; [exact HGp0|].
        apply tyw_conv; [exact (proj2 (Gr_tyw _ _ _ HGp0))|eapply closeat_payload_conv; [exact HA2c|exact HAc]].
  - split.
    + intros C G2 H2. eapply comp_ok_equiv; [apply (proj1 IH _ _ H2)|exact HE|apply rel_equiv_refl].
    + intros A0 G0 H0. eapply comp_ok_equiv; [apply (proj2 IH _ _ H0)|apply rel_equiv_refl|exact HE].
Qed.

Corollary Gr_comp : forall A M B G1 G2, Gr A M G1 -> Gr M B G2 -> comp_ok A B G1 G2.
Proof. intros; eapply (proj1 (Gr_comp_both _ _ _ H)); eassumption. Qed.
