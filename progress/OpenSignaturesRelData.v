(* Semantic rules for description interpretation, inductive families,
   close types, their constructors and the non-recursive case eliminator. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelSem.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Substitution facts for generated binders *)

Lemma subst_var_same : forall u x, subst u x (TVar x) = u.
Proof. intros; unfold subst; cbn [substitute]; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma subst_interp_app : forall a z IT E X,
  ~ In z (free_vars IT) -> ~ In z (free_vars E) -> ~ In z (free_vars X) ->
  subst a z (TInterp IT (TApp E (TVar z)) X) = TInterp IT (TApp E a) X.
Proof.
  intros a z IT E X H1 H2 H3.
  change (subst a z (TInterp IT (TApp E (TVar z)) X)) with
    (TInterp (subst a z IT) (TApp (subst a z E) (subst a z (TVar z))) (subst a z X)).
  rewrite subst_var_same, !subst_not_free by assumption; reflexivity.
Qed.

Lemma fresh_list_not_free : forall ts t, In t ts -> ~ In (fresh ts) (free_vars t).
Proof. exact fresh_not_free. Qed.
Ltac fresh_out := apply fresh_not_free; cbn; auto 10.

Lemma canonT_conv : forall k A A', conv A A' -> rel_equiv (canonT k A) (canonT k A').
Proof.
  intros k A A' H t u; split; intros [B [R [HR Ht]]]; exists B, R; split; try exact Ht;
    eapply interp_conv; [exact HR|exact H|apply cv_refl|exact HR|apply cv_sym; exact H|apply cv_refl].
Qed.

(* ------------------------------------------------------------------ *)
(* Interpretation of description codes as types *)

Lemma interp_conv_l : forall k A B R A', interp k A B R -> conv A' A -> interp k A' B R.
Proof. intros; eapply interp_conv; [eassumption|apply cv_sym; eassumption|apply cv_refl]. Qed.
Lemma interp_conv_both : forall k A B R A' B', interp k A B R -> conv A' A -> conv B' B -> interp k A' B' R.
Proof. intros; eapply interp_conv; [eassumption|apply cv_sym; eassumption|apply cv_sym; eassumption]. Qed.

Lemma interp_root_l : forall IT D X D0 t, conv D D0 -> root_step (TInterp IT D0 X) = Some t ->
  conv (TInterp IT D X) t.
Proof.
  intros IT D X D0 t H Hr.
  eapply cv_trans; [apply cv_compatible, cp_TInterp; [apply cv_refl|exact H|apply cv_refl]|].
  apply conv_root; exact Hr.
Qed.

Lemma interp_TInterp : forall RI Dl Dr F, D2 RI Dl Dr F -> per RI -> conv_closed RI ->
  forall k IT1 IT2 X1 X2 (Y : fam), fam_resp RI Y ->
  (forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 -> interp k (TApp X1 i1) (TApp X2 i2) (Y i1)) ->
  interp k (TInterp IT1 Dl X1) (TInterp IT2 Dr X2) (F Y).
Proof.
  intros RI Dl Dr F H HP HC; induction H; intros k IT1 IT2 X1 X2 Y HY HX.
  - (* variable *)
    eapply interp_conv_both; [apply HX; eassumption
      |eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
  - eapply interp_conv_both; [apply S2_interp, s2_unit; apply cv_refl
      |eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
  - eapply interp_equiv.
    + eapply interp_conv_both; [apply (S2_interp k); apply (s2_enum Bot Bot TNilE TNilE []); apply cv_refl
        |eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
    + intros t u; split; [intros [m [Hm _]]; cbn in Hm; lia|intros []].
  - (* product *)
    apply interp_conv_both with (A := product (TInterp IT1 A X1) (TInterp IT1 B X1))
      (B := product (TInterp IT2 A' X2) (TInterp IT2 B' X2));
      [|eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
    unfold product; eapply t2_sigma; [apply cv_refl|apply cv_refl|apply IHD2_1; eassumption|].
    intros a b Ha Hb Hab. rewrite !subst_not_free by fresh_out. apply IHD2_2; assumption.
  - (* function *)
    apply interp_conv_both with
      (A := TPi (fresh [IT1; A; E; X1]) A (TInterp IT1 (TApp E (TVar (fresh [IT1; A; E; X1]))) X1))
      (B := TPi (fresh [IT2; A'; E'; X2]) A' (TInterp IT2 (TApp E' (TVar (fresh [IT2; A'; E'; X2]))) X2));
      [|eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
    eapply t2_pi; [apply cv_refl|apply cv_refl|apply S2_interp; exact H5|].
    intros a b Ha Hb Hab. rewrite !subst_interp_app by fresh_out. apply H7; assumption.
  - (* dependent pair *)
    apply interp_conv_both with
      (A := TSigma (fresh [IT1; A; E; X1]) A (TInterp IT1 (TApp E (TVar (fresh [IT1; A; E; X1]))) X1))
      (B := TSigma (fresh [IT2; A'; E'; X2]) A' (TInterp IT2 (TApp E' (TVar (fresh [IT2; A'; E'; X2]))) X2));
      [|eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
    eapply t2_sigma; [apply cv_refl|apply cv_refl|apply S2_interp; exact H5|].
    intros a b Ha Hb Hab. rewrite !subst_interp_app by fresh_out. apply H7; assumption.
  - (* choice *)
    apply interp_conv_both with
      (A := TSigma (fresh [IT1; E; C; X1]) (TEnumT E) (TInterp IT1 (TApp C (TVar (fresh [IT1; E; C; X1]))) X1))
      (B := TSigma (fresh [IT2; E'; C'; X2]) (TEnumT E') (TInterp IT2 (TApp C' (TVar (fresh [IT2; E'; C'; X2]))) X2));
      [|eapply interp_root_l; [exact H|reflexivity]|eapply interp_root_l; [exact H0|reflexivity]].
    eapply t2_sigma; [apply cv_refl|apply cv_refl
      |apply S2_interp; eapply s2_enum; [apply cv_refl|apply cv_refl|eassumption|eassumption]|].
    intros e e' He He' [m [Hm [Hem He'm]]].
    rewrite !subst_interp_app by fresh_out.
    eapply interp_equiv; [eapply interp_conv_both; [apply H6; [exact Hm|exact HP|exact HC|exact HY|exact HX]
      |apply cv_compatible, cp_TInterp; [apply cv_refl|apply conv_app_a; exact Hem|apply cv_refl]
      |apply cv_compatible, cp_TInterp; [apply cv_refl|apply conv_app_a; exact He'm|apply cv_refl]]|].
    intros t u; split; [intros Ht; exists m; repeat apply conj; assumption|].
    intros [m' [Hm' [Hem' Ht]]].
    assert (m' = m) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hem'|exact Hem]).
    subst m'; exact Ht.
  - eapply interp_equiv; [apply IHD2; eassumption|apply H0; exact HY].
Qed.

(* ------------------------------------------------------------------ *)
(* Index families *)

Definition fam_of (k : nat) (X : term) : fam := fun i => canonT k (TApp X i).

Lemma subst_sort : forall u x k, subst u x (TSort k) = TSort k.
Proof. reflexivity. Qed.
Lemma subst_idesc_fresh : forall u x IT, ~ In x (free_vars IT) -> subst u x (TIDesc IT) = TIDesc IT.
Proof. intros; apply subst_not_free; cbn; assumption. Qed.

Lemma family_app : forall IT1 IT2 RI X1 X2 i1 i2, S2 IT1 IT2 RI ->
  rel_at X1 X2 (Family IT1) (Family IT2) -> closed i1 -> closed i2 -> RI i1 i2 ->
  ty_rel 0 (TApp X1 i1) (TApp X2 i2).
Proof.
  intros IT1 IT2 RI X1 X2 i1 i2 HI HX H1 H2 Hi; unfold Family in HX.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ HX (small_rel_at _ _ _ _ _ HI Hi) H1 H2) as H.
  rewrite !subst_sort in H; apply rel_at_sort, H.
Qed.

Lemma family_sem : forall IT1 IT2 RI X1 X2, S2 IT1 IT2 RI ->
  rel_at X1 X2 (Family IT1) (Family IT2) ->
  fam_resp RI (fam_of 0 X1) /\
  (forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 -> interp 0 (TApp X1 i1) (TApp X2 i2) (fam_of 0 X1 i1)).
Proof.
  intros IT1 IT2 RI X1 X2 HI HX.
  pose proof (S2_per _ _ _ HI) as HP.
  assert (Hint : forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 ->
    interp 0 (TApp X1 i1) (TApp X2 i2) (fam_of 0 X1 i1)).
  { intros i1 i2 H1 H2 Hi; destruct (family_app _ _ _ _ _ _ _ HI HX H1 H2 Hi) as [R HR].
    exact (canonT_interp _ _ _ _ HR). }
  split; [|exact Hint].
  intros i i' Hc Hc' [Hii|Hii].
  - pose proof (Hint i i' Hc Hc' Hii) as H1.
    pose proof (Hint i' i' Hc' Hc' (per_refl_right _ _ _ HP Hii)) as H2.
    exact (interp_unique_right _ _ _ _ _ _ _ _ H1 H2 (cv_refl _)).
  - apply canonT_conv, conv_app_a, Hii.
Qed.

Lemma def_app : forall IT1 IT2 RI D1 D2' j j', S2 IT1 IT2 RI ->
  rel_at D1 D2' (Def IT1) (Def IT2) -> closed j -> closed j' -> RI j j' ->
  D2 RI (TApp D1 j) (TApp D2' j') (canonL RI (TApp D1 j)).
Proof.
  intros IT1 IT2 RI D1 D2' j j' HI HD H1 H2 Hj; unfold Def in HD.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ HD (small_rel_at _ _ _ _ _ HI Hj) H1 H2) as H.
  rewrite !subst_idesc_fresh in H by fresh_out.
  destruct (rel_at_desc _ _ _ _ _ HI H) as [F HF].
  eapply D2_canonL; [exact HF|eapply S2_per|eapply S2_conv_closed]; exact HI.
Qed.

Definition mu_fun (RI : rel) (D : term) : ifunctor := fun j => canonL RI (TApp D j).

Lemma mu_fun_ok : forall IT1 IT2 RI D1 D2', S2 IT1 IT2 RI ->
  rel_at D1 D2' (Def IT1) (Def IT2) -> mu_ok RI (mu_fun RI D1).
Proof.
  intros IT1 IT2 RI D1 D2' HI HD.
  eapply mu_family_ok with (D' := D2'); [eapply S2_per; exact HI|eapply S2_conv_closed; exact HI| |].
  - intros j j' H1 H2 Hj; eapply def_app; eassumption.
  - intros j j' H1 H2 Hj; apply (proj2 S2_D2_claims); eapply def_app; eassumption.
Qed.

Lemma mu_closed_index : forall RI F i t u, mu_rel RI F i t u -> closed i.
Proof.
  intros RI F i t u H; apply (H (fun k _ _ => closed k)).
  - intros k k' Hk Hk' _ a b; split; intros _; assumption.
  - intros j a b Hj _ _; exact Hj.
Qed.

(* ------------------------------------------------------------------ *)
(* Inductive families *)

Lemma family_ty : forall IT1 IT2, rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  ty_rel 1 (Family IT1) (Family IT2).
Proof.
  intros IT1 IT2 HI; unfold Family. replace 1 with (Nat.max 0 1) by reflexivity.
  apply sem_pi; [apply rel_at_sort, HI|intros; rewrite !subst_sort; exists (univ_rel 0); apply sort_interp].
Qed.
Lemma def_ty : forall IT1 IT2, rel_at IT1 IT2 (TSort 0) (TSort 0) -> ty_rel 1 (Def IT1) (Def IT2).
Proof.
  intros IT1 IT2 HI; unfold Def. replace 1 with (Nat.max 0 1) by reflexivity.
  apply sem_pi; [apply rel_at_sort, HI|intros a1 a2 _ _ _].
  rewrite !subst_idesc_fresh by fresh_out. apply sem_idesc, HI.
Qed.
Lemma family_intro : forall IT1 IT2 X1 X2, rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  (forall i1 i2, closed i1 -> closed i2 -> rel_at i1 i2 IT1 IT2 -> ty_rel 0 (TApp X1 i1) (TApp X2 i2)) ->
  rel_at X1 X2 (Family IT1) (Family IT2).
Proof.
  intros IT1 IT2 X1 X2 HI HX; unfold Family in *.
  eapply sem_pi_intro; [apply (family_ty _ _ HI)|].
  intros a1 a2 H1 H2 Ha; rewrite !subst_sort; apply rel_at_sort, HX; assumption.
Qed.

Lemma mu_type_interp : forall IT1 IT2 RI D1 D2' i1 i2, S2 IT1 IT2 RI ->
  rel_at D1 D2' (Def IT1) (Def IT2) -> closed i1 -> closed i2 -> RI i1 i2 ->
  interp 0 (MuAt IT1 D1 i1) (MuAt IT2 D2' i2) (mu_rel RI (mu_fun RI D1) i1).
Proof.
  intros IT1 IT2 RI D1 D2' i1 i2 HI HD Hc1 Hc2 Hi.
  apply S2_interp; eapply s2_mu; [apply cv_refl|apply cv_refl|exact HI|exact Hc1|exact Hc2|exact Hi|].
  intros j j' Hj1 Hj2 Hj; eapply def_app; eassumption.
Qed.

Lemma sem_mui : forall IT1 IT2 D1 D2', rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at D1 D2' (Def IT1) (Def IT2) ->
  rel_at (TMuI IT1 D1) (TMuI IT2 D2') (Family IT1) (Family IT2).
Proof.
  intros IT1 IT2 D1 D2' HIT HD; destruct (small_of_rel _ _ HIT) as [RI HI].
  apply family_intro; [exact HIT|]. intros i1 i2 H1 H2 Hi.
  eexists; apply (mu_type_interp IT1 IT2 RI); try eassumption. eapply rel_at_small; eassumption.
Qed.

(* The semantic family of the fixed point agrees with the fixed point. *)
Definition live_fam (RI : rel) (Y : fam) : fam := fun j t u => closed j /\ RI j j /\ Y j t u.

Lemma live_fam_resp : forall RI Y, per RI -> conv_closed RI -> fam_resp RI Y -> fam_resp RI (live_fam RI Y).
Proof.
  intros RI Y HP HC HY i i' Hc Hc' Hi t u; unfold live_fam.
  assert (Hrr : RI i i <-> RI i' i').
  { destruct Hi as [Hi|Hi]; split; intro H.
    - eapply per_refl_right; eassumption.
    - eapply per_refl_left; eassumption.
    - eapply HC; [exact H|exact Hi|exact Hi].
    - eapply HC; [exact H|apply cv_sym; exact Hi|apply cv_sym; exact Hi]. }
  pose proof (HY i i' Hc Hc' Hi t u) as HE; tauto.
Qed.

Lemma mu_family_equiv : forall IT1 IT2 RI D1 D2', S2 IT1 IT2 RI ->
  rel_at D1 D2' (Def IT1) (Def IT2) ->
  fam_equiv (live_fam RI (fam_of 0 (TMuI IT1 D1))) (mu_rel RI (mu_fun RI D1)).
Proof.
  intros IT1 IT2 RI D1 D2' HI HD j t u; split.
  - intros [Hc [Hj Ht]].
    exact (rel_equiv_l _ _ _ _ (canonT_equiv _ _ _ _ (mu_type_interp _ _ _ _ _ _ _ HI HD Hc Hc Hj)) Ht).
  - intros Hm; pose proof (mu_closed_index _ _ _ _ _ Hm) as Hc.
    pose proof (mu_fun_ok _ _ _ _ _ HI HD) as Hok. destruct Hok as [HP [HC [HR HG]]].
    assert (Hj : RI j j) by (eapply mu_index; try eassumption; intros k Hk Hkk; apply (HG k Hk Hkk)).
    refine (conj Hc (conj Hj _)).
    exact (rel_equiv_r _ _ _ _ (canonT_equiv _ _ _ _ (mu_type_interp _ _ _ _ _ _ _ HI HD Hc Hc Hj)) Hm).
Qed.

Lemma live_fam_interp : forall RI X1 X2 (Y : fam), per RI ->
  (forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 -> interp 0 (TApp X1 i1) (TApp X2 i2) (Y i1)) ->
  forall i1 i2, closed i1 -> closed i2 -> RI i1 i2 ->
    interp 0 (TApp X1 i1) (TApp X2 i2) (live_fam RI Y i1).
Proof.
  intros RI X1 X2 Y HP HY i1 i2 H1 H2 Hi. eapply interp_equiv; [apply HY; assumption|].
  intros t u; unfold live_fam; split;
    [intros Ht; repeat apply conj; [assumption|eapply per_refl_left; eassumption|exact Ht]
    |intros [_ [_ Ht]]; exact Ht].
Qed.

Lemma sem_in_mu : forall IT1 IT2 D1 D2' i1 i2 xs1 xs2,
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (Def IT1) (Def IT2) ->
  rel_at i1 i2 IT1 IT2 -> closed i1 -> closed i2 -> closed xs1 -> closed xs2 ->
  rel_at xs1 xs2 (TInterp IT1 (TApp D1 i1) (TMuI IT1 D1)) (TInterp IT2 (TApp D2' i2) (TMuI IT2 D2')) ->
  rel_at (TIn xs1) (TIn xs2) (MuAt IT1 D1 i1) (MuAt IT2 D2' i2).
Proof.
  intros IT1 IT2 D1 D2' i1 i2 xs1 xs2 HIT HD Hi Hc1 Hc2 Hx1 Hx2 Hxs.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
  pose proof (rel_at_small _ _ _ _ _ HI Hi) as Hii.
  pose proof (mu_fun_ok _ _ _ _ _ HI HD) as Hok.
  destruct (family_sem _ _ _ _ _ HI (sem_mui _ _ _ _ HIT HD)) as [HYr HYi].
  set (Y := live_fam RI (fam_of 0 (TMuI IT1 D1))).
  assert (HYr' : fam_resp RI Y) by (apply live_fam_resp; assumption).
  pose proof (live_fam_interp _ _ _ _ HP HYi) as HYi'.
  pose proof (interp_TInterp _ _ _ _ (def_app _ _ _ _ _ _ _ HI HD Hc1 Hc2 Hii) HP HC 0
    IT1 IT2 (TMuI IT1 D1) (TMuI IT2 D2') Y HYr' HYi') as Hpay.
  pose proof (rel_at_transfer _ _ _ _ _ _ _ _ Hxs Hpay (cv_refl _)) as Hxs'.
  destruct Hok as [_ [_ [HR HG]]].
  assert (Hxs'' : mu_fun RI D1 i1 (mu_rel RI (mu_fun RI D1)) xs1 xs2).
  { destruct (HG i1 Hc1 (per_refl_left _ _ _ HP Hii)) as [Hm _].
    eapply (Hm Y); [exact HYr'|apply mu_resp| |exact Hxs'].
    intros j a b; apply (mu_family_equiv _ _ _ _ _ HI HD). }
  exists 0, (mu_rel RI (mu_fun RI D1) i1); split; [apply mu_type_interp; assumption|].
  apply mu_fold; [intros j Hj Hjj; apply (proj1 (HG j Hj Hjj))|exact Hc1|eapply per_refl_left; eassumption|].
  exists xs1, xs2; repeat apply conj; [exact Hx1|exact Hx2|apply cv_refl|apply cv_refl|exact Hxs''].
Qed.

(* ------------------------------------------------------------------ *)
(* Close types *)

Lemma close_type_interp : forall IT1 IT2 RI F1 F2 G1 G2 i1 i2, S2 IT1 IT2 RI ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  closed i1 -> closed i2 -> RI i1 i2 ->
  interp 0 (CloseAt IT1 F1 G1 i1) (CloseAt IT2 F2 G2 i2)
    (roll (canonL RI (TApp F1 i1) (mu_rel RI (mu_fun RI G1)))).
Proof.
  intros IT1 IT2 RI F1 F2 G1 G2 i1 i2 HI HF HG H1 H2 Hi.
  apply S2_interp; eapply s2_close; [apply cv_refl|apply cv_refl|exact HI|exact H1|exact H2|exact Hi
    |eapply def_app; eassumption|].
  intros j j' Hj1 Hj2 Hj; eapply def_app; eassumption.
Qed.

Lemma sem_close : forall IT1 IT2 F1 F2 G1 G2, rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  rel_at (TClose IT1 F1 G1) (TClose IT2 F2 G2) (Family IT1) (Family IT2).
Proof.
  intros IT1 IT2 F1 F2 G1 G2 HIT HF HG; destruct (small_of_rel _ _ HIT) as [RI HI].
  apply family_intro; [exact HIT|]. intros i1 i2 H1 H2 Hi.
  eexists; apply (close_type_interp IT1 IT2 RI); try eassumption. eapply rel_at_small; eassumption.
Qed.

Lemma carrier_family_equiv : forall IT1 IT2 RI G1 G2, S2 IT1 IT2 RI ->
  rel_at G1 G2 (Def IT1) (Def IT2) ->
  fam_equiv (live_fam RI (fam_of 0 (carrier IT1 G1))) (mu_rel RI (mu_fun RI G1)).
Proof.
  intros IT1 IT2 RI G1 G2 HI HG j t u.
  pose proof (mu_fun_ok _ _ _ _ _ HI HG) as Hok.
  split.
  - intros [Hc [Hj Ht]].
    pose proof (rel_equiv_l _ _ _ _ (canonT_equiv _ _ _ _
      (close_type_interp _ _ _ _ _ _ _ _ _ HI HG HG Hc Hc Hj)) Ht) as Hr.
    exact (proj2 (mu_ok_unfold _ _ Hok j t u Hc Hj) Hr).
  - intros Hm; pose proof (mu_closed_index _ _ _ _ _ Hm) as Hc.
    pose proof Hok as [HP [HC [HR HGd]]].
    assert (Hj : RI j j) by (eapply mu_index; try eassumption; intros k Hk Hkk; apply (HGd k Hk Hkk)).
    refine (conj Hc (conj Hj _)).
    apply (rel_equiv_r _ _ _ _ (canonT_equiv _ _ _ _ (close_type_interp _ _ _ _ _ _ _ _ _ HI HG HG Hc Hc Hj))).
    exact (proj1 (mu_ok_unfold _ _ Hok j t u Hc Hj) Hm).
Qed.

(* The payload of a close type at related data is the unrolled relation. *)
Lemma payload_interp : forall IT1 IT2 RI F1 F2 G1 G2 i1 i2, S2 IT1 IT2 RI ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  closed i1 -> closed i2 -> RI i1 i2 ->
  interp 0 (payload IT1 F1 G1 i1) (payload IT2 F2 G2 i2)
    (canonL RI (TApp F1 i1) (mu_rel RI (mu_fun RI G1))).
Proof.
  intros IT1 IT2 RI F1 F2 G1 G2 i1 i2 HI HIT HF HG H1 H2 Hi.
  pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
  destruct (family_sem _ _ _ _ _ HI (sem_close _ _ _ _ _ _ HIT HG HG)) as [HYr HYi].
  set (Y := live_fam RI (fam_of 0 (carrier IT1 G1))).
  assert (HYr' : fam_resp RI Y) by (apply live_fam_resp; assumption).
  pose proof (live_fam_interp _ _ _ _ HP HYi) as HYi'.
  pose proof (def_app _ _ _ _ _ _ _ HI HF H1 H2 Hi) as HDF.
  pose proof (interp_TInterp _ _ _ _ HDF HP HC 0 IT1 IT2 (carrier IT1 G1) (carrier IT2 G2) Y HYr' HYi') as Hpay.
  eapply interp_equiv; [exact Hpay|].
  destruct (D2_good _ _ _ _ HDF HP HC) as [Hm _].
  apply fmono_equiv with (RI := RI); [exact Hm|exact HYr'|apply mu_resp|].
  apply carrier_family_equiv with IT2 G2; assumption.
Qed.

Lemma sem_in_close : forall IT1 IT2 F1 F2 G1 G2 i1 i2 xs1 xs2,
  rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  rel_at i1 i2 IT1 IT2 -> closed i1 -> closed i2 -> closed xs1 -> closed xs2 ->
  rel_at xs1 xs2 (payload IT1 F1 G1 i1) (payload IT2 F2 G2 i2) ->
  rel_at (TIn xs1) (TIn xs2) (CloseAt IT1 F1 G1 i1) (CloseAt IT2 F2 G2 i2).
Proof.
  intros IT1 IT2 F1 F2 G1 G2 i1 i2 xs1 xs2 HIT HF HG Hi H1 H2 Hx1 Hx2 Hxs.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  pose proof (rel_at_small _ _ _ _ _ HI Hi) as Hii.
  exists 0, (roll (canonL RI (TApp F1 i1) (mu_rel RI (mu_fun RI G1)))); split;
    [apply close_type_interp; assumption|].
  exists xs1, xs2; refine (conj Hx1 (conj Hx2 (conj (cv_refl _) (conj (cv_refl _) _)))).
  eapply rel_at_transfer; [exact Hxs|apply (payload_interp IT1 IT2 RI F1 F2 G1 G2 i1 i2); assumption|apply cv_refl].
Qed.

Lemma close_case_method_subst : forall IT F G i Q xs,
  subst xs (fresh [IT; F; G; i; Q]) (TApp Q (TIn (TVar (fresh [IT; F; G; i; Q])))) = TApp Q (TIn xs).
Proof.
  intros. change (subst xs (fresh [IT; F; G; i; Q]) (TApp Q (TIn (TVar (fresh [IT; F; G; i; Q]))))) with
    (TApp (subst xs (fresh [IT; F; G; i; Q]) Q) (TIn (subst xs (fresh [IT; F; G; i; Q]) (TVar (fresh [IT; F; G; i; Q]))))).
  rewrite subst_var_same, subst_not_free by fresh_out; reflexivity.
Qed.

Lemma sem_close_case : forall k IT1 IT2 F1 F2 G1 G2 i1 i2 Q1 Q2 b1 b2 x1 x2,
  rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  rel_at i1 i2 IT1 IT2 -> closed i1 -> closed i2 ->
  rel_at b1 b2 (close_case_method IT1 F1 G1 i1 Q1) (close_case_method IT2 F2 G2 i2 Q2) ->
  rel_at x1 x2 (CloseAt IT1 F1 G1 i1) (CloseAt IT2 F2 G2 i2) ->
  rel_at (TCloseCase k IT1 F1 G1 i1 Q1 b1 x1) (TCloseCase k IT2 F2 G2 i2 Q2 b2 x2)
    (TApp Q1 x1) (TApp Q2 x2).
Proof.
  intros k IT1 IT2 F1 F2 G1 G2 i1 i2 Q1 Q2 b1 b2 x1 x2 HIT HF HG Hi H1 H2 Hb Hx.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  pose proof (rel_at_small _ _ _ _ _ HI Hi) as Hii.
  pose proof (rel_at_transfer _ _ _ _ _ _ _ _ Hx (close_type_interp _ _ _ _ _ _ _ _ _ HI HF HG H1 H2 Hii) (cv_refl _))
    as [xs1 [xs2 [Hx1 [Hx2 [Hc1 [Hc2 Hr]]]]]].
  assert (Hxs : rel_at xs1 xs2 (payload IT1 F1 G1 i1) (payload IT2 F2 G2 i2)).
  { exists 0, (canonL RI (TApp F1 i1) (mu_rel RI (mu_fun RI G1))); split; [apply payload_interp; assumption|exact Hr]. }
  unfold close_case_method in Hb.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hb Hxs Hx1 Hx2) as Happ.
  rewrite !close_case_method_subst in Happ.
  eapply rel_at_conv; [exact Happ| | |apply conv_app_a, cv_sym, Hc1|apply conv_app_a, cv_sym, Hc2].
  - apply cv_trans with (u := TCloseCase k IT1 F1 G1 i1 Q1 b1 (TIn xs1)).
    + apply cv_sym, conv_root; reflexivity.
    + apply cv_compatible, cp_TCloseCase; try apply cv_refl. apply cv_sym, Hc1.
  - apply cv_trans with (u := TCloseCase k IT2 F2 G2 i2 Q2 b2 (TIn xs2)).
    + apply cv_sym, conv_root; reflexivity.
    + apply cv_compatible, cp_TCloseCase; try apply cv_refl. apply cv_sym, Hc2.
Qed.
