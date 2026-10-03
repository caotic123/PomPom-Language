(* Semantic rules for the description eliminators: the hypothesis type
   TIAll, the hypothesis builder THyps, and the induction principles. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelData.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Structural substitution equations *)

Lemma subst_app : forall u x a b, subst u x (TApp a b) = TApp (subst u x a) (subst u x b).
Proof. reflexivity. Qed.
Lemma subst_pair : forall u x a b, subst u x (TPair a b) = TPair (subst u x a) (subst u x b).
Proof. reflexivity. Qed.
Lemma subst_in : forall u x a, subst u x (TIn a) = TIn (subst u x a).
Proof. reflexivity. Qed.
Lemma subst_interp : forall u x a b c, subst u x (TInterp a b c) = TInterp (subst u x a) (subst u x b) (subst u x c).
Proof. reflexivity. Qed.
Lemma subst_iall : forall u x a b c d e,
  subst u x (TIAll a b c d e) = TIAll (subst u x a) (subst u x b) (subst u x c) (subst u x d) (subst u x e).
Proof. reflexivity. Qed.
Lemma subst_hyps : forall u x a b c d e f,
  subst u x (THyps a b c d e f) = THyps (subst u x a) (subst u x b) (subst u x c) (subst u x d) (subst u x e) (subst u x f).
Proof. reflexivity. Qed.
Lemma subst_ind : forall u x a b c d e f,
  subst u x (TInd a b c d e f) = TInd (subst u x a) (subst u x b) (subst u x c) (subst u x d) (subst u x e) (subst u x f).
Proof. reflexivity. Qed.
Lemma subst_closeind : forall u x a b c d e f g,
  subst u x (TCloseInd a b c d e f g) =
  TCloseInd (subst u x a) (subst u x b) (subst u x c) (subst u x d) (subst u x e) (subst u x f) (subst u x g).
Proof. reflexivity. Qed.
Lemma subst_mui : forall u x a b, subst u x (TMuI a b) = TMuI (subst u x a) (subst u x b).
Proof. reflexivity. Qed.
Lemma subst_closeterm : forall u x a b c, subst u x (TClose a b c) = TClose (subst u x a) (subst u x b) (subst u x c).
Proof. reflexivity. Qed.
Lemma subst_fst : forall u x a, subst u x (TFst a) = TFst (subst u x a).
Proof. reflexivity. Qed.
Lemma subst_snd : forall u x a, subst u x (TSnd a) = TSnd (subst u x a).
Proof. reflexivity. Qed.
Lemma subst_var_other : forall u x y, x <> y -> subst u x (TVar y) = TVar y.
Proof. intros u x y H; unfold subst; cbn [substitute]; rewrite (proj2 (Nat.eqb_neq y x)) by auto; reflexivity. Qed.
Lemma subst_pi_closed : forall u x y A B, closed u -> x <> y ->
  subst u x (TPi y A B) = TPi y (subst u x A) (subst u x B).
Proof. intros; apply subst_closed_pi; assumption. Qed.
Lemma subst_lam_closed : forall u x y b, closed u -> x <> y ->
  subst u x (TLam y b) = TLam y (subst u x b).
Proof. intros; apply subst_closed_lam; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* Semantic motives and recursive hypotheses *)

Definition mot_rel (RI : rel) (Y : fam) (P1 P2 : term) :=
  forall i1 i2 x1 x2, closed i1 -> closed i2 -> closed x1 -> closed x2 ->
    RI i1 i2 -> Y i1 x1 x2 -> ty_rel 0 (TApp P1 (TPair i1 x1)) (TApp P2 (TPair i2 x2)).
Definition hyp_rel (RI : rel) (Y : fam) (P1 P2 h1 h2 : term) :=
  forall i1 i2 x1 x2, closed i1 -> closed i2 -> closed x1 -> closed x2 ->
    RI i1 i2 -> Y i1 x1 x2 ->
    rel_at (TApp (TApp h1 i1) x1) (TApp (TApp h2 i2) x2)
      (TApp P1 (TPair i1 x1)) (TApp P2 (TPair i2 x2)).

Lemma iall_root : forall IT D X x P D0 t, conv D D0 ->
  root_step (TIAll IT D0 X x P) = Some t -> conv (TIAll IT D X x P) t.
Proof.
  intros IT D X x P D0 t H Hr.
  apply cv_trans with (u := TIAll IT D0 X x P); [apply cv_compatible, cp_TIAll; try apply cv_refl; exact H|].
  apply conv_root; exact Hr.
Qed.
Lemma iall_root2 : forall IT D X x P D0 x0 t, conv D D0 -> conv x x0 ->
  root_step (TIAll IT D0 X x0 P) = Some t -> conv (TIAll IT D X x P) t.
Proof.
  intros IT D X x P D0 x0 t H Hx Hr.
  apply cv_trans with (u := TIAll IT D0 X x0 P); [apply cv_compatible, cp_TIAll; try apply cv_refl; assumption|].
  apply conv_root; exact Hr.
Qed.
Lemma hyps_root : forall IT D X P h x D0 t, conv D D0 ->
  root_step (THyps IT D0 X P h x) = Some t -> conv (THyps IT D X P h x) t.
Proof.
  intros IT D X P h x D0 t H Hr.
  apply cv_trans with (u := THyps IT D0 X P h x); [apply cv_compatible, cp_THyps; try apply cv_refl; exact H|].
  apply conv_root; exact Hr.
Qed.
Lemma hyps_root2 : forall IT D X P h x D0 x0 t, conv D D0 -> conv x x0 ->
  root_step (THyps IT D0 X P h x0) = Some t -> conv (THyps IT D X P h x) t.
Proof.
  intros IT D X P h x D0 x0 t H Hx Hr.
  apply cv_trans with (u := THyps IT D0 X P h x0); [apply cv_compatible, cp_THyps; try apply cv_refl; assumption|].
  apply conv_root; exact Hr.
Qed.

Lemma closed_pair_inv : forall a b, closed (TPair a b) -> closed a /\ closed b.
Proof.
  unfold closed; intros a b H; cbn in H.
  destruct (free_vars a), (free_vars b); cbn in *; try discriminate; auto.
Qed.

Lemma sem_iall_gen : forall RI Dl Dr F, D2 RI Dl Dr F -> per RI -> conv_closed RI ->
  forall IT1 IT2 X1 X2 P1 P2 (Y : fam), fam_resp RI Y -> mot_rel RI Y P1 P2 ->
  forall xs1 xs2, closed xs1 -> closed xs2 -> F Y xs1 xs2 ->
  ty_rel 0 (TIAll IT1 Dl X1 xs1 P1) (TIAll IT2 Dr X2 xs2 P2).
Proof.
  intros RI Dl Dr F H HP HC; induction H; intros IT1 IT2 X1 X2 P1 P2 Y HY HM xs1 xs2 Hc1 Hc2 Hxs.
  - eapply ty_rel_conv; [apply (HM i i' xs1 xs2 H1 H2 Hc1 Hc2 H3 Hxs)| |].
    + apply cv_sym; eapply iall_root; [exact H|reflexivity].
    + apply cv_sym; eapply iall_root; [exact H0|reflexivity].
  - destruct Hxs as [Hu1 Hu2].
    eapply ty_rel_conv; [apply (sem_unitT 0)| |].
    + apply cv_sym; eapply iall_root2; [exact H|exact Hu1|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H0|exact Hu2|reflexivity].
  - contradiction.
  - destruct Hxs as [a1 [b1 [a2 [b2 [Ha1 [Hb1 [Ha2 [Hb2 [Hp1 [Hp2 [HA HB]]]]]]]]]]].
    eapply ty_rel_conv; [|apply cv_sym; eapply iall_root2; [exact H|exact Hp1|reflexivity]
      |apply cv_sym; eapply iall_root2; [exact H0|exact Hp2|reflexivity]].
    replace 0 with (Nat.max 0 0) by reflexivity.
    apply sem_product; [eapply IHD2_1|eapply IHD2_2]; eassumption.
  - eapply ty_rel_conv; [|apply cv_sym; eapply iall_root; [exact H|reflexivity]
      |apply cv_sym; eapply iall_root; [exact H0|reflexivity]].
    replace 0 with (Nat.max 0 0) by reflexivity.
    apply sem_pi; [eapply small_ty_rel; exact H5|].
    intros a1 a2 Ha1 Ha2 Ha.
    rewrite !subst_iall, !subst_app, !subst_var_same, !(subst_not_free IT1), !(subst_not_free IT2),
      !(subst_not_free E), !(subst_not_free E'), !(subst_not_free X1), !(subst_not_free X2),
      !(subst_not_free xs1), !(subst_not_free xs2), !(subst_not_free P1), !(subst_not_free P2)
      by fresh_out.
    pose proof (rel_at_small _ _ _ _ _ H5 Ha) as HRA.
    eapply H7; [exact Ha1|exact Ha2|exact HRA|exact HP|exact HC|exact HY|exact HM
      |apply closed_app; assumption|apply closed_app; assumption|apply Hxs; assumption].
  - destruct Hxs as [a1 [b1 [a2 [b2 [Ha1 [Hb1 [Ha2 [Hb2 [Hp1 [Hp2 [HA HB]]]]]]]]]]].
    eapply ty_rel_conv; [|apply cv_sym; eapply iall_root2; [exact H|exact Hp1|reflexivity]
      |apply cv_sym; eapply iall_root2; [exact H0|exact Hp2|reflexivity]].
    eapply H7; [exact Ha1|exact Ha2|exact HA|exact HP|exact HC|exact HY|exact HM|exact Hb1|exact Hb2|exact HB].
  - destruct Hxs as [e1 [b1 [e2 [b2 [He1 [Hb1 [He2 [Hb2 [Hp1 [Hp2 [HE [m [Hm [Hem HB]]]]]]]]]]]]]].
    destruct HE as [m' [Hm' [Hem' He'm']]].
    assert (m' = m) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hem'|exact Hem]).
    subst m'.
    eapply ty_rel_conv; [|apply cv_sym; eapply iall_root2; [exact H|exact Hp1|reflexivity]
      |apply cv_sym; eapply iall_root2; [exact H0|exact Hp2|reflexivity]].
    eapply ty_rel_conv; [eapply H6; [exact Hm|exact HP|exact HC|exact HY|exact HM|exact Hb1|exact Hb2|exact HB]| |].
    + apply cv_compatible, cp_TIAll; try apply cv_refl. apply conv_app_a, cv_sym, Hem.
    + apply cv_compatible, cp_TIAll; try apply cv_refl. apply conv_app_a, cv_sym, He'm'.
  - eapply IHD2; try eassumption. apply (H0 Y HY), Hxs.
Qed.

Lemma closed_hyps : forall a b c d e f, closed a -> closed b -> closed c -> closed d ->
  closed e -> closed f -> closed (THyps a b c d e f).
Proof. unfold closed; intros; cbn [free_vars]; repeat match goal with H : free_vars _ = [] |- _ => rewrite H end; reflexivity. Qed.
Lemma closed_iall : forall a b c d e, closed a -> closed b -> closed c -> closed d ->
  closed e -> closed (TIAll a b c d e).
Proof. unfold closed; intros; cbn [free_vars]; repeat match goal with H : free_vars _ = [] |- _ => rewrite H end; reflexivity. Qed.

Lemma sem_hyps_gen : forall RI Dl Dr F, D2 RI Dl Dr F -> per RI -> conv_closed RI ->
  forall IT1 IT2 X1 X2 P1 P2 h1 h2 (Y : fam), fam_resp RI Y -> mot_rel RI Y P1 P2 ->
  hyp_rel RI Y P1 P2 h1 h2 ->
  closed IT1 -> closed IT2 -> closed X1 -> closed X2 -> closed P1 -> closed P2 ->
  closed h1 -> closed h2 ->
  forall xs1 xs2, closed xs1 -> closed xs2 -> F Y xs1 xs2 ->
  rel_at (THyps IT1 Dl X1 P1 h1 xs1) (THyps IT2 Dr X2 P2 h2 xs2)
    (TIAll IT1 Dl X1 xs1 P1) (TIAll IT2 Dr X2 xs2 P2).
Proof.
  intros RI Dl Dr F H HP HC; induction H; intros IT1 IT2 X1 X2 P1 P2 h1 h2 Y HY HM HH
    HcI1 HcI2 HcX1 HcX2 HcP1 HcP2 Hch1 Hch2 xs1 xs2 Hc1 Hc2 Hxs.
  - eapply rel_at_conv; [apply (HH i i' xs1 xs2 H1 H2 Hc1 Hc2 H3 Hxs)| | | |].
    + apply cv_sym; eapply hyps_root; [exact H|reflexivity].
    + apply cv_sym; eapply hyps_root; [exact H0|reflexivity].
    + apply cv_sym; eapply iall_root; [exact H|reflexivity].
    + apply cv_sym; eapply iall_root; [exact H0|reflexivity].
  - destruct Hxs as [Hu1 Hu2].
    eapply rel_at_conv; [apply sem_unit| | | |].
    + apply cv_sym; eapply hyps_root2; [exact H|exact Hu1|reflexivity].
    + apply cv_sym; eapply hyps_root2; [exact H0|exact Hu2|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H|exact Hu1|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H0|exact Hu2|reflexivity].
  - contradiction.
  - destruct Hxs as [a1 [b1 [a2 [b2 [Ha1 [Hb1 [Ha2 [Hb2 [Hp1 [Hp2 [HA HB]]]]]]]]]]].
    assert (Hpair : rel_at (TPair (THyps IT1 A X1 P1 h1 a1) (THyps IT1 B X1 P1 h1 b1))
      (TPair (THyps IT2 A' X2 P2 h2 a2) (THyps IT2 B' X2 P2 h2 b2))
      (product (TIAll IT1 A X1 a1 P1) (TIAll IT1 B X1 b1 P1))
      (product (TIAll IT2 A' X2 a2 P2) (TIAll IT2 B' X2 b2 P2))).
    { apply sem_product_pair with (k := 0).
      - replace 0 with (Nat.max 0 0) by reflexivity.
        apply sem_product; [eapply (sem_iall_gen RI A A' FA)|eapply (sem_iall_gen RI B B' FB)]; eassumption.
      - apply closed_hyps; assumption.
      - apply closed_hyps; assumption.
      - apply closed_hyps; assumption.
      - apply closed_hyps; assumption.
      - eapply IHD2_1; eassumption.
      - eapply IHD2_2; eassumption. }
    eapply rel_at_conv; [exact Hpair| | | |].
    + apply cv_sym; eapply hyps_root2; [exact H|exact Hp1|reflexivity].
    + apply cv_sym; eapply hyps_root2; [exact H0|exact Hp2|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H|exact Hp1|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H0|exact Hp2|reflexivity].
  - set (z1 := fresh [IT1; A; E; X1; P1; h1; xs1]).
    set (z2 := fresh [IT2; A'; E'; X2; P2; h2; xs2]).
    set (w1 := fresh [IT1; A; E; X1; xs1; P1]).
    set (w2 := fresh [IT2; A'; E'; X2; xs2; P2]).
    assert (HT : ty_rel 0 (TIAll IT1 D X1 xs1 P1) (TIAll IT2 D' X2 xs2 P2)).
    { eapply (sem_iall_gen RI D D' (fun X => pi_rel RA (fun a _ => FE a X)));
        [eapply d2_pi; eassumption|exact HP|exact HC|exact HY|exact HM|exact Hc1|exact Hc2|exact Hxs]. }
    eapply rel_at_conv; [eapply sem_lam with
      (x' := w1) (A1 := A) (B1 := TIAll IT1 (TApp E (TVar w1)) X1 (TApp xs1 (TVar w1)) P1)
      (y' := w2) (A2 := A') (B2 := TIAll IT2 (TApp E' (TVar w2)) X2 (TApp xs2 (TVar w2)) P2)
      (x := z1) (b1 := THyps IT1 (TApp E (TVar z1)) X1 P1 h1 (TApp xs1 (TVar z1)))
      (y := z2) (b2 := THyps IT2 (TApp E' (TVar z2)) X2 P2 h2 (TApp xs2 (TVar z2)))| | | |].
    + eapply ty_rel_conv; [exact HT| |].
      * eapply iall_root; [exact H|reflexivity].
      * eapply iall_root; [exact H0|reflexivity].
    + intros a1 a2 Ha1 Ha2 Ha.
      rewrite !subst_hyps, !subst_iall, !subst_app, !subst_var_same.
      rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free E), !(subst_not_free E'),
        !(subst_not_free X1), !(subst_not_free X2), !(subst_not_free P1), !(subst_not_free P2),
        !(subst_not_free h1), !(subst_not_free h2), !(subst_not_free xs1), !(subst_not_free xs2)
        by fresh_out.
      pose proof (rel_at_small _ _ _ _ _ H5 Ha) as HRA.
      eapply H7; [exact Ha1|exact Ha2|exact HRA|exact HP|exact HC|exact HY|exact HM|exact HH
        |assumption|assumption|assumption|assumption|assumption|assumption|assumption|assumption
        |apply closed_app; assumption|apply closed_app; assumption|apply Hxs; assumption].
    + apply cv_sym; eapply hyps_root; [exact H|reflexivity].
    + apply cv_sym; eapply hyps_root; [exact H0|reflexivity].
    + apply cv_sym; eapply iall_root; [exact H|reflexivity].
    + apply cv_sym; eapply iall_root; [exact H0|reflexivity].
  - destruct Hxs as [a1 [b1 [a2 [b2 [Ha1 [Hb1 [Ha2 [Hb2 [Hp1 [Hp2 [HA HB]]]]]]]]]]].
    eapply rel_at_conv; [exact (H7 a1 a2 Ha1 Ha2 HA HP HC IT1 IT2 X1 X2 P1 P2 h1 h2 Y HY HM HH
      HcI1 HcI2 HcX1 HcX2 HcP1 HcP2 Hch1 Hch2 b1 b2 Hb1 Hb2 HB)| | | |].
    + apply cv_sym; eapply hyps_root2; [exact H|exact Hp1|reflexivity].
    + apply cv_sym; eapply hyps_root2; [exact H0|exact Hp2|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H|exact Hp1|reflexivity].
    + apply cv_sym; eapply iall_root2; [exact H0|exact Hp2|reflexivity].
  - destruct Hxs as [e1 [b1 [e2 [b2 [He1 [Hb1 [He2 [Hb2 [Hp1 [Hp2 [HE [m [Hm [Hem HB]]]]]]]]]]]]]].
    destruct HE as [m' [Hm' [Hem' He'm']]].
    assert (m' = m) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hem'|exact Hem]).
    subst m'.
    eapply rel_at_conv; [exact (H6 m Hm HP HC IT1 IT2 X1 X2 P1 P2 h1 h2 Y HY HM HH
      HcI1 HcI2 HcX1 HcX2 HcP1 HcP2 Hch1 Hch2 b1 b2 Hb1 Hb2 HB)| | | |].
    + apply cv_sym; eapply cv_trans; [eapply hyps_root2; [exact H|exact Hp1|reflexivity]|].
      apply cv_compatible, cp_THyps; try apply cv_refl. apply conv_app_a, Hem.
    + apply cv_sym; eapply cv_trans; [eapply hyps_root2; [exact H0|exact Hp2|reflexivity]|].
      apply cv_compatible, cp_THyps; try apply cv_refl. apply conv_app_a, He'm'.
    + apply cv_sym; eapply cv_trans; [eapply iall_root2; [exact H|exact Hp1|reflexivity]|].
      apply cv_compatible, cp_TIAll; try apply cv_refl. apply conv_app_a, Hem.
    + apply cv_sym; eapply cv_trans; [eapply iall_root2; [exact H0|exact Hp2|reflexivity]|].
      apply cv_compatible, cp_TIAll; try apply cv_refl. apply conv_app_a, He'm'.
  - eapply IHD2; try eassumption. apply (H0 Y HY), Hxs.
Qed.

(* ------------------------------------------------------------------ *)
(* Payloads of inductive families and motives *)

Lemma mu_payload_interp : forall IT1 IT2 RI D1 D2' j1 j2, S2 IT1 IT2 RI ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (Def IT1) (Def IT2) ->
  closed j1 -> closed j2 -> RI j1 j2 ->
  interp 0 (TInterp IT1 (TApp D1 j1) (TMuI IT1 D1)) (TInterp IT2 (TApp D2' j2) (TMuI IT2 D2'))
    (mu_fun RI D1 j1 (mu_rel RI (mu_fun RI D1))).
Proof.
  intros IT1 IT2 RI D1 D2' j1 j2 HI HIT HD H1 H2 Hj.
  pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
  destruct (family_sem _ _ _ _ _ HI (sem_mui _ _ _ _ HIT HD)) as [HYr HYi].
  set (Y := live_fam RI (fam_of 0 (TMuI IT1 D1))).
  assert (HYr' : fam_resp RI Y) by (apply live_fam_resp; assumption).
  pose proof (live_fam_interp _ _ _ _ HP HYi) as HYi'.
  pose proof (def_app _ _ _ _ _ _ _ HI HD H1 H2 Hj) as HDF.
  pose proof (interp_TInterp _ _ _ _ HDF HP HC 0 IT1 IT2 (TMuI IT1 D1) (TMuI IT2 D2') Y HYr' HYi') as Hpay.
  eapply interp_equiv; [exact Hpay|].
  destruct (D2_good _ _ _ _ HDF HP HC) as [Hm _].
  apply fmono_equiv with (RI := RI); [exact Hm|exact HYr'|apply mu_resp|].
  apply mu_family_equiv with IT2 D2'; assumption.
Qed.

Lemma total_ty : forall IT1 IT2 RI X1 X2, S2 IT1 IT2 RI -> rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  rel_at X1 X2 (Family IT1) (Family IT2) -> ty_rel 0 (total IT1 X1) (total IT2 X2).
Proof.
  intros IT1 IT2 RI X1 X2 HI HIT HX; unfold total.
  replace 0 with (Nat.max 0 0) by reflexivity.
  apply sem_sigma; [apply rel_at_sort, HIT|intros a1 a2 Ha1 Ha2 Ha].
  rewrite !subst_app, !subst_var_same, !(subst_not_free X1), !(subst_not_free X2) by fresh_out.
  eapply family_app; [exact HI|exact HX|exact Ha1|exact Ha2|eapply rel_at_small; eassumption].
Qed.

Lemma motive_mot_rel : forall IT1 IT2 RI X1 X2 P1 P2 (Y : fam), S2 IT1 IT2 RI ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at X1 X2 (Family IT1) (Family IT2) ->
  (forall i1 i2 x1 x2, closed i1 -> closed i2 -> closed x1 -> closed x2 -> RI i1 i2 ->
    Y i1 x1 x2 -> rel_at x1 x2 (TApp X1 i1) (TApp X2 i2)) ->
  rel_at P1 P2 (motive IT1 X1) (motive IT2 X2) -> mot_rel RI Y P1 P2.
Proof.
  intros IT1 IT2 RI X1 X2 P1 P2 Y HI HIT HX HYx HP i1 i2 x1 x2 Hi1 Hi2 Hx1 Hx2 Hi Hx.
  unfold motive in HP.
  assert (Hpair : rel_at (TPair i1 x1) (TPair i2 x2) (total IT1 X1) (total IT2 X2)).
  { destruct (total_ty _ _ _ _ _ HI HIT HX) as [R HR]. unfold total in *.
    eapply sem_pair; [exists R; exact HR|exact Hi1|exact Hi2|exact Hx1|exact Hx2
      |eapply small_rel_at; eassumption|].
    rewrite !subst_app, !subst_var_same, !(subst_not_free X1), !(subst_not_free X2) by fresh_out.
    apply HYx; assumption. }
  apply rel_at_sort. eapply sem_arrow_app; [exact HP|exact Hpair|apply closed_pair; assumption
    |apply closed_pair; assumption].
Qed.

Lemma closed_lam_of : forall x b, (forall y, In y (free_vars b) -> y = x) -> closed (TLam x b).
Proof.
  intros x b H; unfold closed; cbn [free_vars].
  remember (free_vars b) as l eqn:El; clear El.
  induction l as [|y l IH]; [reflexivity|].
  cbn. destruct (Nat.eq_dec x y) as [->|Hne]; [apply IH; intros z Hz; apply H; right; exact Hz|].
  exfalso; apply Hne; symmetry; apply H; left; reflexivity.
Qed.

Lemma closed_mui : forall a b, closed a -> closed b -> closed (TMuI a b).
Proof. unfold closed; intros a b Ha Hb; cbn [free_vars]; rewrite Ha, Hb; reflexivity. Qed.
Lemma closed_closeterm : forall a b c, closed a -> closed b -> closed c -> closed (TClose a b c).
Proof. unfold closed; intros a b c Ha Hb Hc; cbn [free_vars]; rewrite Ha, Hb, Hc; reflexivity. Qed.

Lemma closed_ind : forall a b c d e f, closed a -> closed b -> closed c -> closed d ->
  closed e -> closed f -> closed (TInd a b c d e f).
Proof. unfold closed; intros; cbn [free_vars]; repeat match goal with H : free_vars _ = [] |- _ => rewrite H end; reflexivity. Qed.

(* The recursive-call function built by the induction step. *)
Definition ind_rec IT D P st a := TLam a (TLam (S a) (TInd IT D P st (TVar a) (TVar (S a)))).

Lemma closed_of_no_free : forall t, (forall y, ~ In y (free_vars t)) -> closed t.
Proof.
  intros t H; unfold closed; destruct (free_vars t) as [|y l] eqn:E; [reflexivity|].
  exfalso; apply (H y); try rewrite E; left; reflexivity.
Qed.

Lemma closed_ind_rec : forall IT D P st a, closed IT -> closed D -> closed P -> closed st ->
  closed (ind_rec IT D P st a).
Proof.
  intros IT D P st a H1 H2 H3 H4; apply closed_of_no_free; intros y Hy; unfold ind_rec in Hy.
  cbn [free_vars] in Hy. apply in_remove_iff in Hy as [Hy Hya]. apply in_remove_iff in Hy as [Hy HySa].
  unfold closed in *; rewrite H1, H2, H3, H4 in Hy; cbn in Hy.
  destruct Hy as [Hy|[Hy|[]]]; subst; congruence.
Qed.

Lemma ind_rec_beta : forall IT D P st a k y, closed IT -> closed D -> closed P -> closed st ->
  closed k -> closed y ->
  conv (TApp (TApp (ind_rec IT D P st a) k) y) (TInd IT D P st k y).
Proof.
  intros IT D P st a k y H1 H2 H3 H4 Hk Hy; unfold ind_rec.
  eapply cv_trans; [apply conv_app_f, beta_conv|].
  rewrite subst_lam_closed by (exact Hk || lia).
  eapply cv_trans; [apply beta_conv|].
  rewrite !subst_ind, !subst_var_same, subst_var_other by lia.
  rewrite !(subst_not_free IT), !(subst_not_free D), !(subst_not_free P), !(subst_not_free st)
    by (unfold closed in *; match goal with H : free_vars ?t = [] |- ~ In _ (free_vars ?t) => rewrite H; tauto end).
  rewrite subst_var_same, (subst_not_free k) by (rewrite Hk; tauto).
  apply cv_refl.
Qed.

Ltac fresh_out2 := first
  [ solve [apply fresh_not_free; cbn; auto 10]
  | solve [match goal with
    | |- ~ In (S (S (fresh ?ts))) _ => apply (above_fresh_not_free ts); [cbn; auto 10|lia]
    | |- ~ In (S (fresh ?ts)) _ => apply (above_fresh_not_free ts); [cbn; auto 10|lia]
    end]
  | solve [unfold closed in *; match goal with H : free_vars ?t = [] |- ~ In _ (free_vars ?t) => rewrite H; tauto end] ].

Lemma sem_mu_ind_method_app : forall IT1 IT2 D1 D2' P1 P2 st1 st2 j1 j2 xs1 xs2 hy1 hy2,
  closed j1 -> closed j2 -> closed xs1 -> closed xs2 -> closed hy1 -> closed hy2 ->
  rel_at st1 st2 (mu_ind_method IT1 D1 P1) (mu_ind_method IT2 D2' P2) ->
  rel_at j1 j2 IT1 IT2 ->
  rel_at xs1 xs2 (TInterp IT1 (TApp D1 j1) (TMuI IT1 D1)) (TInterp IT2 (TApp D2' j2) (TMuI IT2 D2')) ->
  rel_at hy1 hy2 (TIAll IT1 (TApp D1 j1) (TMuI IT1 D1) xs1 P1) (TIAll IT2 (TApp D2' j2) (TMuI IT2 D2') xs2 P2) ->
  rel_at (TApp (TApp (TApp st1 j1) xs1) hy1) (TApp (TApp (TApp st2 j2) xs2) hy2)
    (TApp P1 (TPair j1 (TIn xs1))) (TApp P2 (TPair j2 (TIn xs2))).
Proof.
  intros IT1 IT2 D1 D2' P1 P2 st1 st2 j1 j2 xs1 xs2 hy1 hy2 Hj1 Hj2 Hx1 Hx2 Hh1 Hh2 Hst Hj Hxs Hhy.
  unfold mu_ind_method in Hst.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hst Hj Hj1 Hj2) as H1.
  rewrite !subst_pi_closed in H1 by (assumption || lia).
  rewrite !subst_interp, !subst_iall, !subst_app, !subst_pair, !subst_in, !subst_mui, !subst_var_same in H1.
  rewrite !subst_var_other in H1 by lia.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free D1), !(subst_not_free D2'),
    !(subst_not_free P1), !(subst_not_free P2) in H1 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H1 Hxs Hx1 Hx2) as H2.
  rewrite !subst_pi_closed in H2 by (assumption || lia).
  rewrite !subst_iall, !subst_app, !subst_pair, !subst_in, !subst_mui, !subst_var_same in H2.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free D1), !(subst_not_free D2'),
    !(subst_not_free P1), !(subst_not_free P2), !(subst_not_free j1), !(subst_not_free j2) in H2 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H2 Hhy Hh1 Hh2) as H3.
  rewrite !subst_app, !subst_pair, !subst_in in H3.
  rewrite !(subst_not_free P1), !(subst_not_free P2), !(subst_not_free j1), !(subst_not_free j2),
    !(subst_not_free xs1), !(subst_not_free xs2) in H3 by fresh_out2.
  exact H3.
Qed.

Lemma ind_root : forall IT D P st i x xs, conv x (TIn xs) ->
  conv (TInd IT D P st i x)
    (TApp (TApp (TApp st i) xs)
      (THyps IT (TApp D i) (TMuI IT D) P (ind_rec IT D P st (fresh [IT; D; P; st; i; xs])) xs)).
Proof.
  intros IT D P st i x xs H.
  apply cv_trans with (u := TInd IT D P st i (TIn xs)).
  - apply cv_compatible, cp_TInd; try apply cv_refl; exact H.
  - apply conv_root; reflexivity.
Qed.

Theorem sem_ind : forall IT1 IT2 D1 D2' P1 P2 st1 st2 i1 i2 x1 x2,
  closed IT1 -> closed IT2 -> closed D1 -> closed D2' -> closed P1 -> closed P2 ->
  closed st1 -> closed st2 -> closed i1 -> closed i2 -> closed x1 -> closed x2 ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at D1 D2' (Def IT1) (Def IT2) ->
  rel_at P1 P2 (motive IT1 (TMuI IT1 D1)) (motive IT2 (TMuI IT2 D2')) ->
  rel_at st1 st2 (mu_ind_method IT1 D1 P1) (mu_ind_method IT2 D2' P2) ->
  rel_at i1 i2 IT1 IT2 -> rel_at x1 x2 (MuAt IT1 D1 i1) (MuAt IT2 D2' i2) ->
  rel_at (TInd IT1 D1 P1 st1 i1 x1) (TInd IT2 D2' P2 st2 i2 x2)
    (TApp P1 (TPair i1 x1)) (TApp P2 (TPair i2 x2)).
Proof.
  intros IT1 IT2 D1 D2' P1 P2 st1 st2 i1 i2 x1 x2 HcI1 HcI2 HcD1 HcD2 HcP1 HcP2 Hcs1 Hcs2
    Hci1 Hci2 Hcx1 Hcx2 HIT HD HP Hst Hi Hx.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  pose proof (S2_per _ _ _ HI) as HPI; pose proof (S2_conv_closed _ _ _ HI) as HCI.
  pose proof (mu_fun_ok _ _ _ _ _ HI HD) as Hok.
  pose proof Hok as [_ [_ [Hresp Hgood]]].
  set (F := mu_fun RI D1). set (mu := mu_rel RI F).
  pose proof (rel_at_small _ _ _ _ _ HI Hi) as Hii.
  assert (Hxmu : mu i1 x1 x2).
  { eapply rel_at_transfer; [exact Hx|apply (mu_type_interp _ _ _ _ _ _ _ HI HD Hci1 Hci2 Hii)|apply cv_refl]. }
  set (Q := fun j t u => forall j1 j2, closed j1 -> closed j2 -> RI j j1 -> RI j1 j2 ->
    rel_at (TInd IT1 D1 P1 st1 j1 t) (TInd IT2 D2' P2 st2 j2 u)
      (TApp P1 (TPair j1 t)) (TApp P2 (TPair j2 u))).
  assert (HQr : fam_resp RI Q).
  { intros j j' Hcj Hcj' Hjj t u; unfold Q; split; intros HQ j1 j2 H1 H2 Hr1 Hr2; apply HQ; try assumption.
    - destruct Hjj as [Hjj|Hjj]; [eapply (proj2 HPI); [exact Hjj|exact Hr1]|].
      eapply HCI; [exact Hr1|apply cv_sym; exact Hjj|apply cv_refl].
    - destruct Hjj as [Hjj|Hjj]; [eapply (proj2 HPI); [apply (proj1 HPI); exact Hjj|exact Hr1]|].
      eapply HCI; [exact Hr1|exact Hjj|apply cv_refl]. }
  assert (Hind : forall j t u, mu j t u -> Q j t u).
  { apply (mu_induction RI F); [intros k Hk Hkk; apply (Hgood k Hk Hkk)|exact HQr|].
    intros j t u Hcj Hjj [xs1 [xs2 [Hcxs1 [Hcxs2 [Ht [Hu HF]]]]]] j1 j2 Hcj1 Hcj2 Hr1 Hr2.
    set (Y := fun k a b => mu k a b /\ Q k a b).
    assert (HYr : fam_resp RI Y).
    { intros k k' Hk Hk' Hkk a b; unfold Y; split; intros [Hm Hq]; split;
        try (apply (mu_resp RI F k k' Hk Hk' Hkk); exact Hm); try (apply (HQr k k' Hk Hk' Hkk); exact Hq). }
    pose proof (Hgood j Hcj Hjj) as [Fm _].
    assert (HF1 : F j1 Y xs1 xs2).
    { apply (Hresp j j1 Hcj Hcj1 Hjj (or_introl Hr1) Y HYr), HF. }
    assert (HFm : F j1 mu xs1 xs2).
    { destruct (Hgood j1 Hcj1 (per_refl_left _ _ _ HPI Hr2)) as [Fm1 _].
      eapply (Fm1 Y mu HYr (mu_resp RI F)); [intros k a b [Hm _]; exact Hm|exact HF1]. }
    assert (Hxs : rel_at xs1 xs2 (TInterp IT1 (TApp D1 j1) (TMuI IT1 D1)) (TInterp IT2 (TApp D2' j2) (TMuI IT2 D2'))).
    { exists 0, (F j1 mu); split; [apply mu_payload_interp; assumption|exact HFm]. }
    set (r1 := ind_rec IT1 D1 P1 st1 (fresh [IT1; D1; P1; st1; j1; xs1])).
    set (r2 := ind_rec IT2 D2' P2 st2 (fresh [IT2; D2'; P2; st2; j2; xs2])).
    assert (Hcr1 : closed r1) by (apply closed_ind_rec; assumption).
    assert (Hcr2 : closed r2) by (apply closed_ind_rec; assumption).
    assert (HM : mot_rel RI Y P1 P2).
    { eapply motive_mot_rel; [exact HI|exact HIT|exact (sem_mui _ _ _ _ HIT HD)| |exact HP].
      intros k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk [Hm _].
      exists 0, (mu k1); split; [apply mu_type_interp; assumption|exact Hm]. }
    assert (HH : hyp_rel RI Y P1 P2 r1 r2).
    { intros k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk [_ Hq].
      eapply rel_at_conv; [apply (Hq k1 k2 Hk1 Hk2 (per_refl_left _ _ _ HPI Hk) Hk)| | |apply cv_refl|apply cv_refl].
      - apply cv_sym, ind_rec_beta; assumption.
      - apply cv_sym, ind_rec_beta; assumption. }
    pose proof (def_app _ _ _ _ _ _ _ HI HD Hcj1 Hcj2 Hr2) as HDj.
    assert (Hhy : rel_at (THyps IT1 (TApp D1 j1) (TMuI IT1 D1) P1 r1 xs1)
      (THyps IT2 (TApp D2' j2) (TMuI IT2 D2') P2 r2 xs2)
      (TIAll IT1 (TApp D1 j1) (TMuI IT1 D1) xs1 P1) (TIAll IT2 (TApp D2' j2) (TMuI IT2 D2') xs2 P2)).
    { eapply (sem_hyps_gen RI _ _ _ HDj HPI HCI); try eassumption;
        try (unfold closed in *; cbn [free_vars]; repeat match goal with H : free_vars _ = [] |- _ => rewrite H end; reflexivity). }
    pose proof (sem_mu_ind_method_app IT1 IT2 D1 D2' P1 P2 st1 st2 j1 j2 xs1 xs2 _ _
      Hcj1 Hcj2 Hcxs1 Hcxs2 (closed_hyps _ _ _ _ _ _ HcI1 (closed_app _ _ HcD1 Hcj1)
        (closed_mui _ _ HcI1 HcD1) HcP1 Hcr1 Hcxs1)
      (closed_hyps _ _ _ _ _ _ HcI2 (closed_app _ _ HcD2 Hcj2)
        (closed_mui _ _ HcI2 HcD2) HcP2 Hcr2 Hcxs2)
      Hst (small_rel_at _ _ _ _ _ HI Hr2) Hxs Hhy) as Happ.
    eapply rel_at_conv; [exact Happ| | | |].
    - apply cv_sym, ind_root, Ht.
    - apply cv_sym, ind_root, Hu.
    - apply conv_app_a, conv_pair; [apply cv_refl|apply cv_sym, Ht].
    - apply conv_app_a, conv_pair; [apply cv_refl|apply cv_sym, Hu]. }
  apply (Hind i1 x1 x2 Hxmu i1 i2 Hci1 Hci2 (per_refl_left _ _ _ HPI Hii) Hii).
Qed.

(* ------------------------------------------------------------------ *)
(* Close induction *)

Lemma closed_diag : forall G P, closed G -> closed P -> closed (diagonal_motive G P).
Proof.
  intros G P HG HP; apply closed_of_no_free; intros y Hy; unfold diagonal_motive in Hy.
  cbn [free_vars] in Hy. apply in_remove_iff in Hy as [Hy Hne].
  unfold closed in *; rewrite HG, HP in Hy; cbn in Hy.
  destruct Hy as [Hy|[Hy|[]]]; subst; congruence.
Qed.

Lemma closed_rewrite_tac_dummy : True.
Proof. exact I. Qed.

Ltac closed_free := unfold closed in *;
  match goal with H : free_vars ?t = [] |- ~ In _ (free_vars ?t) => rewrite H; tauto end.

Lemma diag_app_conv : forall G P k y, closed G -> closed P -> closed k -> closed y ->
  conv (TApp (diagonal_motive G P) (TPair k y)) (TApp (TApp (TApp P G) k) y).
Proof.
  intros G P k y HG HP Hk Hy; unfold diagonal_motive.
  eapply cv_trans; [apply beta_conv|].
  rewrite !subst_app, !subst_fst, !subst_snd, !subst_var_same.
  rewrite (subst_not_free P), (subst_not_free G) by closed_free.
  apply conv_app; [apply conv_app_a|]; apply conv_root; reflexivity.
Qed.

Definition close_rec IT G P st a := TLam a (TLam (S a) (TCloseInd IT G P st G (TVar a) (TVar (S a)))).

Lemma closed_close_rec : forall IT G P st a, closed IT -> closed G -> closed P -> closed st ->
  closed (close_rec IT G P st a).
Proof.
  intros IT G P st a H1 H2 H3 H4; apply closed_of_no_free; intros y Hy; unfold close_rec in Hy.
  cbn [free_vars] in Hy. apply in_remove_iff in Hy as [Hy Hya]. apply in_remove_iff in Hy as [Hy HySa].
  unfold closed in *; rewrite H1, H2, H3, H4 in Hy; cbn in Hy.
  destruct Hy as [Hy|[Hy|[]]]; subst; congruence.
Qed.

Lemma close_rec_beta : forall IT G P st a k y, closed IT -> closed G -> closed P -> closed st ->
  closed k -> closed y ->
  conv (TApp (TApp (close_rec IT G P st a) k) y) (TCloseInd IT G P st G k y).
Proof.
  intros IT G P st a k y H1 H2 H3 H4 Hk Hy; unfold close_rec.
  eapply cv_trans; [apply conv_app_f, beta_conv|].
  rewrite subst_lam_closed by (exact Hk || lia).
  eapply cv_trans; [apply beta_conv|].
  rewrite !subst_closeind, !subst_var_same, subst_var_other by lia.
  rewrite !(subst_not_free IT), !(subst_not_free G), !(subst_not_free P), !(subst_not_free st)
    by closed_free.
  rewrite subst_var_same, (subst_not_free k) by (rewrite Hk; tauto).
  apply cv_refl.
Qed.

Lemma closeind_root : forall IT G P st F i x xs, conv x (TIn xs) ->
  conv (TCloseInd IT G P st F i x)
    (TApp (TApp (TApp (TApp st F) i) xs)
      (THyps IT (TApp F i) (carrier IT G) (diagonal_motive G P)
        (close_rec IT G P st (fresh [IT; G; P; st; F; i; xs])) xs)).
Proof.
  intros IT G P st F i x xs H.
  apply cv_trans with (u := TCloseInd IT G P st F i (TIn xs)).
  - apply cv_compatible, cp_TCloseInd; try apply cv_refl; exact H.
  - apply conv_root; reflexivity.
Qed.

Lemma closed_payload_parts : forall IT G, closed IT -> closed G -> closed (carrier IT G).
Proof. intros; unfold carrier; apply closed_closeterm; assumption. Qed.

(* Applying a close motive to a description, an index and close data. *)
Lemma sem_close_motive_app : forall IT1 IT2 G1 G2 P1 P2 Fx1 Fx2 k1 k2 y1 y2,
  closed Fx1 -> closed Fx2 -> closed k1 -> closed k2 -> closed y1 -> closed y2 ->
  closed IT1 -> closed IT2 -> closed G1 -> closed G2 ->
  rel_at P1 P2 (close_motive IT1 G1) (close_motive IT2 G2) ->
  rel_at Fx1 Fx2 (Def IT1) (Def IT2) -> rel_at k1 k2 IT1 IT2 ->
  rel_at y1 y2 (CloseAt IT1 Fx1 G1 k1) (CloseAt IT2 Fx2 G2 k2) ->
  ty_rel 0 (TApp (TApp (TApp P1 Fx1) k1) y1) (TApp (TApp (TApp P2 Fx2) k2) y2).
Proof.
  intros IT1 IT2 G1 G2 P1 P2 Fx1 Fx2 k1 k2 y1 y2 Hf1 Hf2 Hk1 Hk2 Hy1 Hy2 HI1 HI2 HG1 HG2 HP HF Hk Hy.
  unfold close_motive in HP.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ HP HF Hf1 Hf2) as H1.
  rewrite !subst_pi_closed in H1 by (assumption || lia).
  unfold CloseAt in H1.
  rewrite !subst_app, !subst_closeterm, !subst_var_same in H1.
  rewrite !subst_var_other in H1 by lia.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free G1), !(subst_not_free G2)
    in H1 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H1 Hk Hk1 Hk2) as H2.
  rewrite !subst_pi_closed in H2 by (assumption || lia).
  rewrite !subst_app, !subst_closeterm, !subst_var_same in H2.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free G1), !(subst_not_free G2),
    !(subst_not_free Fx1), !(subst_not_free Fx2) in H2 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H2 Hy Hy1 Hy2) as H3.
  rewrite !subst_sort in H3. apply rel_at_sort, H3.
Qed.

Lemma sem_close_ind_method_app : forall IT1 IT2 G1 G2 P1 P2 st1 st2 Fx1 Fx2 j1 j2 xs1 xs2 hy1 hy2,
  closed IT1 -> closed IT2 -> closed G1 -> closed G2 -> closed P1 -> closed P2 ->
  closed Fx1 -> closed Fx2 -> closed j1 -> closed j2 -> closed xs1 -> closed xs2 ->
  closed hy1 -> closed hy2 ->
  rel_at st1 st2 (close_ind_method IT1 G1 P1) (close_ind_method IT2 G2 P2) ->
  rel_at Fx1 Fx2 (Def IT1) (Def IT2) -> rel_at j1 j2 IT1 IT2 ->
  rel_at xs1 xs2 (payload IT1 Fx1 G1 j1) (payload IT2 Fx2 G2 j2) ->
  rel_at hy1 hy2 (TIAll IT1 (TApp Fx1 j1) (carrier IT1 G1) xs1 (diagonal_motive G1 P1))
    (TIAll IT2 (TApp Fx2 j2) (carrier IT2 G2) xs2 (diagonal_motive G2 P2)) ->
  rel_at (TApp (TApp (TApp (TApp st1 Fx1) j1) xs1) hy1) (TApp (TApp (TApp (TApp st2 Fx2) j2) xs2) hy2)
    (TApp (TApp (TApp P1 Fx1) j1) (TIn xs1)) (TApp (TApp (TApp P2 Fx2) j2) (TIn xs2)).
Proof.
  intros IT1 IT2 G1 G2 P1 P2 st1 st2 Fx1 Fx2 j1 j2 xs1 xs2 hy1 hy2 HI1 HI2 HG1 HG2 HP1 HP2
    Hf1 Hf2 Hj1 Hj2 Hx1 Hx2 Hh1 Hh2 Hst HF Hj Hxs Hhy.
  assert (Hc1 : closed (carrier IT1 G1)) by (apply closed_payload_parts; assumption).
  assert (Hc2 : closed (carrier IT2 G2)) by (apply closed_payload_parts; assumption).
  assert (Hd1 : closed (diagonal_motive G1 P1)) by (apply closed_diag; assumption).
  assert (Hd2 : closed (diagonal_motive G2 P2)) by (apply closed_diag; assumption).
  unfold close_ind_method, payload in Hst; unfold payload in Hxs.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hst HF Hf1 Hf2) as H1.
  rewrite !subst_pi_closed in H1 by (assumption || lia).
  rewrite !subst_interp, !subst_iall, !subst_app, !subst_in, !subst_var_same in H1.
  rewrite !subst_var_other in H1 by lia.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free P1), !(subst_not_free P2),
    !(subst_not_free (carrier IT1 G1)), !(subst_not_free (carrier IT2 G2)),
    !(subst_not_free (diagonal_motive G1 P1)), !(subst_not_free (diagonal_motive G2 P2)) in H1 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H1 Hj Hj1 Hj2) as H2.
  rewrite !subst_pi_closed in H2 by (assumption || lia).
  rewrite !subst_interp, !subst_iall, !subst_app, !subst_in, !subst_var_same in H2.
  rewrite !subst_var_other in H2 by lia.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free P1), !(subst_not_free P2),
    !(subst_not_free Fx1), !(subst_not_free Fx2),
    !(subst_not_free (carrier IT1 G1)), !(subst_not_free (carrier IT2 G2)),
    !(subst_not_free (diagonal_motive G1 P1)), !(subst_not_free (diagonal_motive G2 P2)) in H2 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H2 Hxs Hx1 Hx2) as H3.
  rewrite !subst_pi_closed in H3 by (assumption || lia).
  rewrite !subst_iall, !subst_app, !subst_in, !subst_var_same in H3.
  rewrite !(subst_not_free IT1), !(subst_not_free IT2), !(subst_not_free P1), !(subst_not_free P2),
    !(subst_not_free Fx1), !(subst_not_free Fx2), !(subst_not_free j1), !(subst_not_free j2),
    !(subst_not_free (carrier IT1 G1)), !(subst_not_free (carrier IT2 G2)),
    !(subst_not_free (diagonal_motive G1 P1)), !(subst_not_free (diagonal_motive G2 P2)) in H3 by fresh_out2.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ H3 Hhy Hh1 Hh2) as H4.
  rewrite !subst_app, !subst_in in H4.
  rewrite !(subst_not_free P1), !(subst_not_free P2), !(subst_not_free Fx1), !(subst_not_free Fx2),
    !(subst_not_free j1), !(subst_not_free j2), !(subst_not_free xs1), !(subst_not_free xs2) in H4 by fresh_out2.
  exact H4.
Qed.

Section CloseInduction.
Variables IT1 IT2 G1 G2 P1 P2 st1 st2 : term.
Variable RI : rel.
Hypothesis HcI1 : closed IT1. Hypothesis HcI2 : closed IT2.
Hypothesis HcG1 : closed G1. Hypothesis HcG2 : closed G2.
Hypothesis HcP1 : closed P1. Hypothesis HcP2 : closed P2.
Hypothesis Hcs1 : closed st1. Hypothesis Hcs2 : closed st2.
Hypothesis HI : S2 IT1 IT2 RI.
Hypothesis HIT : rel_at IT1 IT2 (TSort 0) (TSort 0).
Hypothesis HG : rel_at G1 G2 (Def IT1) (Def IT2).
Hypothesis HP : rel_at P1 P2 (close_motive IT1 G1) (close_motive IT2 G2).
Hypothesis Hst : rel_at st1 st2 (close_ind_method IT1 G1 P1) (close_ind_method IT2 G2 P2).

Let mu := mu_rel RI (mu_fun RI G1).

Definition diag_prop : fam := fun j t u => forall j1 j2, closed j1 -> closed j2 -> RI j j1 -> RI j1 j2 ->
  rel_at (TCloseInd IT1 G1 P1 st1 G1 j1 t) (TCloseInd IT2 G2 P2 st2 G2 j2 u)
    (TApp (TApp (TApp P1 G1) j1) t) (TApp (TApp (TApp P2 G2) j2) u).

Lemma diag_prop_resp : fam_resp RI diag_prop.
Proof.
  pose proof (S2_per _ _ _ HI) as HPI; pose proof (S2_conv_closed _ _ _ HI) as HCI.
  intros j j' Hcj Hcj' Hjj t u; unfold diag_prop; split; intros HQ j1 j2 H1 H2 Hr1 Hr2; apply HQ; try assumption.
  - destruct Hjj as [Hjj|Hjj]; [eapply (proj2 HPI); [exact Hjj|exact Hr1]|].
    eapply HCI; [exact Hr1|apply cv_sym; exact Hjj|apply cv_refl].
  - destruct Hjj as [Hjj|Hjj]; [eapply (proj2 HPI); [apply (proj1 HPI); exact Hjj|exact Hr1]|].
    eapply HCI; [exact Hr1|exact Hjj|apply cv_refl].
Qed.

Lemma close_ind_step : forall Fx1 Fx2 j1 j2 xs1 xs2,
  closed Fx1 -> closed Fx2 -> closed j1 -> closed j2 -> closed xs1 -> closed xs2 ->
  rel_at Fx1 Fx2 (Def IT1) (Def IT2) -> RI j1 j2 ->
  canonL RI (TApp Fx1 j1) (fun k a b => mu k a b /\ diag_prop k a b) xs1 xs2 ->
  rel_at (TApp (TApp (TApp (TApp st1 Fx1) j1) xs1)
      (THyps IT1 (TApp Fx1 j1) (carrier IT1 G1) (diagonal_motive G1 P1)
        (close_rec IT1 G1 P1 st1 (fresh [IT1; G1; P1; st1; Fx1; j1; xs1])) xs1))
    (TApp (TApp (TApp (TApp st2 Fx2) j2) xs2)
      (THyps IT2 (TApp Fx2 j2) (carrier IT2 G2) (diagonal_motive G2 P2)
        (close_rec IT2 G2 P2 st2 (fresh [IT2; G2; P2; st2; Fx2; j2; xs2])) xs2))
    (TApp (TApp (TApp P1 Fx1) j1) (TIn xs1)) (TApp (TApp (TApp P2 Fx2) j2) (TIn xs2)).
Proof.
  intros Fx1 Fx2 j1 j2 xs1 xs2 Hf1 Hf2 Hj1 Hj2 Hx1 Hx2 HF Hj HY.
  pose proof (S2_per _ _ _ HI) as HPI; pose proof (S2_conv_closed _ _ _ HI) as HCI.
  pose proof (mu_fun_ok _ _ _ _ _ HI HG) as Hok.
  set (Y := fun k a b => mu k a b /\ diag_prop k a b).
  assert (HYr : fam_resp RI Y).
  { intros k k' Hk Hk' Hkk a b; unfold Y; split; intros [Hm Hq]; split;
      try (apply (mu_resp RI _ k k' Hk Hk' Hkk); exact Hm);
      try (apply (diag_prop_resp k k' Hk Hk' Hkk); exact Hq). }
  pose proof (def_app _ _ _ _ _ _ _ HI HF Hj1 Hj2 Hj) as HDF.
  destruct (D2_good _ _ _ _ HDF HPI HCI) as [Fm _].
  assert (Hpay : rel_at xs1 xs2 (payload IT1 Fx1 G1 j1) (payload IT2 Fx2 G2 j2)).
  { exists 0, (canonL RI (TApp Fx1 j1) mu); split; [apply payload_interp; assumption|].
    eapply (Fm Y mu HYr (mu_resp RI _)); [intros k a b [Hm _]; exact Hm|exact HY]. }
  set (r1 := close_rec IT1 G1 P1 st1 (fresh [IT1; G1; P1; st1; Fx1; j1; xs1])).
  set (r2 := close_rec IT2 G2 P2 st2 (fresh [IT2; G2; P2; st2; Fx2; j2; xs2])).
  assert (Hcr1 : closed r1) by (apply closed_close_rec; assumption).
  assert (Hcr2 : closed r2) by (apply closed_close_rec; assumption).
  assert (Hcd1 : closed (diagonal_motive G1 P1)) by (apply closed_diag; assumption).
  assert (Hcd2 : closed (diagonal_motive G2 P2)) by (apply closed_diag; assumption).
  assert (Hcc1 : closed (carrier IT1 G1)) by (apply closed_payload_parts; assumption).
  assert (Hcc2 : closed (carrier IT2 G2)) by (apply closed_payload_parts; assumption).
  assert (Hymu : forall k1 k2 y1 y2, closed k1 -> closed k2 -> closed y1 -> closed y2 -> RI k1 k2 ->
    mu k1 y1 y2 -> rel_at y1 y2 (CloseAt IT1 G1 G1 k1) (CloseAt IT2 G2 G2 k2)).
  { intros k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk Hm.
    exists 0, (roll (canonL RI (TApp G1 k1) mu)); split; [apply close_type_interp; assumption|].
    exact (proj1 (mu_ok_unfold _ _ Hok k1 y1 y2 Hk1 (per_refl_left _ _ _ HPI Hk)) Hm). }
  assert (HM : mot_rel RI Y (diagonal_motive G1 P1) (diagonal_motive G2 P2)).
  { intros k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk [Hm _].
    eapply ty_rel_conv; [exact (sem_close_motive_app IT1 IT2 G1 G2 P1 P2 G1 G2 k1 k2 y1 y2
      HcG1 HcG2 Hk1 Hk2 Hy1 Hy2 HcI1 HcI2 HcG1 HcG2 HP HG (small_rel_at _ _ _ _ _ HI Hk)
      (Hymu k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk Hm))| |]; apply cv_sym, diag_app_conv; assumption. }
  assert (HH : hyp_rel RI Y (diagonal_motive G1 P1) (diagonal_motive G2 P2) r1 r2).
  { intros k1 k2 y1 y2 Hk1 Hk2 Hy1 Hy2 Hk [_ Hq].
    eapply rel_at_conv; [apply (Hq k1 k2 Hk1 Hk2 (per_refl_left _ _ _ HPI Hk) Hk)| | | |].
    - apply cv_sym, close_rec_beta; assumption.
    - apply cv_sym, close_rec_beta; assumption.
    - apply cv_sym, diag_app_conv; assumption.
    - apply cv_sym, diag_app_conv; assumption. }
  assert (Hhy : rel_at (THyps IT1 (TApp Fx1 j1) (carrier IT1 G1) (diagonal_motive G1 P1) r1 xs1)
      (THyps IT2 (TApp Fx2 j2) (carrier IT2 G2) (diagonal_motive G2 P2) r2 xs2)
      (TIAll IT1 (TApp Fx1 j1) (carrier IT1 G1) xs1 (diagonal_motive G1 P1))
      (TIAll IT2 (TApp Fx2 j2) (carrier IT2 G2) xs2 (diagonal_motive G2 P2))).
  { eapply (sem_hyps_gen RI _ _ _ HDF HPI HCI); eassumption. }
  apply (sem_close_ind_method_app IT1 IT2 G1 G2 P1 P2 st1 st2 Fx1 Fx2 j1 j2 xs1 xs2 _ _
    HcI1 HcI2 HcG1 HcG2 HcP1 HcP2 Hf1 Hf2 Hj1 Hj2 Hx1 Hx2
    (closed_hyps _ _ _ _ _ _ HcI1 (closed_app _ _ Hf1 Hj1) Hcc1 Hcd1 Hcr1 Hx1)
    (closed_hyps _ _ _ _ _ _ HcI2 (closed_app _ _ Hf2 Hj2) Hcc2 Hcd2 Hcr2 Hx2)
    Hst HF (small_rel_at _ _ _ _ _ HI Hj) Hpay Hhy).
Qed.

Lemma diag_induction : forall j t u, mu j t u -> diag_prop j t u.
Proof.
  pose proof (S2_per _ _ _ HI) as HPI; pose proof (S2_conv_closed _ _ _ HI) as HCI.
  pose proof (mu_fun_ok _ _ _ _ _ HI HG) as Hok. pose proof Hok as [_ [_ [Hresp Hgood]]].
  apply (mu_induction RI (mu_fun RI G1)); [intros k Hk Hkk; apply (Hgood k Hk Hkk)|exact diag_prop_resp|].
  intros j t u Hcj Hjj [xs1 [xs2 [Hcx1 [Hcx2 [Ht [Hu HF]]]]]] j1 j2 Hcj1 Hcj2 Hr1 Hr2.
  set (Y := fun k a b => mu k a b /\ diag_prop k a b).
  assert (HYr : fam_resp RI Y).
  { intros k k' Hk Hk' Hkk a b; unfold Y; split; intros [Hm Hq]; split;
      try (apply (mu_resp RI _ k k' Hk Hk' Hkk); exact Hm);
      try (apply (diag_prop_resp k k' Hk Hk' Hkk); exact Hq). }
  assert (HF1 : canonL RI (TApp G1 j1) Y xs1 xs2).
  { apply (Hresp j j1 Hcj Hcj1 Hjj (or_introl Hr1) Y HYr), HF. }
  eapply rel_at_conv; [apply (close_ind_step G1 G2 j1 j2 xs1 xs2); try assumption| | | |].
  - apply cv_sym, closeind_root, Ht.
  - apply cv_sym, closeind_root, Hu.
  - apply conv_app_a, cv_sym, Ht.
  - apply conv_app_a, cv_sym, Hu.
Qed.

End CloseInduction.

Theorem sem_close_ind : forall IT1 IT2 G1 G2 P1 P2 st1 st2 F1 F2 i1 i2 x1 x2,
  closed IT1 -> closed IT2 -> closed G1 -> closed G2 -> closed P1 -> closed P2 ->
  closed st1 -> closed st2 -> closed F1 -> closed F2 -> closed i1 -> closed i2 ->
  closed x1 -> closed x2 ->
  rel_at IT1 IT2 (TSort 0) (TSort 0) -> rel_at G1 G2 (Def IT1) (Def IT2) ->
  rel_at P1 P2 (close_motive IT1 G1) (close_motive IT2 G2) ->
  rel_at st1 st2 (close_ind_method IT1 G1 P1) (close_ind_method IT2 G2 P2) ->
  rel_at F1 F2 (Def IT1) (Def IT2) -> rel_at i1 i2 IT1 IT2 ->
  rel_at x1 x2 (CloseAt IT1 F1 G1 i1) (CloseAt IT2 F2 G2 i2) ->
  rel_at (TCloseInd IT1 G1 P1 st1 F1 i1 x1) (TCloseInd IT2 G2 P2 st2 F2 i2 x2)
    (TApp (TApp (TApp P1 F1) i1) x1) (TApp (TApp (TApp P2 F2) i2) x2).
Proof.
  intros IT1 IT2 G1 G2 P1 P2 st1 st2 F1 F2 i1 i2 x1 x2 HcI1 HcI2 HcG1 HcG2 HcP1 HcP2 Hcs1 Hcs2
    Hcf1 Hcf2 Hci1 Hci2 Hcx1 Hcx2 HIT HG HP Hst HF Hi Hx.
  destruct (small_of_rel _ _ HIT) as [RI HI].
  pose proof (S2_per _ _ _ HI) as HPI; pose proof (S2_conv_closed _ _ _ HI) as HCI.
  pose proof (rel_at_small _ _ _ _ _ HI Hi) as Hii.
  pose proof (rel_at_transfer _ _ _ _ _ _ _ _ Hx (close_type_interp _ _ _ _ _ _ _ _ _ HI HF HG Hci1 Hci2 Hii) (cv_refl _))
    as [xs1 [xs2 [Hx1 [Hx2 [Ht [Hu Hr]]]]]].
  pose proof (def_app _ _ _ _ _ _ _ HI HF Hci1 Hci2 Hii) as HDF.
  destruct (D2_good _ _ _ _ HDF HPI HCI) as [Fm _].
  pose proof (mu_fun_ok _ _ _ _ _ HI HG) as Hok.
  set (Y := fun k a b => mu_rel RI (mu_fun RI G1) k a b /\
    diag_prop IT1 IT2 G1 G2 P1 P2 st1 st2 RI k a b).
  assert (HYr : fam_resp RI Y).
  { intros k k' Hk Hk' Hkk a b; unfold Y; split; intros [Hm Hq]; split;
      try (apply (mu_resp RI _ k k' Hk Hk' Hkk); exact Hm);
      try (apply (diag_prop_resp IT1 IT2 G1 G2 P1 P2 st1 st2 RI HI k k' Hk Hk' Hkk); exact Hq). }
  assert (HY : canonL RI (TApp F1 i1) Y xs1 xs2).
  { eapply (Fm (mu_rel RI (mu_fun RI G1)) Y (mu_resp RI _) HYr); [|exact Hr].
    intros k a b Hm; split; [exact Hm|].
    exact (diag_induction IT1 IT2 G1 G2 P1 P2 st1 st2 RI HcI1 HcI2 HcG1 HcG2 HcP1 HcP2 Hcs1 Hcs2
      HI HIT HG HP Hst k a b Hm). }
  eapply rel_at_conv; [exact (close_ind_step IT1 IT2 G1 G2 P1 P2 st1 st2 RI HcI1 HcI2 HcG1 HcG2
    HcP1 HcP2 Hcs1 Hcs2 HI HIT HG HP Hst F1 F2 i1 i2 xs1 xs2 Hcf1 Hcf2 Hci1 Hci2 Hx1 Hx2 HF Hii HY)| | | |].
  - apply cv_sym, closeind_root, Ht.
  - apply cv_sym, closeind_root, Hu.
  - apply conv_app_a, cv_sym, Ht.
  - apply conv_app_a, cv_sym, Hu.
Qed.
