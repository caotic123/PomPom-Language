Require Import Progress _tmp_estep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ---------------------------------------------------------------------- *)
(*  Small algebra helpers                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma lift_zero_id : forall t k, lift 0 k t = t.
Proof.
  assert (Hmap : forall bs k,
      (forall c b, In (c,b) bs ->
        lift 0 k c = c /\ lift 0 (S k) b = b) ->
      map (fun '(c,b) => (lift 0 k c, lift 0 (S k) b)) bs = bs).
  {
    intros bs k H. induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    rewrite (proj1 (H c b (or_introl eq_refl))).
    rewrite (proj2 (H c b (or_introl eq_refl))).
    rewrite (IH ltac:(intros c' b' Hin; apply H; right; exact Hin)).
    reflexivity.
  }
  apply (tsize_strong_ind (fun t => forall k, lift 0 k t = t)).
  intros t IH k. destruct t; cbn [lift].
  all: try solve [destruct (Nat.ltb n k); reflexivity].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  rewrite (Hmap bs k ltac:(intros c b Hin; split;
    [apply IH; eapply tsize_case_bs; exact Hin |
     apply IH; eapply tsize_case_bs_body; exact Hin])).
  reflexivity.
Qed.

Lemma subst_eta_app : forall f a,
    subst a 0 (TApp (lift 1 0 f) (TVar 0)) = TApp f a.
Proof.
  intros f a. cbn [subst].
  rewrite subst_lift_zero, lift_zero_id. reflexivity.
Qed.

Lemma subst_var_shift : forall n j,
    subst (TVar 0) j (lift 1 (S j) (TVar n)) = TVar n.
Proof.
  intros n j. cbn [lift].
  destruct (Nat.ltb n (S j)) eqn:H2.
  - apply Nat.ltb_lt in H2. cbn [subst]. destruct (Nat.ltb n j) eqn:H1.
    + reflexivity.
    + apply Nat.ltb_ge in H1. assert (Hnj : n = j) by lia. subst n.
      rewrite Nat.eqb_refl. cbn. rewrite Nat.add_0_r. reflexivity.
  - apply Nat.ltb_ge in H2. cbn [subst]. destruct (Nat.ltb n j) eqn:H1.
    + apply Nat.ltb_lt in H1. exfalso; lia.
    + reflexivity.
Qed.


Lemma subst_lift_shift : forall t j, subst (TVar 0) j (lift 1 (S j) t) = t.
Proof.
  intros t. induction t; intros j.
  - apply subst_var_shift.
  - reflexivity.
  - f_equal. apply IHt1.
  - f_equal. apply IHt.
  - f_equal. apply IHt1.
  - reflexivity.
  - f_equal. apply IHt1.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2.
  - reflexivity.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2.
  - f_equal. apply IHt1. f_equal. apply IHt2.
  - reflexivity.
  - f_equal. apply IHt1.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2. f_equal. apply IHt3.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2.
  - f_equal. apply IHt1. f_equal. apply IHt2.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2. f_equal. apply IHt3.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt1. f_equal. apply IHt2. f_equal. apply IHt3.
  - f_equal. apply IHt1. f_equal. apply IHt2. f_equal. apply IHt3.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt1. f_equal. apply IHt2. f_equal. apply IHt3.
  - induction bs as [|[c b] bs IHbs].
    + reflexivity.
    + cbn. f_equal; [| f_equal; [apply IHt2 | apply IHt3]].
      apply IHt1. eapply tsize_case_bs. left. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  estep vs epstep                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma epbranches_snoc_replace : forall bs1 c c' b bs2,
    estep c c' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b) :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c c' b bs2 Hcc; cbn.
  - econstructor; [exact Hcc | apply epstep_refl | apply epbranches_refl].
  - econstructor; [apply epstep_refl | apply epstep_refl |
      apply IH; exact Hcc].
Qed.

Lemma estep_epstep : forall t u, estep t u -> epstep t u.
Proof.
  intros t u H; induction H.
  - apply eps_eta, epstep_refl.
  - apply epbranches_snoc_replace; assumption.
  - apply epbranches_snoc_replace; assumption.
  - all: try (econstructor; solve
      [ assumption | apply IHestep
      | apply epstep_refl | apply epbranches_refl ]).
Qed.

(* ---------------------------------------------------------------------- *)
(*  rtc closure machinery                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma rtc_estep_congr : forall (F : term -> term),
    (forall x y, estep x y -> estep (F x) (F y)) ->
    forall x y, rtc estep x y -> rtc estep (F x) (F y).
Proof.
  intros F HF x y H; induction H;
    [apply rtc_refl | eapply rtc_step; eauto].
Qed.

Lemma rtc_estep_congr2 : forall (F : term -> term -> term),
    (forall x y z, estep x y -> estep (F x z) (F y z)) ->
    (forall z x y, estep x y -> estep (F z x) (F z y)) ->
    forall x x' y y', rtc estep x x' -> rtc estep y y' ->
      rtc estep (F x y) (F x' y').
Proof.
  intros F H1 H2 x x' y y' Hx Hy. eapply rtc_trans.
  - eapply rtc_estep_congr; [apply H1 | exact Hx].
  - eapply rtc_estep_congr; [apply H2 | exact Hy].
Qed.

Lemma rtc_estep_congr3 : forall (F : term -> term -> term -> term),
    (forall x y a b, estep x y -> estep (F x a b) (F y a b)) ->
    (forall a x y b, estep x y -> estep (F a x b) (F a y b)) ->
    (forall a b x y, estep x y -> estep (F a b x) (F a b y)) ->
    forall a a' b b' c c', rtc estep a a' -> rtc estep b b' ->
      rtc estep c c' -> rtc estep (F a b c) (F a' b' c').
Proof.
  intros F H1 H2 H3 a a' b b' c c' Ha Hb Hc. eapply rtc_trans.
  - eapply rtc_estep_congr; [apply H1 | exact Ha].
  - eapply rtc_trans.
    + eapply rtc_estep_congr; [apply H2 | exact Hb].
    + eapply rtc_estep_congr; [apply H3 | exact Hc].
Qed.

Lemma rtc_estep_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall x y a b c, estep x y -> estep (F x a b c) (F y a b c)) ->
    (forall a x y b c, estep x y -> estep (F a x b c) (F a y b c)) ->
    (forall a b x y c, estep x y -> estep (F a b x c) (F a b y c)) ->
    (forall a b c x y, estep x y -> estep (F a b c x) (F a b c y)) ->
    forall a a' b b' c c' d d',
      rtc estep a a' -> rtc estep b b' -> rtc estep c c' ->
      rtc estep d d' -> rtc estep (F a b c d) (F a' b' c' d').
Proof.
  intros F H1 H2 H3 H4 a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_trans.
  - eapply rtc_estep_congr; [apply H1 | exact Ha].
  - eapply rtc_trans.
    + eapply rtc_estep_congr; [apply H2 | exact Hb].
    + eapply rtc_trans.
      * eapply rtc_estep_congr; [apply H3 | exact Hc].
      * eapply rtc_estep_congr; [apply H4 | exact Hd].
Qed.

Lemma rtc_estep_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall x y a b c d, estep x y -> estep (F x a b c d) (F y a b c d)) ->
    (forall a x y b c d, estep x y -> estep (F a x b c d) (F a y b c d)) ->
    (forall a b x y c d, estep x y -> estep (F a b x c d) (F a b y c d)) ->
    (forall a b c x y d, estep x y -> estep (F a b c x d) (F a b c y d)) ->
    (forall a b c d x y, estep x y -> estep (F a b c d x) (F a b c d y)) ->
    forall a a' b b' c c' d d' e e',
      rtc estep a a' -> rtc estep b b' -> rtc estep c c' ->
      rtc estep d d' -> rtc estep e e' ->
      rtc estep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F H1 H2 H3 H4 H5 a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_trans.
  - eapply rtc_estep_congr; [apply H1 | exact Ha].
  - eapply rtc_trans.
    + eapply rtc_estep_congr; [apply H2 | exact Hb].
    + eapply rtc_trans.
      * eapply rtc_estep_congr; [apply H3 | exact Hc].
      * eapply rtc_trans.
        -- eapply rtc_estep_congr; [apply H4 | exact Hd].
        -- eapply rtc_estep_congr; [apply H5 | exact He].
Qed.

Lemma epbranches_rtc_estep : forall bs bs',
    epbranches bs bs' -> forall pre M Q,
    rtc estep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs')).
Proof.
  intros bs bs' Hbs. induction Hbs as [|[c b] bs0 [Hc Hb] Hbs0 IH];
    intros pre M Q.
  - apply rtc_refl.
  - rewrite <- app_assoc in *.
    eapply rtc_trans.
    + eapply rtc_estep_congr
        (F := fun z => TCase M Q (pre ++ (z,b) :: bs0));
      [intros x y Hxy; apply es_case_br1; exact Hxy | exact Hc].
    + eapply rtc_trans.
      * eapply rtc_estep_congr
          (F := fun z => TCase M Q (pre ++ (c',z) :: bs0));
        [intros x y Hxy; apply es_case_br2; exact Hxy | exact Hb].
      * apply (IH ((pre ++ [(c',b')])) M Q). reflexivity.
Qed.

Lemma epstep_rtc_estep :
  (forall t u, epstep t u -> rtc estep t u) /\
  (forall bs bs', epbranches bs bs' -> True).
Proof.
  split.
  2: intros; exact I.
  intros t u H. induction H using epstep_epbranches_ind.
  - apply es_eta. assumption.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - apply rtc_refl.
  - (* eps_pi *) eapply rtc_estep_congr2 (F := fun x y => TPi x y);
      [intros x y z Hxy; apply es_pi1; exact Hxy
      |intros z x y Hxy; apply es_pi2; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TLam z);
      [intros x y Hxy; apply es_lam; exact Hxy | assumption].
  - eapply rtc_estep_congr2 (F := fun x y => TApp x y);
      [intros x y z Hxy; apply es_app1; exact Hxy
      |intros z x y Hxy; apply es_app2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TSigma x y);
      [intros x y z Hxy; apply es_sigma1; exact Hxy
      |intros z x y Hxy; apply es_sigma2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TPair x y);
      [intros x y z Hxy; apply es_pair1; exact Hxy
      |intros z x y Hxy; apply es_pair2; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TFst z);
      [intros x y Hxy; apply es_fst; exact Hxy | assumption].
  - eapply rtc_estep_congr (F := fun z => TSnd z);
      [intros x y Hxy; apply es_snd; exact Hxy | assumption].
  - eapply rtc_estep_congr2 (F := fun x y => TConsE x y);
      [intros x y z Hxy; apply es_conse1; exact Hxy
      |intros z x y Hxy; apply es_conse2; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TEnumT z);
      [intros x y Hxy; apply es_enumt; exact Hxy | assumption].
  - eapply rtc_estep_congr (F := fun z => TESucc z);
      [intros x y Hxy; apply es_esucc; exact Hxy | assumption].
  - eapply rtc_estep_congr2 (F := fun x y => TEPi x y);
      [intros x y z Hxy; apply es_epi1; exact Hxy
      |intros z x y Hxy; apply es_epi2; exact Hxy]; assumption.
  - eapply rtc_estep_congr4
      (F := fun x y z w => TSwitch x y z w);
    [intros x y a b c Hxy; apply es_switch1; exact Hxy
    |intros a x y b c Hxy; apply es_switch2; exact Hxy
    |intros a b x y c Hxy; apply es_switch3; exact Hxy
    |intros a b c x y Hxy; apply es_switch4; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TIDesc z);
      [intros x y Hxy; apply es_idesc; exact Hxy | assumption].
  - eapply rtc_estep_congr (F := fun z => TIVar z);
      [intros x y Hxy; apply es_ivar; exact Hxy | assumption].
  - eapply rtc_estep_congr2 (F := fun x y => TIProd x y);
      [intros x y z Hxy; apply es_iprod1; exact Hxy
      |intros z x y Hxy; apply es_iprod2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TIPi x y);
      [intros x y z Hxy; apply es_ipi1; exact Hxy
      |intros z x y Hxy; apply es_ipi2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TISig x y);
      [intros x y z Hxy; apply es_isig1; exact Hxy
      |intros z x y Hxy; apply es_isig2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TIChoice x y);
      [intros x y z Hxy; apply es_ichoice1; exact Hxy
      |intros z x y Hxy; apply es_ichoice2; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TInterp x y);
      [intros x y z Hxy; apply es_interp1; exact Hxy
      |intros z x y Hxy; apply es_interp2; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TMuI z);
      [intros x y Hxy; apply es_mui; exact Hxy | assumption].
  - eapply rtc_estep_congr (F := fun z => TMuS z);
      [intros x y Hxy; apply es_mus; exact Hxy | assumption].
  - eapply rtc_estep_congr (F := fun z => TIn z);
      [intros x y Hxy; apply es_in; exact Hxy | assumption].
  - eapply rtc_estep_congr5
      (F := fun x y z w v => TInd x y z w v);
    [intros x y a b c d Hxy; apply es_ind1; exact Hxy
    |intros a x y b c d Hxy; apply es_ind2; exact Hxy
    |intros a b x y c d Hxy; apply es_ind3; exact Hxy
    |intros a b c x y d Hxy; apply es_ind4; exact Hxy
    |intros a b c d x y Hxy; apply es_ind5; exact Hxy]; assumption.
  - eapply rtc_estep_congr4
      (F := fun x y z w => TIAll x y z w);
    [intros x y a b c Hxy; apply es_iall1; exact Hxy
    |intros a x y b c Hxy; apply es_iall2; exact Hxy
    |intros a b x y c Hxy; apply es_iall3; exact Hxy
    |intros a b c x y Hxy; apply es_iall4; exact Hxy]; assumption.
  - eapply rtc_estep_congr5
      (F := fun x y z w v => THyps x y z w v);
    [intros x y a b c d Hxy; apply es_hyps1; exact Hxy
    |intros a x y b c d Hxy; apply es_hyps2; exact Hxy
    |intros a b x y c d Hxy; apply es_hyps3; exact Hxy
    |intros a b c x y d Hxy; apply es_hyps4; exact Hxy
    |intros a b c d x y Hxy; apply es_hyps5; exact Hxy]; assumption.
  - eapply rtc_estep_congr (F := fun z => TList z);
      [intros x y Hxy; apply es_list; exact Hxy | assumption].
  - eapply rtc_estep_congr3
      (F := fun x y z => TLCons x y z);
    [intros x y a b Hxy; apply es_lcons1; exact Hxy
    |intros a x y b Hxy; apply es_lcons2; exact Hxy
    |intros a b x y Hxy; apply es_lcons3; exact Hxy]; assumption.
  - eapply rtc_estep_congr2 (F := fun x y => TCase x y bs);
      [intros x y z Hxy; apply es_case1; exact Hxy
      |intros z x y Hxy; apply es_case2; exact Hxy]; assumption.
  - eapply rtc_trans.
    + eapply rtc_estep_congr (F := fun z => TCase M Q (bs1 ++ (z,b) :: bs2));
      [intros x y Hxy; apply es_case_br1; exact Hxy | assumption].
    + eapply rtc_trans.
      * eapply rtc_estep_congr
          (F := fun z => TCase M Q (bs1 ++ (c',z) :: bs2));
        [intros x y Hxy; apply es_case_br2; exact Hxy | assumption].
      * apply (epbranches_rtc_estep bs2 bs2' H H5 M Q).
        reflexivity.
Qed.

Corollary epstep_rtc_estep_p : forall t u, epstep t u -> rtc estep t u.
Proof. intros t u H. exact (proj1 epstep_rtc_estep t u H). Qed.
