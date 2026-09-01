Require Import Progress.
Require Import TypeRules.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Lemma rtc_map_test : forall (F : term -> term) x y,
    (forall a b, fstep a b -> fstep (F a) (F b)) ->
    rtc fstep x y -> rtc fstep (F x) (F y).
Proof.
  intros F x y HF H; induction H as [x|x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact Hxy | exact IH].
Qed.

Lemma rtc_congr2 : forall (F : term -> term -> term) x x' y y',
    (forall a b, fstep a b -> fstep (F a y) (F b y)) ->
    (forall a b, fstep a b -> fstep (F x' a) (F x' b)) ->
    rtc fstep x x' -> rtc fstep y y' ->
    rtc fstep (F x y) (F x' y').
Proof.
  intros F x x' y y' H1 H2 Hx Hy.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun a => F a y) x x'); eauto.
  - eapply (rtc_map_test (fun b => F x' b) y y'); eauto.
Qed.

Lemma test_pi2 : forall A A' B B', rtc fstep A A' -> rtc fstep B B' ->
    rtc fstep (TPi A B) (TPi A' B').
Proof.
  intros; eapply (rtc_congr2 (fun x y => TPi x y));
    eauto using fs_pi1, fs_pi2.
Qed.

Lemma rtc_congr1 : forall (F : term -> term) x x',
    (forall a b, fstep a b -> fstep (F a) (F b)) ->
    rtc fstep x x' -> rtc fstep (F x) (F x').
Proof. intros; eapply rtc_map_test; eauto. Qed.

Lemma rtc_congr3 : forall (F : term -> term -> term -> term)
    x x' y y' z z',
    (forall a b, fstep a b -> fstep (F a y z) (F b y z)) ->
    (forall a b, fstep a b -> fstep (F x' a z) (F x' b z)) ->
    (forall a b, fstep a b -> fstep (F x' y' a) (F x' y' b)) ->
    rtc fstep x x' -> rtc fstep y y' -> rtc fstep z z' ->
    rtc fstep (F x y z) (F x' y' z').
Proof.
  intros F x x' y y' z z' H1 H2 H3 Hx Hy Hz.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun a => F a y z) x x'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun b => F x' b z) y y'); eauto.
    + eapply (rtc_map_test (fun c => F x' y' c) z z'); eauto.
Qed.

Lemma rtc_congr4 : forall (F : term -> term -> term -> term -> term)
    a a' b b' c c' d d',
    (forall x y, fstep x y -> fstep (F x b c d) (F y b c d)) ->
    (forall x y, fstep x y -> fstep (F a' x c d) (F a' y c d)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d) (F a' b' y d)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x) (F a' b' c' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' ->
    rtc fstep (F a b c d) (F a' b' c' d').
Proof.
  intros F a a' b b' c c' d d' H1 H2 H3 H4 Ha Hb Hc Hd.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d) c c'); eauto.
      * eapply (rtc_map_test (fun x => F a' b' c' x) d d'); eauto.
Qed.

Lemma rtc_congr5 : forall (F : term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e',
    (forall x y, fstep x y -> fstep (F x b c d e) (F y b c d e)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e) (F a' y c d e)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e) (F a' b' y d e)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e) (F a' b' c' y e)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x) (F a' b' c' d' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' -> rtc fstep e e' ->
    rtc fstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F a a' b b' c c' d d' e e' H1 H2 H3 H4 H5 Ha Hb Hc Hd He.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e) d d'); eauto. }
        { eapply (rtc_map_test (fun x => F a' b' c' d' x) e e'); eauto. }
Qed.

Lemma test_branch : forall bs bs', pbranches bs bs' ->
    (forall c c', pstep c c' -> rtc fstep c c') -> forall M Q pre,
    rtc fstep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs')).
Proof.
  intros bs bs' Hpb.
  intros HP.
  induction Hpb as [|c c' b b' bs bs' Hc Hb Htail IH];
    intros M Q pre.
  - cbn. apply rtc_refl.
  - cbn [app_assoc].
    pose proof (rtc_congr1
      (fun x => TCase M Q (pre ++ (x,b)::bs)) _ _
      (fun x y H => fs_case_br1 M Q pre x y b bs H) (HP c c' Hc)) as H1.
    pose proof (rtc_congr1
      (fun x => TCase M Q (pre ++ (c',x)::bs)) _ _
      (fun x y H => fs_case_br2 M Q pre c' x y bs H) (HP b b' Hb)) as H2.
    pose proof (IH M Q (pre ++ [(c',b')])) as H3.
    rewrite <- (app_assoc pre [(c',b')] bs) in H3.
    cbn in H3.
    rewrite <- (app_assoc pre [(c',b')] bs') in H3.
    cbn in H3.
    eapply rtc_trans; [exact H1 |].
    eapply rtc_trans; [exact H2 | exact H3].
Qed.

Lemma rtc_congr6 : forall (F : term -> term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e' f f',
    (forall x y, fstep x y -> fstep (F x b c d e f) (F y b c d e f)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e f) (F a' y c d e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e f) (F a' b' y d e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e f) (F a' b' c' y e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x f) (F a' b' c' d' y f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' x) (F a' b' c' d' e' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' -> rtc fstep e e' -> rtc fstep f f' ->
    rtc fstep (F a b c d e f) (F a' b' c' d' e' f').
Proof.
  intros F a a' b b' c c' d d' e e' f f' H1 H2 H3 H4 H5 H6 Ha Hb Hc Hd He Hf.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e f) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e f) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e f) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e f) d d'); eauto. }
        { eapply rtc_trans.
          - eapply (rtc_map_test (fun x => F a' b' c' d' x f) e e'); eauto.
          - eapply (rtc_map_test (fun x => F a' b' c' d' e' x) f f'); eauto. }
Qed.

Lemma rtc_case_body_nth : forall bs k c b b',
    nth_error bs k = Some (c,b) -> rtc fstep b b' ->
    exists bs', nth_error bs' k = Some (c,b') /\
      (forall j cj bj, j < k -> nth_error bs j = Some (cj,bj) ->
        nth_error bs' j = Some (cj,bj)) /\
      forall M Q pre, rtc fstep (TCase M Q (pre ++ bs))
        (TCase M Q (pre ++ bs')).
Proof.
  intros bs. induction bs as [|[c0 b0] bs IH];
    intros [|k] c b b' Hnth Hb.
  - discriminate.
  - discriminate.
  - cbn in Hnth. inversion Hnth; subst c b.
    exists ((c0,b')::bs). split; [reflexivity|]. split.
    + intros j cj bj Hj. lia.
    +
    intros M Q pre.
    eapply (rtc_congr1
      (fun x => TCase M Q (pre ++ (c0,x)::bs)) _ _
      (fun x y H => fs_case_br2 M Q pre c0 x y bs H) Hb).
  - cbn in Hnth.
    destruct (IH k c b b' Hnth Hb) as [bs' [Hidx [Hpres Hpath]]].
    exists ((c0,b0)::bs'). split; [exact Hidx|]. split.
    + intros j cj bj Hj Horig. destruct j as [|j].
      * cbn in Horig. inversion Horig; subst. cbn. reflexivity.
      * cbn in Horig. cbn. apply Hpres; [lia|exact Horig].
    + intros M Q pre.
    pose proof (Hpath M Q (pre ++ [(c0,b0)])) as H.
    rewrite <- (app_assoc pre [(c0,b0)] bs) in H.
    cbn in H.
    rewrite <- (app_assoc pre [(c0,b0)] bs') in H.
    cbn in H.
    exact H.
Qed.

Lemma test_switche : forall E P p x y,
 fstep x y -> fstep (TSwitch E P p (TESucc x)) (TSwitch E P p (TESucc y)).
Proof. intros; eapply fs_switch4; eapply fs_esucc; eauto. Qed.

Lemma branch_cons : forall c c' b b' bs bs',
    rtc fstep c c' -> rtc fstep b b' ->
    (forall M Q pre, rtc fstep (TCase M Q (pre ++ bs))
      (TCase M Q (pre ++ bs'))) ->
    forall M Q pre, rtc fstep
      (TCase M Q (pre ++ (c,b)::bs))
      (TCase M Q (pre ++ (c',b')::bs')).
Proof.
  intros c c' b b' bs bs' Hc Hb Htail M Q pre.
  pose proof (rtc_congr1
    (fun x => TCase M Q (pre ++ (x,b)::bs)) _ _
    (fun x y H => fs_case_br1 M Q pre x y b bs H) Hc) as H1.
  pose proof (rtc_congr1
    (fun x => TCase M Q (pre ++ (c',x)::bs)) _ _
    (fun x y H => fs_case_br2 M Q pre c' x y bs H) Hb) as H2.
  pose proof (Htail M Q (pre ++ [(c',b')])) as H3.
  rewrite <- (app_assoc pre [(c',b')] bs) in H3; cbn in H3.
  rewrite <- (app_assoc pre [(c',b')] bs') in H3; cbn in H3.
  eapply rtc_trans; [exact H1|].
  eapply rtc_trans; [exact H2|exact H3].
Qed.

Lemma case_red_bridge : forall a xs xs' Q bs k c b b' n,
    nth_error bs k = Some (c,b) -> enum_pos c n -> enum_pos a n ->
    (forall j cj bj, j < k -> nth_error bs j = Some (cj,bj) ->
      exists nj, enum_pos cj nj /\ nj <> n) ->
    rtc fstep xs xs' -> rtc fstep b b' ->
    rtc fstep (TCase (TIn (TPair a xs)) Q bs) (subst xs' 0 b').
Proof.
  intros a xs xs' Q bs k c b b' n Hidx Hcpos Hapre Hpre Hxs Hb.
  destruct (rtc_case_body_nth bs k c b b' Hidx Hb)
    as [bs' [Hidx' Hbody]].
  pose proof (rtc_congr1
    (fun x => TCase (TIn (TPair a x)) Q bs) _ _
    (fun x y H => fs_case1 _ _ _ _
      (fs_in _ _ (fs_pair2 _ _ _ H))) Hxs) as H1.
  pose proof (Hbody (TIn (TPair a xs')) Q []) as H2.
  cbn in H2.
  eapply rtc_trans; [exact H1|].
  eapply rtc_trans; [exact H2|].
  eapply rtc_step; [apply fs_step; eapply st_case; eauto|apply rtc_refl].
  all: match goal with |- ?g => idtac g end.
Qed.

Lemma rtc_congr7 : forall (F : term -> term -> term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e' f f' g g',
    (forall x y, fstep x y -> fstep (F x b c d e f g) (F y b c d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e f g) (F a' y c d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e f g) (F a' b' y d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e f g) (F a' b' c' y e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x f g) (F a' b' c' d' y f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' x g) (F a' b' c' d' e' y g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' f' x) (F a' b' c' d' e' f' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' ->
    rtc fstep e e' -> rtc fstep f f' -> rtc fstep g g' ->
    rtc fstep (F a b c d e f g) (F a' b' c' d' e' f' g').
Proof.
  intros F a a' b b' c c' d d' e e' f f' g g' H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc Hd He Hf Hg.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e f g) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e f g) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e f g) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e f g) d d'); eauto. }
        { eapply rtc_trans.
          - eapply (rtc_map_test (fun x => F a' b' c' d' x f g) e e'); eauto.
          - eapply rtc_trans.
            + eapply (rtc_map_test (fun x => F a' b' c' d' e' x g) f f'); eauto.
            + eapply (rtc_map_test (fun x => F a' b' c' d' e' f' x) g g'); eauto. }
Qed.

Lemma test_mut :
  (forall t u, pstep t u -> rtc fstep t u) /\
  (forall bs bs', pbranches bs bs' -> forall M Q pre,
    rtc fstep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply pstep_pbranches_ind; cbn; intros.
  all: try solve [apply rtc_refl].
  all: try solve [eapply (rtc_congr1 (fun x => TLam x)); eauto using fs_lam].
  all: try solve [eapply (rtc_congr1 (fun x => TFst x)); eauto using fs_fst].
  all: try solve [eapply (rtc_congr1 (fun x => TSnd x)); eauto using fs_snd].
  all: try solve [eapply (rtc_congr1 (fun x => TEnumT x)); eauto using fs_enumt].
  all: try solve [eapply (rtc_congr1 (fun x => TESucc x)); eauto using fs_esucc].
  all: try solve [eapply (rtc_congr1 (fun x => TIDesc x)); eauto using fs_idesc].
  all: try solve [eapply (rtc_congr1 (fun x => TIVar x)); eauto using fs_ivar].
  all: try solve [eapply (rtc_congr1 (fun x => TMuI x)); eauto using fs_mui].
  all: try solve [eapply (rtc_congr1 (fun x => TMuS x)); eauto using fs_mus].
  all: try solve [eapply (rtc_congr1 (fun x => TIn x)); eauto using fs_in].
  all: try solve [eapply (rtc_congr1 (fun x => TList x)); eauto using fs_list].
  all: try solve [eapply (rtc_congr1 (fun x => TLNil x)); eauto using fs_lnil].
  all: try solve [eapply (rtc_congr2 (fun x y => TPi x y)); eauto using fs_pi1, fs_pi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TApp x y)); eauto using fs_app1, fs_app2].
  all: try solve [eapply (rtc_congr2 (fun x y => TSigma x y)); eauto using fs_sigma1, fs_sigma2].
  all: try solve [eapply (rtc_congr2 (fun x y => TPair x y)); eauto using fs_pair1, fs_pair2].
  all: try solve [eapply (rtc_congr2 (fun x y => TConsE x y)); eauto using fs_conse1, fs_conse2].
  all: try solve [eapply (rtc_congr2 (fun x y => TEPi x y)); eauto using fs_epi1, fs_epi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIProd x y)); eauto using fs_iprod1, fs_iprod2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIPi x y)); eauto using fs_ipi1, fs_ipi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TISig x y)); eauto using fs_isig1, fs_isig2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIChoice x y)); eauto using fs_ichoice1, fs_ichoice2].
  all: try solve [eapply (rtc_congr2 (fun x y => TInterp x y)); eauto using fs_interp1, fs_interp2].
  all: try solve [eapply (rtc_congr3 (fun x y z => TLCons x y z)); eauto using fs_lcons1, fs_lcons2, fs_lcons3].
  all: try solve [eapply (rtc_congr4 (fun a b c d => TSwitch a b c d)); eauto using fs_switch1, fs_switch2, fs_switch3, fs_switch4].
  all: try solve [eapply (rtc_congr5 (fun a b c d e => TInd a b c d e)); eauto using fs_ind1, fs_ind2, fs_ind3, fs_ind4, fs_ind5].
  all: try solve [eapply (rtc_congr4 (fun a b c d => TIAll a b c d)); eauto using fs_iall1, fs_iall2, fs_iall3, fs_iall4].
  all: try solve [eapply (rtc_congr5 (fun a b c d e => THyps a b c d e)); eauto using fs_hyps1, fs_hyps2, fs_hyps3, fs_hyps4, fs_hyps5].
  all: try match goal with
    |- rtc fstep (TApp (TLam ?b) ?a) (subst ?a' 0 ?b') =>
      idtac "BETA";
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun b a => TApp (TLam b) a))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_case1, fs_case2].
  all: try solve [intros; eauto using fs_case1, fs_case2].
  all: try solve [eauto using fs_lam, fs_app1, fs_app2].
  all: try match goal with
    |- rtc fstep (TFst (TPair ?a ?b)) ?a' =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun a b => TFst (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TSnd (TPair ?a ?b)) ?b' =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun a b => TSnd (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TEPi TNilE ?P) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun P => TEPi TNilE P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TEPi (TConsE ?tg ?E) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun tg E P => TEPi (TConsE tg E) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TSwitch (TConsE ?tg ?E) ?P (TPair ?p0 ?ps) TEZero) ?p0' =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun tg E P p0 ps => TSwitch (TConsE tg E) P (TPair p0 ps) TEZero))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_pair1, fs_pair2, fs_fst, fs_snd,
    fs_conse1, fs_conse2, fs_epi1, fs_epi2,
    fs_switch1, fs_switch2, fs_switch3, fs_switch4].
  all: try match goal with
    |- rtc fstep (TSwitch (TConsE ?tg ?E) ?P (TPair ?p0 ?ps) (TESucc ?n)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun tg E P p0 ps n => TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_switch1, fs_switch2, fs_switch3, fs_switch4,
    fs_conse1, fs_conse2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (TIAll (TIVar ?j) ?X ?x ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr4 (fun j X x P => TIAll (TIVar j) X x P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll TI1 ?X TUnit ?P) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun X P => TIAll TI1 X TUnit P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIProd ?A ?B) ?X (TPair ?a ?b) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun A B X a b P => TIAll (TIProd A B) X (TPair a b) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIPi ?S ?T) ?X ?f ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun S T X f P => TIAll (TIPi S T) X f P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TISig ?S ?T) ?X (TPair ?s ?x) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun S T X s x P => TIAll (TISig S T) X (TPair s x) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIChoice ?E ?T) ?X (TPair ?e ?x) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun E T X e x P => TIAll (TIChoice E T) X (TPair e x) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_iall1, fs_iall2, fs_iall3, fs_iall4,
    fs_ivar, fs_iprod1, fs_iprod2, fs_ipi1, fs_ipi2, fs_isig1, fs_isig2,
    fs_ichoice1, fs_ichoice2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (THyps (TIVar ?j) ?X ?P ?h ?x) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun j X P h x => THyps (TIVar j) X P h x))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps TI1 ?X ?P ?h TUnit) TUnit =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun X P h => THyps TI1 X P h TUnit))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIProd ?A ?B) ?X ?P ?h (TPair ?a ?b)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun A B X P h a b => THyps (TIProd A B) X P h (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIPi ?S ?T) ?X ?P ?h ?f) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun S T X P h f => THyps (TIPi S T) X P h f))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TISig ?S ?T) ?X ?P ?h (TPair ?s ?x)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun S T X P h s x => THyps (TISig S T) X P h (TPair s x)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIChoice ?E ?T) ?X ?P ?h (TPair ?e ?x)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun E T X P h e x => THyps (TIChoice E T) X P h (TPair e x)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_hyps1, fs_hyps2, fs_hyps3, fs_hyps4, fs_hyps5,
    fs_ivar, fs_iprod1, fs_iprod2, fs_ipi1, fs_ipi2, fs_isig1, fs_isig2,
    fs_ichoice1, fs_ichoice2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (TInd ?R ?P ?s ?i (TIn ?xs)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun R P s i xs => TInd R P s i (TIn xs)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_ind1, fs_ind2, fs_ind3, fs_ind4, fs_ind5, fs_in].
  all: try solve [eapply branch_cons; eauto].
  all: try match goal with
    |- rtc fstep (TCase ?M ?Q ?bs) (TCase ?M' ?Q' ?bs') =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun M => TCase M Q bs))
      | eapply rtc_trans;
        [eapply (rtc_congr1 (fun Q => TCase M' Q bs))
        | cbn; eauto]]
    end.
  all: try solve [eauto using fs_case1, fs_case2].
  all: try solve [intros; eauto using fs_case1, fs_case2].
  all: try match goal with
    |- rtc fstep (TInterp (TIVar ?i) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun i X => TInterp (TIVar i) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp TI1 ?X) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun X => TInterp TI1 X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_interp1, fs_interp2, fs_ivar].
  all: try match goal with
    |- rtc fstep (TInterp (TIProd ?A ?B) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun A B X => TInterp (TIProd A B) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TIPi ?S ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun S T X => TInterp (TIPi S T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TISig ?S ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun S T X => TInterp (TISig S T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TIChoice ?E ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun E T X => TInterp (TIChoice E T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_interp1, fs_interp2, fs_ivar, fs_iprod1, fs_iprod2,
    fs_ipi1, fs_ipi2, fs_isig1, fs_isig2, fs_ichoice1, fs_ichoice2,
    fs_esucc].
  all: try solve [intros x y H; eapply fs_switch4; eapply fs_esucc; exact H].
  all: try eapply test_switche.
  all: try solve [eapply test_branch; eauto].
  all: try solve [eapply test_branch; [eauto | intros; eauto]].
  all: match goal with |- ?g => idtac g end.
Qed.

Lemma test_pi : forall A A' B B', rtc fstep A A' -> rtc fstep B B' ->
    rtc fstep (TPi A B) (TPi A' B').
Proof.
  intros A A' B B' HA HB.
  pose proof (rtc_map_test (fun x => TPi x B) A A'
    (fun x y H => fs_pi1 _ _ _ H) HA) as H1.
  pose proof (rtc_map_test (fun x => TPi A' x) B B'
    (fun x y H => fs_pi2 _ _ _ H) HB) as H2.
  eapply rtc_trans; eauto.
Qed.

Lemma test_beta : forall b b' a a', rtc fstep b b' -> rtc fstep a a' ->
 rtc fstep (TApp (TLam b) a) (subst a' 0 b').
Proof.
 intros. eapply rtc_trans.
 - eapply (rtc_congr2 (fun b a => TApp (TLam b) a)); eauto using fs_lam, fs_app1, fs_app2.
 - eapply rtc_step; [apply fs_step; constructor | apply rtc_refl].
Qed.

Lemma test_switche : forall E P p x y,
 fstep x y -> fstep (TSwitch E P p (TESucc x)) (TSwitch E P p (TESucc y)).
Proof. intros; eapply fs_switch4; eapply fs_esucc; eauto. Qed.
