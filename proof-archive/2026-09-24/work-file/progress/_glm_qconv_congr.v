(* GLM worker 2 — quotient-conversion bundle, part 2: contextual congruence  *)
(* for qconv.                                                                *)
(*                                                                           *)
(* qconv (= rtc qlink) is closed under every term context needed by conv's   *)
(* congruence rules.  Each context is shown to preserve qlink slot-wise:     *)
(* the cjoin half via the cjoin_congr/cjoin_C lemmas of _luna_cjoin_congr,   *)
(* the mueq half via the structural me_ constructors of _luna_mueq.  The     *)
(* TCase context is proved here: head/motive congruence and one-branch       *)
(* replacement (both missing from _luna_cjoin_congr, which has no case       *)
(* lemmas).                                                                  *)

Require Import Progress.
Require Import _tmp_epstep _work_epstep_rtc _work_cjoin
               _luna_mueq _luna_mueq_equiv _luna_cjoin_congr
               _glm_qconv_def.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* --- generic rtc-level context lemmas ------------------------------------- *)

Lemma qconv_congr1 : forall (F : term -> term),
    (forall x y, cjoin x y -> cjoin (F x) (F y)) ->
    (forall x y, mueq x y -> mueq (F x) (F y)) ->
    forall x y, qconv x y -> qconv (F x) (F y).
Proof.
  intros F Hcj Hmq x y H. eapply rtc_map_rel; [|exact H].
  intros a b [Hab | Hab].
  - left. apply Hcj, Hab.
  - right. apply Hmq, Hab.
Qed.

Lemma qconv_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', cjoin a a' -> cjoin b b' -> cjoin (F a b) (F a' b')) ->
    (forall a a' b b', mueq a a' -> mueq b b' -> mueq (F a b) (F a' b')) ->
    forall a a' b b', qconv a a' -> qconv b b' -> qconv (F a b) (F a' b').
Proof.
  intros F Hcj Hmq a a' b b' Ha Hb. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => F x b); [|exact Ha].
    intros x y [Hxy | Hxy].
    + left. apply Hcj; [exact Hxy | apply cjoin_refl].
    + right. apply Hmq; [exact Hxy | apply mueq_refl].
  - eapply rtc_map_rel with (F := fun x => F a' x); [|exact Hb].
    intros x y [Hxy | Hxy].
    + left. apply Hcj; [apply cjoin_refl | exact Hxy].
    + right. apply Hmq; [apply mueq_refl | exact Hxy].
Qed.

Lemma qconv_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      cjoin a a' -> cjoin b b' -> cjoin c c' ->
      cjoin (F a b c) (F a' b' c')) ->
    (forall a a' b b' c c',
      mueq a a' -> mueq b b' -> mueq c c' ->
      mueq (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      qconv a a' -> qconv b b' -> qconv c c' ->
      qconv (F a b c) (F a' b' c').
Proof.
  intros F Hcj Hmq a a' b b' c c' Ha Hb Hc. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => F x b c); [|exact Ha].
    intros x y [Hxy | Hxy].
    + left. apply Hcj; [exact Hxy | apply cjoin_refl | apply cjoin_refl].
    + right. apply Hmq; [exact Hxy | apply mueq_refl | apply mueq_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => F a' x c); [|exact Hb].
      intros x y [Hxy | Hxy].
      * left. apply Hcj; [apply cjoin_refl | exact Hxy | apply cjoin_refl].
      * right. apply Hmq; [apply mueq_refl | exact Hxy | apply mueq_refl].
    + eapply rtc_map_rel with (F := fun x => F a' b' x); [|exact Hc].
      intros x y [Hxy | Hxy].
      * left. apply Hcj; [apply cjoin_refl | apply cjoin_refl | exact Hxy].
      * right. apply Hmq; [apply mueq_refl | apply mueq_refl | exact Hxy].
Qed.

Lemma qconv_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      cjoin a a' -> cjoin b b' -> cjoin c c' -> cjoin d d' ->
      cjoin (F a b c d) (F a' b' c' d')) ->
    (forall a a' b b' c c' d d',
      mueq a a' -> mueq b b' -> mueq c c' -> mueq d d' ->
      mueq (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      qconv a a' -> qconv b b' -> qconv c c' -> qconv d d' ->
      qconv (F a b c d) (F a' b' c' d').
Proof.
  intros F Hcj Hmq a a' b b' c c' d d' Ha Hb Hc Hd. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => F x b c d); [|exact Ha].
    intros x y [Hxy | Hxy].
    + left. apply Hcj; [exact Hxy | apply cjoin_refl | apply cjoin_refl | apply cjoin_refl].
    + right. apply Hmq; [exact Hxy | apply mueq_refl | apply mueq_refl | apply mueq_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => F a' x c d); [|exact Hb].
      intros x y [Hxy | Hxy].
      * left. apply Hcj; eauto using cjoin_refl.
      * right. apply Hmq; eauto using mueq_refl.
    + eapply rtc_trans.
      * eapply rtc_map_rel with (F := fun x => F a' b' x d); [|exact Hc].
        intros x y [Hxy | Hxy].
        -- left. apply Hcj; eauto using cjoin_refl.
        -- right. apply Hmq; eauto using mueq_refl.
      * eapply rtc_map_rel with (F := fun x => F a' b' c' x); [|exact Hd].
        intros x y [Hxy | Hxy].
        -- left. apply Hcj; eauto using cjoin_refl.
        -- right. apply Hmq; eauto using mueq_refl.
Qed.

Lemma qconv_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      cjoin a a' -> cjoin b b' -> cjoin c c' -> cjoin d d' -> cjoin e e' ->
      cjoin (F a b c d e) (F a' b' c' d' e')) ->
    (forall a a' b b' c c' d d' e e',
      mueq a a' -> mueq b b' -> mueq c c' -> mueq d d' -> mueq e e' ->
      mueq (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      qconv a a' -> qconv b b' -> qconv c c' -> qconv d d' -> qconv e e' ->
      qconv (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F Hcj Hmq a a' b b' c c' d d' e e' Ha Hb Hc Hd He. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => F x b c d e); [|exact Ha].
    intros x y [Hxy | Hxy].
    + left. apply Hcj; [exact Hxy | apply cjoin_refl | apply cjoin_refl | apply cjoin_refl | apply cjoin_refl].
    + right. apply Hmq; [exact Hxy | apply mueq_refl | apply mueq_refl | apply mueq_refl | apply mueq_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => F a' x c d e); [|exact Hb].
      intros x y [Hxy | Hxy].
      * left. apply Hcj; eauto using cjoin_refl.
      * right. apply Hmq; eauto using mueq_refl.
    + eapply rtc_trans.
      * eapply rtc_map_rel with (F := fun x => F a' b' x d e); [|exact Hc].
        intros x y [Hxy | Hxy].
        -- left. apply Hcj; eauto using cjoin_refl.
        -- right. apply Hmq; eauto using mueq_refl.
      * eapply rtc_trans.
        -- eapply rtc_map_rel with (F := fun x => F a' b' c' x e); [|exact Hd].
           intros x y [Hxy | Hxy].
           ++ left. apply Hcj; eauto using cjoin_refl.
           ++ right. apply Hmq; eauto using mueq_refl.
        -- eapply rtc_map_rel with (F := fun x => F a' b' c' d' x); [|exact He].
           intros x y [Hxy | Hxy].
           ++ left. apply Hcj; eauto using cjoin_refl.
           ++ right. apply Hmq; eauto using mueq_refl.
Qed.

(* --- TCase: the contexts missing from _luna_cjoin_congr -------------------- *)

Lemma pbranches_app_cons : forall bs1 c c' b b' bs2,
    pstep c c' -> pstep b b' ->
    pbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b') :: bs2).
Proof.
  induction bs1 as [| [d e] bs1 IH]; intros c c' b b' bs2 Hc Hb; cbn.
  - constructor; [exact Hc | exact Hb | apply pbranches_refl].
  - constructor; [apply pstep_refl | apply pstep_refl | apply IH; assumption].
Qed.

Lemma epbranches_app_cons : forall bs1 c c' b b' bs2,
    epstep c c' -> epstep b b' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b') :: bs2).
Proof.
  induction bs1 as [| [d e] bs1 IH]; intros c c' b b' bs2 Hc Hb; cbn.
  - constructor; [exact Hc | exact Hb | apply epbranches_refl].
  - constructor; [apply epstep_refl | apply epstep_refl | apply IH; assumption].
Qed.

Lemma mubeq_app_cons : forall bs1 c c' b b' bs2,
    mueq c c' -> mueq b b' ->
    mubeq (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b') :: bs2).
Proof.
  induction bs1 as [| [d e] bs1 IH]; intros c c' b b' bs2 Hc Hb; cbn.
  - constructor; [exact Hc | exact Hb | apply mubeq_refl].
  - constructor; [apply mueq_refl | apply mueq_refl | apply IH; assumption].
Qed.

(* head/motive replacement, branches fixed *)
Lemma cjoin_case_mq : forall M M' Q Q' bs,
    cjoin M M' -> cjoin Q Q' ->
    cjoin (TCase M Q bs) (TCase M' Q' bs).
Proof.
  intros M M' Q Q' bs HM HQ.
  eapply (cjoin_congr2 (fun m q => TCase m q bs)).
  - intros x y z w Hx Hy. apply ps_case;
      [exact Hx | exact Hy | apply pbranches_refl].
  - intros x y z w Hx Hy. apply eps_case;
      [exact Hx | exact Hy | apply epbranches_refl].
  - exact HM.
  - exact HQ.
Qed.

(* one branch replacement, head/motive fixed *)
Lemma cjoin_case_br : forall M Q bs1 c c' b b' bs2,
    cjoin c c' -> cjoin b b' ->
    cjoin (TCase M Q (bs1 ++ (c,b) :: bs2))
          (TCase M Q (bs1 ++ (c',b') :: bs2)).
Proof.
  intros M Q bs1 c c' b b' bs2 Hc Hb.
  eapply (cjoin_congr2 (fun x y => TCase M Q (bs1 ++ (x,y) :: bs2))).
  - intros x x' y y' Hx Hy. apply ps_case;
      [apply pstep_refl | apply pstep_refl | apply pbranches_app_cons; assumption].
  - intros x x' y y' Hx Hy. apply eps_case;
      [apply epstep_refl | apply epstep_refl | apply epbranches_app_cons; assumption].
  - exact Hc.
  - exact Hb.
Qed.

(* --- the per-constructor qconv congruences -------------------------------- *)

Lemma qconv_pi : forall A A' B B', qconv A A' -> qconv B B' ->
    qconv (TPi A B) (TPi A' B').
Proof.
  intros A A' B B' HA HB. eapply (qconv_congr2 (fun a b => TPi a b)).
  - exact cjoin_pi.
  - exact me_pi.
  - exact HA.
  - exact HB.
Qed.

Lemma qconv_lam : forall b b', qconv b b' -> qconv (TLam b) (TLam b').
Proof.
  intros b b' H. eapply (qconv_congr1 (fun x => TLam x)).
  - exact cjoin_lam.
  - exact me_lam.
  - exact H.
Qed.

Lemma qconv_app : forall f f' a a', qconv f f' -> qconv a a' ->
    qconv (TApp f a) (TApp f' a').
Proof.
  intros f f' a a' HF HA. eapply (qconv_congr2 (fun x y => TApp x y)).
  - exact cjoin_app.
  - exact me_app.
  - exact HF.
  - exact HA.
Qed.

Lemma qconv_sigma : forall A A' B B', qconv A A' -> qconv B B' ->
    qconv (TSigma A B) (TSigma A' B').
Proof.
  intros A A' B B' HA HB. eapply (qconv_congr2 (fun a b => TSigma a b)).
  - exact cjoin_sigma.
  - exact me_sigma.
  - exact HA.
  - exact HB.
Qed.

Lemma qconv_pair : forall a a' b b', qconv a a' -> qconv b b' ->
    qconv (TPair a b) (TPair a' b').
Proof.
  intros a a' b b' HA HB. eapply (qconv_congr2 (fun x y => TPair x y)).
  - exact cjoin_pair.
  - exact me_pair.
  - exact HA.
  - exact HB.
Qed.

Lemma qconv_fst : forall p p', qconv p p' -> qconv (TFst p) (TFst p').
Proof.
  intros p p' H. eapply (qconv_congr1 (fun x => TFst x)).
  - exact cjoin_fst.
  - exact me_fst.
  - exact H.
Qed.

Lemma qconv_snd : forall p p', qconv p p' -> qconv (TSnd p) (TSnd p').
Proof.
  intros p p' H. eapply (qconv_congr1 (fun x => TSnd x)).
  - exact cjoin_snd.
  - exact me_snd.
  - exact H.
Qed.

Lemma qconv_conse : forall t t' E E', qconv t t' -> qconv E E' ->
    qconv (TConsE t E) (TConsE t' E').
Proof.
  intros t t' E E' HT HE. eapply (qconv_congr2 (fun x y => TConsE x y)).
  - exact cjoin_conse.
  - exact me_conse.
  - exact HT.
  - exact HE.
Qed.

Lemma qconv_enumt : forall E E', qconv E E' -> qconv (TEnumT E) (TEnumT E').
Proof.
  intros E E' H. eapply (qconv_congr1 (fun x => TEnumT x)).
  - exact cjoin_enumt.
  - exact me_enumt.
  - exact H.
Qed.

Lemma qconv_esucc : forall n n', qconv n n' -> qconv (TESucc n) (TESucc n').
Proof.
  intros n n' H. eapply (qconv_congr1 (fun x => TESucc x)).
  - exact cjoin_esucc.
  - exact me_esucc.
  - exact H.
Qed.

Lemma qconv_epi : forall E E' P P', qconv E E' -> qconv P P' ->
    qconv (TEPi E P) (TEPi E' P').
Proof.
  intros E E' P P' HE HP. eapply (qconv_congr2 (fun x y => TEPi x y)).
  - exact cjoin_epi.
  - exact me_epi.
  - exact HE.
  - exact HP.
Qed.

Lemma qconv_switch : forall E E' P P' p p' e e',
    qconv E E' -> qconv P P' -> qconv p p' -> qconv e e' ->
    qconv (TSwitch E P p e) (TSwitch E' P' p' e').
Proof.
  intros E E' P P' p p' e e' HE HP Hp He.
  eapply (qconv_congr4 (fun w x y z => TSwitch w x y z)).
  - exact cjoin_switch.
  - exact me_switch.
  - exact HE.
  - exact HP.
  - exact Hp.
  - exact He.
Qed.

Lemma qconv_idesc : forall I I', qconv I I' -> qconv (TIDesc I) (TIDesc I').
Proof.
  intros I I' H. eapply (qconv_congr1 (fun x => TIDesc x)).
  - exact cjoin_idesc.
  - exact me_idesc.
  - exact H.
Qed.

Lemma qconv_ivar : forall i i', qconv i i' -> qconv (TIVar i) (TIVar i').
Proof.
  intros i i' H. eapply (qconv_congr1 (fun x => TIVar x)).
  - exact cjoin_ivar.
  - exact me_ivar.
  - exact H.
Qed.

Lemma qconv_iprod : forall A A' B B', qconv A A' -> qconv B B' ->
    qconv (TIProd A B) (TIProd A' B').
Proof.
  intros A A' B B' HA HB. eapply (qconv_congr2 (fun a b => TIProd a b)).
  - exact cjoin_iprod.
  - exact me_iprod.
  - exact HA.
  - exact HB.
Qed.

Lemma qconv_ipi : forall S S' T T', qconv S S' -> qconv T T' ->
    qconv (TIPi S T) (TIPi S' T').
Proof.
  intros S S' T T' HS HT. eapply (qconv_congr2 (fun a b => TIPi a b)).
  - exact cjoin_ipi.
  - exact me_ipi.
  - exact HS.
  - exact HT.
Qed.

Lemma qconv_isig : forall S S' T T', qconv S S' -> qconv T T' ->
    qconv (TISig S T) (TISig S' T').
Proof.
  intros S S' T T' HS HT. eapply (qconv_congr2 (fun a b => TISig a b)).
  - exact cjoin_isig.
  - exact me_isig.
  - exact HS.
  - exact HT.
Qed.

Lemma qconv_ichoice : forall E E' T T', qconv E E' -> qconv T T' ->
    qconv (TIChoice E T) (TIChoice E' T').
Proof.
  intros E E' T T' HE HT. eapply (qconv_congr2 (fun a b => TIChoice a b)).
  - exact cjoin_ichoice.
  - exact me_ichoice.
  - exact HE.
  - exact HT.
Qed.

Lemma qconv_interp : forall D D' X X', qconv D D' -> qconv X X' ->
    qconv (TInterp D X) (TInterp D' X').
Proof.
  intros D D' X X' HD HX. eapply (qconv_congr2 (fun a b => TInterp a b)).
  - exact cjoin_interp.
  - exact me_interp.
  - exact HD.
  - exact HX.
Qed.

Lemma qconv_mui : forall R R', qconv R R' -> qconv (TMuI R) (TMuI R').
Proof.
  intros R R' H. eapply (qconv_congr1 (fun x => TMuI x)).
  - exact cjoin_mui.
  - exact me_mui.
  - exact H.
Qed.

Lemma qconv_mus : forall S S', qconv S S' -> qconv (TMuS S) (TMuS S').
Proof.
  intros S S' H. eapply (qconv_congr1 (fun x => TMuS x)).
  - exact cjoin_mus.
  - exact me_mus.
  - exact H.
Qed.

Lemma qconv_in : forall x x', qconv x x' -> qconv (TIn x) (TIn x').
Proof.
  intros x x' H. eapply (qconv_congr1 (fun y => TIn y)).
  - exact cjoin_in.
  - exact me_in.
  - exact H.
Qed.

Lemma qconv_ind : forall R R' P P' s s' i i' x x',
    qconv R R' -> qconv P P' -> qconv s s' -> qconv i i' -> qconv x x' ->
    qconv (TInd R P s i x) (TInd R' P' s' i' x').
Proof.
  intros R R' P P' s s' i i' x x' HR HP Hs Hi Hx.
  eapply (qconv_congr5 (fun a b c d e => TInd a b c d e)).
  - exact cjoin_ind.
  - exact me_ind.
  - exact HR.
  - exact HP.
  - exact Hs.
  - exact Hi.
  - exact Hx.
Qed.

Lemma qconv_iall : forall D D' X X' xs xs' P P',
    qconv D D' -> qconv X X' -> qconv xs xs' -> qconv P P' ->
    qconv (TIAll D X xs P) (TIAll D' X' xs' P').
Proof.
  intros D D' X X' xs xs' P P' HD HX Hxs HP.
  eapply (qconv_congr4 (fun a b c d => TIAll a b c d)).
  - exact cjoin_iall.
  - exact me_iall.
  - exact HD.
  - exact HX.
  - exact Hxs.
  - exact HP.
Qed.

Lemma qconv_hyps : forall D D' X X' P P' h h' xs xs',
    qconv D D' -> qconv X X' -> qconv P P' -> qconv h h' -> qconv xs xs' ->
    qconv (THyps D X P h xs) (THyps D' X' P' h' xs').
Proof.
  intros D D' X X' P P' h h' xs xs' HD HX HP Hh Hxs.
  eapply (qconv_congr5 (fun a b c d e => THyps a b c d e)).
  - exact cjoin_hyps.
  - exact me_hyps.
  - exact HD.
  - exact HX.
  - exact HP.
  - exact Hh.
  - exact Hxs.
Qed.

Lemma qconv_list : forall A A', qconv A A' -> qconv (TList A) (TList A').
Proof.
  intros A A' H. eapply (qconv_congr1 (fun x => TList x)).
  - exact cjoin_list.
  - exact me_list.
  - exact H.
Qed.

Lemma qconv_lnil : forall A A', qconv A A' -> qconv (TLNil A) (TLNil A').
Proof.
  intros A A' H. eapply (qconv_congr1 (fun x => TLNil x)).
  - exact cjoin_lnil.
  - exact me_lnil.
  - exact H.
Qed.

Lemma qconv_lcons : forall A A' a a' l l',
    qconv A A' -> qconv a a' -> qconv l l' ->
    qconv (TLCons A a l) (TLCons A' a' l').
Proof.
  intros A A' a a' l l' HA Ha Hl.
  eapply (qconv_congr3 (fun x y z => TLCons x y z)).
  - exact cjoin_lcons.
  - exact me_lcons.
  - exact HA.
  - exact Ha.
  - exact Hl.
Qed.

(* TCase head/motive, branches fixed *)
Lemma qconv_case_mq : forall M M' Q Q' bs,
    qconv M M' -> qconv Q Q' ->
    qconv (TCase M Q bs) (TCase M' Q' bs).
Proof.
  intros M M' Q Q' bs HM HQ. eapply (qconv_congr2 (fun m q => TCase m q bs)).
  - intros x x' y y' Hx Hy. apply cjoin_case_mq; assumption.
  - intros x x' y y' Hx Hy. apply me_case;
      [exact Hx | exact Hy | apply mubeq_refl].
  - exact HM.
  - exact HQ.
Qed.

(* TCase one branch replacement, head/motive fixed *)
Lemma qconv_case_br : forall M Q bs1 c c' b b' bs2,
    qconv c c' -> qconv b b' ->
    qconv (TCase M Q (bs1 ++ (c,b) :: bs2))
          (TCase M Q (bs1 ++ (c',b') :: bs2)).
Proof.
  intros M Q bs1 c c' b b' bs2 Hc Hb.
  eapply (qconv_congr2 (fun x y => TCase M Q (bs1 ++ (x,y) :: bs2))).
  - intros x x' y y' Hx Hy. apply cjoin_case_br; assumption.
  - intros x x' y y' Hx Hy. apply me_case;
      [apply mueq_refl | apply mueq_refl | apply mubeq_app_cons; assumption].
  - exact Hc.
  - exact Hb.
Qed.
