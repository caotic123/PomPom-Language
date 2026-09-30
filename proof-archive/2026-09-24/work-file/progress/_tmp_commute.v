Require Import Progress _tmp_epstep _tmp_eta_shape _tmp_epstep_inv
  _tmp_eta_tool _tmp_epstep_subst _work_pstep_lift_inv
  _work_eta_critical _work_epstep_rtc.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma lift_zero_id_local : forall t k, lift 0 k t = t.
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

Lemma subst_eta_app_local : forall f a,
    subst a 0 (TApp (lift 1 0 f) (TVar 0)) = TApp f a.
Proof.
  intros f a. cbn [subst].
  rewrite subst_lift_zero, lift_zero_id_local. reflexivity.
Qed.

Lemma epstep_enum_pos_id : forall c c' n,
    epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hep Hpos. revert c' Hep.
  induction Hpos; intros c' Hep; inversion Hep; subst; [reflexivity |].
  f_equal. eauto.
Qed.

Lemma epbranches_nth_error_fwd : forall bs bs' k c b,
    epbranches bs bs' -> nth_error bs k = Some (c,b) ->
    exists c' b', nth_error bs' k = Some (c',b') /\
      epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c b Hbs. revert k c b.
  induction Hbs; intros k c0 b0 Hnth; destruct k; cbn in Hnth.
  - discriminate.
  - discriminate.
  - inversion Hnth; subst. eexists; eexists; repeat split; eauto.
  - eapply IHHbs; exact Hnth.
Qed.

Lemma epbranches_nth_error_rev : forall bs bs' k c' b',
    epbranches bs bs' -> nth_error bs' k = Some (c',b') ->
    exists c b, nth_error bs k = Some (c,b) /\
      epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c' b' Hbs. revert k c' b'.
  induction Hbs; intros k c0 b0 Hnth; destruct k; cbn in Hnth.
  - discriminate.
  - discriminate.
  - inversion Hnth; subst. eexists; eexists; repeat split; eauto.
  - eapply IHHbs; exact Hnth.
Qed.

Ltac invert_eta_other :=
  match goal with
  | Hother : epstep ?s ?u
      |- exists v, rtc epstep ?t v /\ pstep ?u v =>
      inversion Hother; subst; clear Hother
  | Hother : epbranches ?ss ?us
      |- exists vs, rtc epbranches ?ts vs /\ pbranches ?us vs =>
      inversion Hother; subst; clear Hother
  end.

Ltac take_commute :=
  match goal with
  | IH : forall z, epstep ?s z ->
        exists w, rtc epstep ?t w /\ pstep z w,
    H : epstep ?s ?z |- _ =>
      let w := fresh "w" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH z H) as [w [He Hp]];
      clear IH
  | IH : forall zs, epbranches ?ss zs ->
        exists ws, rtc epbranches ?ts ws /\ pbranches zs ws,
    H : epbranches ?ss ?zs |- _ =>
      let ws := fresh "ws" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH zs H) as [ws [He Hp]];
      clear IH
  end.

Ltac invert_eta_known_shape :=
  match goal with
  | Hs : epstep (TLam _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TPair _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TNilE _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TEZero _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TESucc _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TUnit _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TConsE _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIVar _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TI1 _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIProd _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIPi _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TISig _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIChoice _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIn _) _ |- _ => inversion Hs; subst; clear Hs
  end.

Ltac eta_congruence :=
  first
    [ assumption
    | apply epstep_lift; eta_congruence
    | apply epstep_subst; eta_congruence
    | apply eps_var
    | apply eps_sort
    | apply eps_pi; eta_congruence
    | apply eps_lam; eta_congruence
    | apply eps_app; eta_congruence
    | apply eps_sigma; eta_congruence
    | apply eps_pair; eta_congruence
    | apply eps_fst; eta_congruence
    | apply eps_snd; eta_congruence
    | apply eps_unitt
    | apply eps_unit
    | apply eps_uid
    | apply eps_tag
    | apply eps_enumu
    | apply eps_nile
    | apply eps_conse; eta_congruence
    | apply eps_enumt; eta_congruence
    | apply eps_ezero
    | apply eps_esucc; eta_congruence
    | apply eps_epi; eta_congruence
    | apply eps_switch; eta_congruence
    | apply eps_idesc; eta_congruence
    | apply eps_ivar; eta_congruence
    | apply eps_i1
    | apply eps_iprod; eta_congruence
    | apply eps_ipi; eta_congruence
    | apply eps_isig; eta_congruence
    | apply eps_ichoice; eta_congruence
    | apply eps_interp; eta_congruence
    | apply eps_mui; eta_congruence
    | apply eps_mus; eta_congruence
    | apply eps_in; eta_congruence
    | apply eps_ind; eta_congruence
    | apply eps_iall; eta_congruence
    | apply eps_hyps; eta_congruence
    | apply eps_list; eta_congruence
    | apply eps_lnil; eta_congruence
    | apply eps_lcons; eta_congruence
    | apply eps_case; eta_congruence
    | apply epbs_nil
    | apply epbs_cons; eta_congruence ].

Ltac eta_rtc_congruence :=
  first
    [ assumption
    | apply rtc_refl
    | apply rtc_epstep_lift; eta_rtc_congruence
    | apply rtc_epstep_subst; eta_rtc_congruence
    | eapply rtc_epstep_congr1 with (F := fun x => TLam x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TFst x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TSnd x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TEnumT x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TESucc x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIDesc x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIVar x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TMuI x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TMuS x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIn x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TList x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TLNil x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TApp x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TSigma x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TPair x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TConsE x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TEPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIProd x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TISig x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIChoice x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TInterp x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr3 with (F := fun x y z => TLCons x y z);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr4 with (F := fun x y z w => TSwitch x y z w);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr4 with (F := fun x y z w => TIAll x y z w);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr5 with (F := fun x y z w q => TInd x y z w q);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr5 with (F := fun x y z w q => THyps x y z w q);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | apply rtc_epstep_case; eta_rtc_congruence
    | apply rtc_epbranches_cons; eta_rtc_congruence ].

Ltac apply_computation_root :=
  first
    [ eapply ps_fst_pair; eassumption
    | eapply ps_snd_pair; eassumption
    | eapply ps_epi_cons; eassumption
    | eapply ps_switch_zero; eassumption
    | eapply ps_switch_succ; eassumption
    | eapply ps_interp_prod; eassumption
    | eapply ps_interp_pi; eassumption
    | eapply ps_interp_sig; eassumption
    | eapply ps_interp_choice; eassumption
    | eapply ps_iall_var; eassumption
    | eapply ps_iall_prod; eassumption
    | eapply ps_iall_pi; eassumption
    | eapply ps_iall_sig; eassumption
    | eapply ps_iall_choice; eassumption
    | eapply ps_hyps_var; eassumption
    | eapply ps_hyps_prod; eassumption
    | eapply ps_hyps_pi; eassumption
    | eapply ps_hyps_sig; eassumption
    | eapply ps_hyps_choice; eassumption
    | eapply ps_ind_red; eassumption ].

Ltac solve_computation_root :=
  let v := fresh "common" in
  evar (v : term);
  exists v; split;
  cycle 2;
  [ apply_computation_root
  | subst v;
    eauto 30 using epstep_lift, epstep_subst, epstep_refl ].

Lemma pstep_epstep_commute_mut :
  (forall s t (H : pstep s t), forall u, epstep s u ->
      exists v, rtc epstep t v /\ pstep u v) /\
  (forall ss ts (H : pbranches ss ts), forall us, epbranches ss us ->
      exists vs, rtc epbranches ts vs /\ pbranches us vs).
Proof.
  apply pstep_pbranches_ind.
  all: intros.
  all: invert_eta_other.
  all: repeat invert_eta_known_shape.
  all: repeat take_commute.
  all: try solve [eexists; split; cycle 1;
    [econstructor; eauto using pstep_lift, pstep_subst, pstep_refl |
     eta_rtc_congruence]].
  all: try solve [eexists; split; cycle 1;
    [apply_core_root | eta_rtc_congruence]].
  all: try solve [eexists; split;
    [econstructor; eauto using epstep_lift, epstep_subst, epstep_refl |
     econstructor; eauto using pstep_lift, pstep_subst, pstep_refl]].
  all: try solve [
    match goal with
    | He : epstep ?x ?w |- exists v, epstep ?x v /\ pstep (TFst _) v =>
        exists w; split; [exact He | eapply ps_fst_pair; eassumption]
    | He : epstep ?x ?w |- exists v, epstep ?x v /\ pstep (TSnd _) v =>
        exists w; split; [exact He | eapply ps_snd_pair; eassumption]
    | He : epstep ?x ?w
        |- exists v, epstep ?x v /\ pstep (TSwitch _ _ _ TEZero) v =>
        exists w; split; [exact He | eapply ps_switch_zero; eassumption]
    end].
  all: try solve [
    match goal with
    | HP : epstep ?P ?Pw, HE : epstep ?E ?Ew
      |- exists v,
        epstep
          (TSigma (TApp ?P TEZero)
            (lift 1 0
              (TEPi ?E
                (TLam (TApp (lift 1 0 ?P) (TESucc (TVar 0))))))) v /\ _ =>
        exists
          (TSigma (TApp Pw TEZero)
            (lift 1 0
              (TEPi Ew
                (TLam (TApp (lift 1 0 Pw) (TESucc (TVar 0)))))));
        split;
        [ eta_congruence
        | eapply ps_epi_cons; eassumption ]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw, HX : epstep ?X ?Xw
      |- exists v,
        epstep (TSigma (TInterp ?A ?X) (lift 1 0 (TInterp ?B ?X))) v /\ _ =>
        exists (TSigma (TInterp Aw Xw) (lift 1 0 (TInterp Bw Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_prod; eassumption ]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TPi ?S
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TPi Sw
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_pi; eassumption ]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TSigma ?S
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TSigma Sw
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_sig; eassumption ]
    | HE : epstep ?E ?Ew, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TSigma (TEnumT ?E)
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TSigma (TEnumT Ew)
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_choice; eassumption ]
    end].
  all: try solve [
    match goal with
    | HE : epstep ?E ?Ew, HP : epstep ?P ?Pw,
      Hps : epstep ?ps ?psw, Hn : epstep ?n ?nw
      |- exists v,
        epstep
          (TSwitch ?E
            (TLam (TApp (lift 1 0 ?P) (TESucc (TVar 0)))) ?ps ?n) v /\ _ =>
        exists
          (TSwitch Ew
            (TLam (TApp (lift 1 0 Pw) (TESucc (TVar 0)))) psw nw);
        split; [eta_congruence | eapply ps_switch_succ; eassumption]
    | HP : epstep ?P ?Pw, Hj : epstep ?j ?jw, Hx : epstep ?x ?xw
      |- exists v, epstep (TApp ?P (TPair ?j ?x)) v /\ _ =>
        exists (TApp Pw (TPair jw xw));
        split; [eta_congruence | eapply ps_iall_var; eassumption]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw,
      HX : epstep ?X ?Xw, Ha : epstep ?a ?aw,
      Hb : epstep ?b ?bw, HP : epstep ?P ?Pw
      |- exists v,
        epstep
          (TSigma (TIAll ?A ?X ?a ?P) (lift 1 0 (TIAll ?B ?X ?b ?P)))
          v /\ _ =>
        exists
          (TSigma (TIAll Aw Xw aw Pw)
            (lift 1 0 (TIAll Bw Xw bw Pw)));
        split; [eta_congruence | eapply ps_iall_prod; eassumption]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw,
      HX : epstep ?X ?Xw, Hf : epstep ?f ?fw,
      HP : epstep ?P ?Pw
      |- exists v,
        epstep
          (TPi ?S
            (TIAll (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X)
              (TApp (lift 1 0 ?f) (TVar 0)) (lift 1 0 ?P))) v /\ _ =>
        exists
          (TPi Sw
            (TIAll (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)
              (TApp (lift 1 0 fw) (TVar 0)) (lift 1 0 Pw)));
        split; [eta_congruence | eapply ps_iall_pi; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      Hx : epstep ?x ?xw, HP : epstep ?P ?Pw
      |- exists v, epstep (TIAll (TApp ?T ?s) ?X ?x ?P) v /\
          pstep (TIAll (TISig _ _) _ _ _) v =>
        match goal with Hs : epstep s ?sw |- _ =>
          exists (TIAll (TApp Tw sw) Xw xw Pw);
          split; [eta_congruence | eapply ps_iall_sig; eassumption]
        end
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      Hx : epstep ?x ?xw, HP : epstep ?P ?Pw
      |- exists v, epstep (TIAll (TApp ?T ?e) ?X ?x ?P) v /\
          pstep (TIAll (TIChoice _ _) _ _ _) v =>
        match goal with He : epstep e ?ew |- _ =>
          exists (TIAll (TApp Tw ew) Xw xw Pw);
          split; [eta_congruence | eapply ps_iall_choice; eassumption]
        end
    end].
  all: try solve [
    match goal with
    | Hh : epstep ?h ?hw, Hj : epstep ?j ?jw, Hx : epstep ?x ?xw
      |- exists v, epstep (TApp (TApp ?h ?j) ?x) v /\ _ =>
        exists (TApp (TApp hw jw) xw);
        split; [eta_congruence | eapply ps_hyps_var; eassumption]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw,
      HX : epstep ?X ?Xw, HP : epstep ?P ?Pw,
      Hh : epstep ?h ?hw, Ha : epstep ?a ?aw, Hb : epstep ?b ?bw
      |- exists v,
        epstep
          (TPair (THyps ?A ?X ?P ?h ?a) (THyps ?B ?X ?P ?h ?b)) v /\ _ =>
        exists
          (TPair (THyps Aw Xw Pw hw aw) (THyps Bw Xw Pw hw bw));
        split; [eta_congruence | eapply ps_hyps_prod; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hf : epstep ?f ?fw
      |- exists v,
        epstep
          (TLam
            (THyps (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X)
              (lift 1 0 ?P) (lift 1 0 ?h)
              (TApp (lift 1 0 ?f) (TVar 0)))) v /\ _ =>
        exists
          (TLam
            (THyps (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)
              (lift 1 0 Pw) (lift 1 0 hw)
              (TApp (lift 1 0 fw) (TVar 0))));
        split; [eta_congruence | eapply ps_hyps_pi; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hx : epstep ?x ?xw
      |- exists v, epstep (THyps (TApp ?T ?s) ?X ?P ?h ?x) v /\
          pstep (THyps (TISig _ _) _ _ _ _) v =>
        match goal with Hs : epstep s ?sw |- _ =>
          exists (THyps (TApp Tw sw) Xw Pw hw xw);
          split; [eta_congruence | eapply ps_hyps_sig; eassumption]
        end
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hx : epstep ?x ?xw
      |- exists v, epstep (THyps (TApp ?T ?e) ?X ?P ?h ?x) v /\
          pstep (THyps (TIChoice _ _) _ _ _ _) v =>
        match goal with He : epstep e ?ew |- _ =>
          exists (THyps (TApp Tw ew) Xw Pw hw xw);
          split; [eta_congruence | eapply ps_hyps_choice; eassumption]
        end
    end].
  all: try solve [
    match goal with
    | HR : epstep ?R ?Rw, HP : epstep ?P ?Pw,
      Hs : epstep ?s ?sw, Hi : epstep ?i ?iw, Hxs : epstep ?xs ?xsw
      |- exists v,
        epstep
          (TApp (TApp (TApp ?s ?i) ?xs)
            (THyps (TApp ?R ?i) (TMuI ?R) ?P
              (TLam (TLam
                (TInd (lift 2 0 ?R) (lift 2 0 ?P) (lift 2 0 ?s)
                  (TVar 1) (TVar 0)))) ?xs)) v /\ _ =>
        exists
          (TApp (TApp (TApp sw iw) xsw)
            (THyps (TApp Rw iw) (TMuI Rw) Pw
              (TLam (TLam
                (TInd (lift 2 0 Rw) (lift 2 0 Pw) (lift 2 0 sw)
                  (TVar 1) (TVar 0)))) xsw));
        split; [eta_congruence | eapply ps_ind_red; eassumption]
    end].
  all: try solve [solve_computation_root].
  all: try solve [
    match goal with
    | Hb : epstep ?b ?bw, Ha : epstep ?a ?aw
      |- exists v, epstep (subst ?a 0 ?b) v /\ pstep (TApp (TLam _) _) v =>
        exists (subst aw 0 bw); split;
        [ eapply epstep_subst; eassumption
        | eapply ps_beta; eassumption ]
    end].
  all: try solve [
    match goal with
    | IH : forall z,
        epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      Hfu : epstep ?f ?fu,
      Hea : rtc epstep ?a ?aw,
      Hca : pstep ?a0 ?aw
      |- exists v, rtc epstep (subst ?a 0 ?b) v /\ pstep (TApp ?fu ?a0) v =>
        assert (Hbody : epstep
          (TApp (lift 1 0 f) (TVar 0))
          (TApp (lift 1 0 fu) (TVar 0))) by eta_congruence;
        destruct (IH _ Hbody) as [q [Hbq Hfq]];
        exists (subst aw 0 q); split;
        [ eapply rtc_epstep_subst; eassumption
        | pose proof (pstep_subst _ _ Hfq a0 aw 0 Hca) as Hsub;
          rewrite subst_eta_app_local in Hsub; exact Hsub ]
    end].
  all: try solve [eapply eta_lambda_critical_rtc; eassumption].
  destruct (epbranches_nth_error_fwd bs bs' k c b H8 e)
    as [c1 [b1 [Hnth [Hc1 Hb1]]]].
  assert (Hc_eq : c1 = c) by (eapply epstep_enum_pos_id; eassumption).
  subst c1.
  assert (Ha_eq : a' = a) by (eapply epstep_enum_pos_id; eassumption).
  subst a'.
  destruct (H0 b1 Hb1) as [q [Hbq Hbcore]].
  exists (subst w 0 q). split.
  - eapply rtc_epstep_subst; eassumption.
  - eapply ps_case_red with (k := k) (c := c) (b := b1) (n := n).
    + exact Hnth.
    + exact e0.
    + exact e1.
    + intros j cj' bj' Hj Hnth'.
      destruct (epbranches_nth_error_rev bs bs' j cj' bj' H8 Hnth')
        as [cj [bj [Horig [Hcj Hbj]]]].
      destruct (e2 j cj bj Hj Horig) as [nj [Hpos Hneq]].
      assert (Hcj_eq : cj' = cj) by
        (eapply epstep_enum_pos_id; eassumption).
      subst cj'. exists nj. split; assumption.
    + exact Hcore.
    + exact Hbcore.
Qed.

Corollary pstep_epstep_commute : forall s t u,
    pstep s t -> epstep s u ->
    exists v, rtc epstep t v /\ pstep u v.
Proof.
  intros s t u Hp He.
  exact (proj1 pstep_epstep_commute_mut s t Hp u He).
Qed.

Corollary pbranches_epbranches_commute : forall ss ts us,
    pbranches ss ts -> epbranches ss us ->
    exists vs, rtc epbranches ts vs /\ pbranches us vs.
Proof.
  intros ss ts us Hp He.
  exact (proj2 pstep_epstep_commute_mut ss ts Hp us He).
Qed.
